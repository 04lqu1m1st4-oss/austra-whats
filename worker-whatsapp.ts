// worker-whatsapp.ts — dispatch worker WhatsApp via Baileys
//
// Arquitetura espelhada do worker.ts (Telegram), com adaptações pro protocolo WA.
//
// DIFERENÇAS CHAVE vs Telegram:
//   1. Sessão: Baileys usa creds.json (JSONB no Supabase) em vez de StringSession
//   2. Dedup: WA não tem randomId nativo — usamos cycle_message_id (UUID por ciclo)
//             salvo em wa_dispatch_logs ANTES de enviar. Retry verifica no banco.
//   3. Timing: SNIPER_BEFORE_MS = 120ms (RTT WA ~60-80ms one-way vs ~25ms do Telegram)
//              Calibrar com logs [sniper][timing] após primeiros disparos.
//   4. Conexão: Baileys emite eventos de estado — sem polling keepalive.
//               connection.update detecta queda em tempo real.
//   5. JID: grupos WA usam formato "120363XXXXXXXXXX@g.us"
//   6. Sem grupos "abertos" por enquanto — MVP foca em grupos fechados (horário fixo)
//
// v1 (initial):
//   Sniper loop para grupos fechados com timing calibrável
//   Dedup via cycle_message_id no banco (anti-duplicata em retry)
//   Prewarm no boot: conecta todas as contas e popula accountCache
//   Reconnect automático via eventos Baileys (sem polling)
//   Pre-fetch do schedule 800ms antes do disparo
//   Backoff exponencial no retry (3s → 6s → 12s → max 15s)
//   HTTP server na porta 3002 (não conflita com Telegram na 3001)
//
// v2 (fixes):
//   QR convertido para PNG base64 antes de salvar no banco (fix: frontend não renderizava)
//   getSocket não bloqueia em socketReady para contas sem creds (fix: timeout 30s em novas contas)
//   /reload inicia QR para contas novas sem creds (fix: retornava skipped sem iniciar sessão)
//   initAuthCreds importado e usado corretamente na inicialização de sessão

import { createClient }                      from "@supabase/supabase-js";
import makeWASocket, {
  DisconnectReason,
  fetchLatestBaileysVersion,
  makeCacheableSignalKeyStore,
  initAuthCreds,
  WASocket,
  AuthenticationState,
}                                             from "@whiskeysockets/baileys";
import { Boom }                               from "@hapi/boom";
import P                                      from "pino";
import http                                   from "http";
import { randomUUID }                         from "crypto";
import QRCode                                 from "qrcode";

/* ─────────────────────────────────────────────────────────────────────────────
   SUPABASE
   ───────────────────────────────────────────────────────────────────────────── */
const supabase = createClient(
  process.env.SUPABASE_URL!,
  process.env.SUPABASE_SERVICE_ROLE_KEY!
);

/* ─────────────────────────────────────────────────────────────────────────────
   CONSTANTES
   ───────────────────────────────────────────────────────────────────────────── */
const WORKER_PORT              = parseInt(process.env.PORT ?? "3002", 10);
const WORKER_SECRET            = process.env.WORKER_SECRET ?? "";

const SNIPER_BEFORE_MS              = 320;
const SNIPER_SEND_TIMEOUT_MS        = 1_500;
const SNIPER_ATTEMPT_INTERVAL_MS    = 2;
const SNIPER_PAUSE_EVERY_N          = 10;
const SNIPER_PAUSE_MS               = 5;
const SNIPER_INTER_ACCOUNT_DELAY_MS = 5;
const SNIPER_BUDGET_MS              = 50_000;
const SNIPER_DONE_BLOCK_TTL_MS      = 500;

const PREFETCH_BEFORE_MS        = 800;
const RELOAD_INTERVAL_MS        = 30_000;
const LOOKAHEAD_MS              = 2 * 60 * 1_000;
const RETRY_BUDGET_MS           = 50_000;
const SEND_TIMEOUT_MS           = 15_000;
const SEND_RETRY_BACKOFF_MAX_MS = 15_000;

const logger = P({ level: process.env.WA_LOG_LEVEL ?? "silent" });

/* ─────────────────────────────────────────────────────────────────────────────
   TIPOS
   ───────────────────────────────────────────────────────────────────────────── */
interface WaAccount {
  id: string;
  name: string;
  phone_number: string;
  creds_json: Record<string, unknown> | null;
  is_active: boolean;
}

interface WaGroupMember {
  id: string;
  message_text: string | null;
  position: number;
  is_active: boolean;
  wa_accounts: WaAccount | null;
}

interface WaGroup {
  id: string;
  name: string;
  wa_chat_id: string | null;
  wa_chat_name: string | null;
  group_type: "open" | "closed";
  wa_group_members: WaGroupMember[];
}

interface WaSchedule {
  id: string;
  cron_expression: string;
  user_id: string;
  group_id: string;
  next_run_at: string;
  retry_window_seconds: number;
  retry_interval_seconds: number;
  retry_interval_max_seconds: number;
  retry_count: number;
  retry_until: string | null;
  last_attempt_at: string | null;
  wa_groups: WaGroup;
}

interface DispatchResult {
  account_id: string;
  message_text: string | null;
  status: "sent" | "failed" | "skipped";
  retryable: boolean;
  error?: string;
}

/* ─────────────────────────────────────────────────────────────────────────────
   ESTADO GLOBAL
   ───────────────────────────────────────────────────────────────────────────── */
const sockets               = new Map<string, WASocket>();
const socketReady           = new Map<string, boolean>();
const connectingPromises    = new Map<string, Promise<WASocket>>();
const accountCache          = new Map<string, WaAccount>();
const schedulePrefetchCache = new Map<string, WaSchedule>();
const scheduledTimers       = new Map<string, ReturnType<typeof setTimeout>>();
const prefetchTimers        = new Map<string, ReturnType<typeof setTimeout>>();
const sniperTimers          = new Map<string, ReturnType<typeof setTimeout>>();
const firingNow             = new Set<string>();
const sniperFiringNow       = new Set<string>();

/* ─────────────────────────────────────────────────────────────────────────────
   QUERY REUTILIZADA
   ───────────────────────────────────────────────────────────────────────────── */
const SCHEDULE_SELECT = `
  id, cron_expression, user_id, group_id, next_run_at,
  retry_window_seconds, retry_interval_seconds, retry_interval_max_seconds,
  retry_count, retry_until, last_attempt_at,
  wa_groups(
    id, name, wa_chat_id, wa_chat_name, group_type,
    wa_group_members(
      id, message_text, position, is_active,
      wa_accounts(id, name, phone_number, creds_json, is_active)
    )
  )
`.trim();

/* ─────────────────────────────────────────────────────────────────────────────
   HELPERS PUROS
   ───────────────────────────────────────────────────────────────────────────── */
function isRetryableError(_msg: string): boolean {
  return true;
}

function nextWeeklyOccurrence(cron: string): string {
  const parts = cron.trim().split(/\s+/);
  const mi    = parseInt(parts[0], 10);
  const h     = parseInt(parts[1], 10);
  const dow   = parseInt(parts[4], 10);

  if (
    parts.length < 5 ||
    isNaN(mi) || isNaN(h) || isNaN(dow) ||
    mi < 0 || mi > 59 || h < 0 || h > 23 || dow < 0 || dow > 6
  ) {
    throw new Error(`cron_expression inválida: "${cron}"`);
  }

  const now = new Date();
  let daysUntil = (dow - now.getUTCDay() + 7) % 7;

  if (daysUntil === 0) {
    const nowMins  = now.getUTCHours() * 60 + now.getUTCMinutes();
    const targMins = h * 60 + mi;
    if (targMins <= nowMins) daysUntil = 7;
  }

  const next = new Date(now);
  next.setUTCDate(next.getUTCDate() + daysUntil);
  next.setUTCHours(h, mi, 0, 0);
  return next.toISOString();
}

function calcRetryInterval(count: number, base: number, max: number): number {
  return Math.min(base * Math.pow(2, count), max);
}

function isRetryDue(schedule: WaSchedule, now: Date): boolean {
  if (!schedule.last_attempt_at) return true;
  const last     = new Date(schedule.last_attempt_at);
  const interval = calcRetryInterval(
    schedule.retry_count,
    schedule.retry_interval_seconds,
    schedule.retry_interval_max_seconds
  );
  return now >= new Date(last.getTime() + interval * 1_000);
}

/* ─────────────────────────────────────────────────────────────────────────────
   SESSÃO BAILEYS — SUPABASE COMO STORAGE
   
   Estrutura salva em wa_accounts.creds_json:
   {
     creds: { ... },   // credenciais principais
     keys:  { ... }    // signal keys (pré-keys, sessions, etc)
   }
   ───────────────────────────────────────────────────────────────────────────── */
interface SupabaseAuthState {
  state: AuthenticationState;
  saveCreds: () => Promise<void>;
}

async function useSupabaseAuthState(account: WaAccount): Promise<SupabaseAuthState> {
  const data: { creds?: Record<string, unknown>; keys?: Record<string, unknown> } =
    (account.creds_json as any) ?? {};

  const keyStore: Record<string, Record<string, unknown>> = (data.keys as any) ?? {};

  const state: AuthenticationState = {
    // FIX v2: usa initAuthCreds() em vez de {} as any para garantir estrutura correta
    creds: (data.creds as any) ?? initAuthCreds(),
    keys: {
      get: (type: string, ids: string[]) => {
        const dict: Record<string, unknown> = {};
        for (const id of ids) {
          const val = (keyStore[type] as any)?.[id];
          if (val !== undefined) dict[id] = val;
        }
        return dict as any;
      },
      set: (items: Record<string, Record<string, unknown>>) => {
        for (const [type, typeItems] of Object.entries(items)) {
          if (!keyStore[type]) keyStore[type] = {};
          for (const [id, val] of Object.entries(typeItems)) {
            if (val === null || val === undefined) {
              delete (keyStore[type] as any)[id];
            } else {
              (keyStore[type] as any)[id] = val;
            }
          }
        }
      },
    } as any,
  };

  const saveCreds = async () => {
    const payload = { creds: state.creds, keys: keyStore };
    const { error } = await supabase
      .from("wa_accounts")
      .update({ creds_json: payload, updated_at: new Date().toISOString() })
      .eq("id", account.id);

    if (error) {
      console.error(`[creds] Falha ao salvar creds de ${account.phone_number}:`, error.message);
    } else {
      const cached = accountCache.get(account.id);
      if (cached) cached.creds_json = payload as any;
    }
  };

  return { state, saveCreds };
}

/* ─────────────────────────────────────────────────────────────────────────────
   GERENCIAMENTO DE CONEXÕES BAILEYS
   ───────────────────────────────────────────────────────────────────────────── */
async function getSocket(account: WaAccount): Promise<WASocket> {
  const existing = sockets.get(account.id);
  if (existing && socketReady.get(account.id)) return existing;

  const inflight = connectingPromises.get(account.id);
  if (inflight) return inflight;

  const connectPromise = (async () => {
    const old = sockets.get(account.id);
    if (old) {
      try { old.end(undefined); } catch {}
      sockets.delete(account.id);
      socketReady.set(account.id, false);
    }

    const { version } = await fetchLatestBaileysVersion();
    const { state, saveCreds } = await useSupabaseAuthState(account);

    const sock = makeWASocket({
      version,
      logger,
      printQRInTerminal: false,
      auth: {
        creds: state.creds,
        keys:  makeCacheableSignalKeyStore(state.keys as any, logger),
      },
      browser:             ["SenhaBaixa", "Chrome", "1.0.0"],
      connectTimeoutMs:    30_000,
      keepAliveIntervalMs: 30_000,
      retryRequestDelayMs: 250,
      maxMsgRetryCount:    0,
      getMessage: async () => undefined,
    });

    sockets.set(account.id, sock);
    socketReady.set(account.id, false);

    sock.ev.on("creds.update", saveCreds);

    sock.ev.on("connection.update", async (update) => {
      const { connection, lastDisconnect, qr } = update;

      if (qr) {
        // FIX v2: converte string bruta do Baileys para PNG base64 antes de salvar
        // O frontend espera data:image/png;base64,... — sem isso a imagem não renderiza
        console.log(`[connect] QR gerado para ${account.phone_number} — convertendo para PNG e salvando`);
        try {
          const qrDataUrl = await QRCode.toDataURL(qr, { width: 300, margin: 2 });
          await supabase
            .from("wa_accounts")
            .update({ creds_json: { qr: qrDataUrl } })
            .eq("id", account.id);
        } catch (err: any) {
          console.error(`[connect] Falha ao gerar QR PNG para ${account.phone_number}: ${err.message}`);
        }
      }

      if (connection === "open") {
        socketReady.set(account.id, true);
        console.log(`[connect] ✓ Conectado: ${account.phone_number}`);
      }

      if (connection === "close") {
        socketReady.set(account.id, false);
        sockets.delete(account.id);

        const statusCode = (lastDisconnect?.error as Boom)?.output?.statusCode;
        const loggedOut  = statusCode === DisconnectReason.loggedOut;

        if (loggedOut) {
          console.warn(`[connect] Sessão encerrada (logged out): ${account.phone_number} — desativando`);
          await supabase
            .from("wa_accounts")
            .update({ is_active: false, creds_json: null })
            .eq("id", account.id);
          accountCache.delete(account.id);
          return;
        }

        console.warn(`[connect] Desconectado (${statusCode}) — reconectando em 3s: ${account.phone_number}`);
        setTimeout(() => {
          const freshAccount = accountCache.get(account.id) ?? account;
          getSocket(freshAccount).catch(err =>
            console.error(`[connect] Falha na reconexão de ${account.phone_number}:`, err.message)
          );
        }, 3_000);
      }
    });

    // FIX v2: só bloqueia esperando socketReady se a conta JÁ TEM creds salvas.
    // Contas novas (sem creds) precisam escanear QR primeiro — não há como ficar "ready"
    // antes do scan, então não esperamos: o socket fica em background gerando o QR.
    if (account.creds_json && !(account.creds_json as any).qr) {
      await new Promise<void>((resolve, reject) => {
        const timeout = setTimeout(() => reject(new Error("CONNECT_TIMEOUT_30s")), 30_000);
        const check = () => {
          if (socketReady.get(account.id)) {
            clearTimeout(timeout);
            resolve();
          } else {
            setTimeout(check, 100);
          }
        };
        check();
      });
    }

    return sock;
  })();

  connectingPromises.set(account.id, connectPromise);
  try {
    return await connectPromise;
  } finally {
    connectingPromises.delete(account.id);
  }
}

/* ─────────────────────────────────────────────────────────────────────────────
   ENVIO COM RETRY INTERNO
   ───────────────────────────────────────────────────────────────────────────── */
async function sendMessage(
  sock: WASocket,
  account: WaAccount,
  jid: string,
  messageText: string,
  cycleMessageId: string
): Promise<void> {
  const budgetEnd = Date.now() + RETRY_BUDGET_MS;
  let attempt = 0;

  while (Date.now() < budgetEnd) {
    attempt++;
    const timeLeft = budgetEnd - Date.now();
    if (timeLeft < 500) break;

    try {
      await Promise.race([
        sock.sendMessage(jid, { text: messageText }),
        new Promise<never>((_, r) =>
          setTimeout(
            () => r(new Error(`TIMEOUT tentativa ${attempt}`)),
            Math.min(SEND_TIMEOUT_MS, timeLeft - 100)
          )
        ),
      ]);

      if (attempt > 1) console.log(`[send] ✓ ${account.phone_number} enviou na tentativa ${attempt}`);
      return;

    } catch (err: any) {
      const remaining = budgetEnd - Date.now();
      if (remaining > 500) {
        const backoffMs   = Math.min(1_000 * Math.pow(2, attempt - 1), SEND_RETRY_BACKOFF_MAX_MS);
        const safeBackoff = Math.min(backoffMs, remaining - 500);
        console.warn(
          `[send] tentativa ${attempt} falhou — aguardando ${safeBackoff}ms ` +
          `(${Math.round(remaining / 1_000)}s restantes): ${err.message}`
        );
        if (safeBackoff > 0) await new Promise(r => setTimeout(r, safeBackoff));
      }
    }
  }

  throw new Error(`BUDGET_EXCEEDED após ${attempt} tentativa(s)`);
}

/* ─────────────────────────────────────────────────────────────────────────────
   SNIPER SEND
   ───────────────────────────────────────────────────────────────────────────── */
async function sniperSendOnce(
  sock: WASocket,
  jid: string,
  messageText: string
): Promise<void> {
  await Promise.race([
    sock.sendMessage(jid, { text: messageText }),
    new Promise<never>((_, r) =>
      setTimeout(() => r(new Error("SNIPER_TIMEOUT")), SNIPER_SEND_TIMEOUT_MS)
    ),
  ]);
}

/* ─────────────────────────────────────────────────────────────────────────────
   DEDUP
   ───────────────────────────────────────────────────────────────────────────── */
async function getAlreadySentIds(schedule: WaSchedule): Promise<Set<string>> {
  const cycleStart = schedule.retry_until
    ? new Date(
        new Date(schedule.retry_until).getTime() - schedule.retry_window_seconds * 1_000
      ).toISOString()
    : schedule.next_run_at;

  const { data, error } = await supabase
    .from("wa_dispatch_logs")
    .select("account_id")
    .eq("schedule_id", schedule.id)
    .eq("status", "sent")
    .gte("sent_at", cycleStart);

  if (error) {
    console.warn(`[dedup] Falha ao buscar enviados do schedule ${schedule.id}:`, error.message);
    return new Set();
  }
  return new Set((data ?? []).map(r => r.account_id as string));
}

/* ─────────────────────────────────────────────────────────────────────────────
   SNIPER LOOP — GRUPOS FECHADOS
   ───────────────────────────────────────────────────────────────────────────── */
async function sniperFireClosed(scheduleId: string): Promise<void> {
  if (sniperFiringNow.has(scheduleId)) {
    console.warn(`[sniper] Schedule ${scheduleId} já em execução — ignorando duplo disparo`);
    return;
  }
  sniperFiringNow.add(scheduleId);

  const sniperEnteredAt = Date.now();

  try {
    const now = new Date();

    let schedule = schedulePrefetchCache.get(scheduleId);
    if (schedule) {
      schedulePrefetchCache.delete(scheduleId);
      console.log(`[sniper] ⚡ Schedule ${scheduleId} do pre-fetch cache`);
    } else {
      const { data, error } = await supabase
        .from("wa_schedules")
        .select(SCHEDULE_SELECT)
        .eq("id", scheduleId)
        .eq("is_active", true)
        .single();

      if (error || !data) {
        console.warn(`[sniper] Schedule ${scheduleId} não encontrado ou inativo.`);
        return;
      }
      schedule = data as unknown as WaSchedule;
    }

    const scheduledAt     = new Date(schedule.next_run_at).getTime();
    const plannedSniperAt = scheduledAt - SNIPER_BEFORE_MS;
    const timerLagMs      = sniperEnteredAt - plannedSniperAt;
    console.log(`[sniper][timing] timer lag: ${timerLagMs}ms (SNIPER_BEFORE_MS=${SNIPER_BEFORE_MS}, ideal=0)`);

    const group = schedule.wa_groups;
    if (!group?.wa_chat_id) {
      console.warn(`[sniper] Schedule ${scheduleId}: sem wa_chat_id — pulando.`);
      return;
    }

    if (group.wa_group_members) {
      group.wa_group_members = group.wa_group_members.map(m => ({
        ...m,
        wa_accounts: m.wa_accounts ? (accountCache.get(m.wa_accounts.id) ?? m.wa_accounts) : null,
      }));
    }

    const members = (group.wa_group_members ?? [])
      .filter(m => m.is_active && m.wa_accounts?.is_active && m.wa_accounts?.creds_json)
      .sort((a, b) => a.position - b.position);

    if (members.length === 0) {
      console.warn(`[sniper] Nenhuma conta ativa no schedule ${scheduleId} — abortando.`);
      return;
    }

    const jid            = group.wa_chat_id;
    const budgetEnd      = Date.now() + SNIPER_BUDGET_MS;
    const results: DispatchResult[] = [];
    const cycleMessageId = randomUUID();

    console.log(`[sniper] 🎯 Iniciando loop para schedule ${scheduleId} — ${members.length} conta(s) | cycle: ${cycleMessageId}`);

    // ── DEDUP PRÉ-DISPARO: aborta se qualquer conta já enviou neste ciclo ──
    const alreadySent = await getAlreadySentIds(schedule);
    if (alreadySent.size > 0) {
      console.warn(`[sniper] ⛔ Dedup: ${alreadySent.size} conta(s) já enviaram neste ciclo — abortando sniper para schedule ${scheduleId}`);
      await updateScheduleAfterDispatch(
        schedule,
        members.map(m => ({
          account_id:   m.wa_accounts!.id,
          message_text: m.message_text,
          status:       "skipped" as const,
          retryable:    false,
        })),
        now,
        cycleMessageId
      );
      return;
    }

    // ── FASE 1: loop agressivo na primeira conta ──────────────────────────
    const firstMember  = members[0];
    const firstAccount = firstMember.wa_accounts!;
    const firstText    = firstMember.message_text ?? "";

    let firstSock: WASocket;
    try {
      firstSock = await getSocket(firstAccount);
    } catch (err: any) {
      console.error(`[sniper] Falha ao conectar ${firstAccount.phone_number}: ${err.message}`);
      results.push({
        account_id:   firstAccount.id,
        message_text: firstMember.message_text,
        status:       "failed",
        retryable:    isRetryableError(err.message),
        error:        err.message,
      });
      await updateScheduleAfterDispatch(schedule, results, now, cycleMessageId);
      return;
    }

    let attempt        = 0;
    let firstSentAt: Date | null = null;

    while (Date.now() < budgetEnd) {
      attempt++;

      try {
        await sniperSendOnce(firstSock, jid, firstText);
        firstSentAt = new Date();

        const invokeRttMs = firstSentAt.getTime() - sniperEnteredAt;
        const vsHorarioMs = firstSentAt.getTime() - scheduledAt;
        console.log(`[sniper][timing] invoke RTT: ${invokeRttMs}ms`);
        console.log(`[sniper][timing] vs horário: ${vsHorarioMs > 0 ? "+" : ""}${vsHorarioMs}ms tentativa=${attempt}`);
        console.log(`[sniper] ✓ ${firstAccount.phone_number} enviou na tentativa ${attempt}`);

        results.push({
          account_id:   firstAccount.id,
          message_text: firstMember.message_text,
          status:       "sent",
          retryable:    false,
        });
        break;

      } catch (err: any) {
        // se o socket caiu durante o loop, tenta re-adquirir (budget permitting)
        if (!socketReady.get(firstAccount.id)) {
          const reacquireDeadline = Math.min(Date.now() + 6_000, budgetEnd - 500);
          if (Date.now() < reacquireDeadline) {
            console.warn(`[sniper] Socket caiu durante loop — re-adquirindo (${Math.round((reacquireDeadline - Date.now()) / 1_000)}s)`);
            try {
              firstSock = await Promise.race([
                getSocket(firstAccount),
                new Promise<never>((_, r) =>
                  setTimeout(() => r(new Error("REACQUIRE_TIMEOUT")), reacquireDeadline - Date.now())
                ),
              ]);
              console.log(`[sniper] ✓ Socket re-adquirido para ${firstAccount.phone_number}`);
            } catch (reErr: any) {
              console.warn(`[sniper] Re-acquire falhou: ${reErr.message}`);
            }
          }
        } else if (attempt % SNIPER_PAUSE_EVERY_N === 0) {
          await new Promise(r => setTimeout(r, SNIPER_PAUSE_MS));
        } else {
          await new Promise(r => setTimeout(r, SNIPER_ATTEMPT_INTERVAL_MS));
        }
      }
    }

    supabase.from("wa_dispatch_logs").insert({
      user_id:             schedule.user_id,
      group_id:            group.id,
      account_id:          firstAccount.id,
      schedule_id:         schedule.id,
      cycle_message_id:    cycleMessageId,
      status:              firstSentAt ? "sent" : "failed",
      message_text:        firstMember.message_text,
      position_rank:       1,
      group_name_snapshot: group.name,
      chat_name_snapshot:  group.wa_chat_name,
      sent_at:             firstSentAt ? firstSentAt.toISOString() : null,
      error_message:       firstSentAt ? null : `BUDGET_EXCEEDED após ${attempt} tentativas`,
    }).then(({ error: e }) => {
      if (e) console.error(`[sniper][log] Falha ao inserir log para ${firstAccount.id}:`, e.message);
    });

    if (!firstSentAt) {
      console.warn(`[sniper] Budget esgotado para schedule ${scheduleId} após ${attempt} tentativas`);
      results.push({
        account_id:   firstAccount.id,
        message_text: firstMember.message_text,
        status:       "failed",
        retryable:    true,
        error:        `SNIPER_BUDGET_EXCEEDED após ${attempt} tentativas`,
      });
      await updateScheduleAfterDispatch(schedule, results, now, cycleMessageId);
      return;
    }

    // ── FASE 2: demais contas ────────────────────────────────────────────
    for (let i = 1; i < members.length; i++) {
      await new Promise(r => setTimeout(r, SNIPER_INTER_ACCOUNT_DELAY_MS));

      const member  = members[i];
      const account = member.wa_accounts!;
      const text    = member.message_text ?? "";
      let   sentAt: Date | null = null;
      let   error: string | undefined;

      try {
        const sock = await getSocket(account);
        await sniperSendOnce(sock, jid, text);
        sentAt = new Date();
        console.log(`[sniper] ✓ Conta ${i + 1}/${members.length} ${account.phone_number} enviou`);
        results.push({ account_id: account.id, message_text: member.message_text, status: "sent", retryable: false });
      } catch (err: any) {
        error = String(err?.message ?? "");
        console.error(`[sniper] ✗ Conta ${i + 1}/${members.length} ${account.phone_number}: ${error}`);
        results.push({ account_id: account.id, message_text: member.message_text, status: "failed", retryable: isRetryableError(error), error });
      }

      supabase.from("wa_dispatch_logs").insert({
        user_id:             schedule.user_id,
        group_id:            group.id,
        account_id:          account.id,
        schedule_id:         schedule.id,
        cycle_message_id:    cycleMessageId,
        status:              sentAt ? "sent" : "failed",
        message_text:        member.message_text,
        position_rank:       i + 1,
        group_name_snapshot: group.name,
        chat_name_snapshot:  group.wa_chat_name,
        sent_at:             sentAt ? sentAt.toISOString() : null,
        error_message:       error ?? null,
      }).then(({ error: e }) => {
        if (e) console.error(`[sniper][log] Falha ao inserir log para ${account.id}:`, e.message);
      });
    }

    // ── FASE 3: atualiza schedule ────────────────────────────────────────
    await updateScheduleAfterDispatch(schedule, results, firstSentAt, cycleMessageId);

  } finally {
    sniperFiringNow.delete(scheduleId);
    firingNow.add(scheduleId);
    setTimeout(() => firingNow.delete(scheduleId), SNIPER_DONE_BLOCK_TTL_MS);
  }
}

/* ─────────────────────────────────────────────────────────────────────────────
   DESPACHO GENÉRICO
   ───────────────────────────────────────────────────────────────────────────── */
async function dispatchToGroup(
  schedule: WaSchedule,
  group: WaGroup,
  alreadySent: Set<string>,
  cycleMessageId: string
): Promise<DispatchResult[]> {
  const members = (group.wa_group_members ?? [])
    .filter(m => m.is_active && m.wa_accounts?.is_active && m.wa_accounts?.creds_json)
    .sort((a, b) => a.position - b.position);

  return Promise.all(members.map(async (member, i) => {
    const account      = member.wa_accounts!;
    const positionRank = i + 1;

    if (alreadySent.has(account.id)) {
      console.log(`[dispatch] ↷ ${account.phone_number} — já enviou neste ciclo`);
      return { account_id: account.id, message_text: member.message_text, status: "skipped" as const, retryable: false };
    }

    let status: "sent" | "failed" = "failed";
    let error: string | undefined;
    let retryable = false;

    try {
      const sock = await getSocket(account);
      await sendMessage(sock, account, group.wa_chat_id!, member.message_text ?? "", cycleMessageId);
      status = "sent";
      alreadySent.add(account.id);
      console.log(`[dispatch] ✓ ${account.phone_number}`);
    } catch (err) {
      error     = err instanceof Error ? err.message : String(err);
      retryable = isRetryableError(error);
      console.error(`[dispatch] ✗ ${account.phone_number} [${retryable ? "retryável" : "permanente"}]: ${error}`);
    }

    supabase.from("wa_dispatch_logs").insert({
      user_id:             schedule.user_id,
      group_id:            group.id,
      account_id:          account.id,
      schedule_id:         schedule.id,
      cycle_message_id:    cycleMessageId,
      status,
      message_text:        member.message_text,
      position_rank:       positionRank,
      group_name_snapshot: group.name,
      chat_name_snapshot:  group.wa_chat_name,
      sent_at:             status === "sent" ? new Date().toISOString() : null,
      error_message:       error ?? null,
    }).then(({ error: e }) => {
      if (e) console.error(`[log] Falha ao inserir dispatch_log para ${account.id}:`, e.message);
    });

    return { account_id: account.id, message_text: member.message_text, status, retryable, error };
  }));
}

/* ─────────────────────────────────────────────────────────────────────────────
   ATUALIZAÇÃO DO SCHEDULE
   ───────────────────────────────────────────────────────────────────────────── */
async function updateScheduleAfterDispatch(
  schedule: WaSchedule,
  results: DispatchResult[],
  now: Date,
  cycleMessageId: string
): Promise<void> {
  const nowISO         = now.toISOString();
  const sentCount      = results.filter(r => r.status === "sent").length;
  const skippedCount   = results.filter(r => r.status === "skipped").length;
  const retryableFails = results.filter(r => r.status === "failed" && r.retryable);
  const permanentFails = results.filter(r => r.status === "failed" && !r.retryable);

  const allOk =
    results.length > 0 &&
    retryableFails.length === 0 &&
    permanentFails.length === 0 &&
    (sentCount + skippedCount) > 0;

  if (allOk) {
    let nextRun: string;
    try {
      nextRun = nextWeeklyOccurrence(schedule.cron_expression);
    } catch (err) {
      console.error(`[schedule] cron inválido em ${schedule.id}, desativando:`, err);
      await supabase.from("wa_schedules").update({ is_active: false }).eq("id", schedule.id);
      return;
    }

    supabase.from("wa_schedules").update({
      next_run_at:         nextRun,
      last_run_at:         nowISO,
      retry_until:         null,
      retry_count:         0,
      last_attempt_at:     nowISO,
      last_attempt_status: "sent",
      last_attempt_error:  null,
    }).eq("id", schedule.id).then(({ error: e }) => {
      if (e) console.error(`[schedule] Falha ao atualizar ${schedule.id}:`, e.message);
    });

    console.log(`[schedule] ✓ Schedule ${schedule.id} OK. Próxima: ${nextRun}`);
    scheduleTimer(schedule.id, nextRun);

  } else {
    const newRetryCount = schedule.retry_count + 1;
    const retryUntil    = schedule.retry_until ??
      new Date(now.getTime() + schedule.retry_window_seconds * 1_000).toISOString();
    const interval      = calcRetryInterval(
      newRetryCount,
      schedule.retry_interval_seconds,
      schedule.retry_interval_max_seconds
    );
    const failErrors = results
      .filter(r => r.error)
      .map(r => `[${r.account_id}] ${r.error}`)
      .join("; ");

    console.warn(
      `[schedule] ⚠ ${schedule.id}: ${retryableFails.length} falha(s) retryável(eis), ` +
      `${permanentFails.length} permanente(s). Retry #${newRetryCount} em ~${interval}s`
    );

    await supabase.from("wa_schedules").update({
      retry_until:         retryUntil,
      retry_count:         newRetryCount,
      last_attempt_at:     nowISO,
      last_attempt_status: "retrying",
      last_attempt_error:  failErrors || null,
    }).eq("id", schedule.id);

    const retryAt = new Date(now.getTime() + interval * 1_000);
    if (retryAt < new Date(retryUntil)) {
      scheduleTimer(schedule.id, retryAt.toISOString());
    }
  }
}

/* ─────────────────────────────────────────────────────────────────────────────
   FIRE SCHEDULE
   ───────────────────────────────────────────────────────────────────────────── */
async function fireSchedule(scheduleId: string): Promise<void> {
  if (sniperFiringNow.has(scheduleId)) {
    console.warn(`[fire] Schedule ${scheduleId} em execução no sniper — ignorando fireSchedule`);
    return;
  }
  if (firingNow.has(scheduleId)) {
    console.warn(`[fire] Schedule ${scheduleId} já em execução — ignorando duplo disparo`);
    return;
  }
  firingNow.add(scheduleId);

  try {
    const now = new Date();

    let schedule = schedulePrefetchCache.get(scheduleId);
    if (schedule) {
      schedulePrefetchCache.delete(scheduleId);
      console.log(`[fire] ⚡ Schedule ${scheduleId} do pre-fetch cache`);
    } else {
      const { data, error } = await supabase
        .from("wa_schedules")
        .select(SCHEDULE_SELECT)
        .eq("id", scheduleId)
        .eq("is_active", true)
        .single();

      if (error || !data) {
        console.warn(`[fire] Schedule ${scheduleId} não encontrado ou inativo.`);
        return;
      }
      schedule = data as unknown as WaSchedule;
    }

    const group = schedule.wa_groups;
    if (!group?.wa_chat_id) {
      console.warn(`[fire] Schedule ${scheduleId}: sem wa_chat_id — pulando.`);
      return;
    }

    if (group.wa_group_members) {
      group.wa_group_members = group.wa_group_members.map(m => ({
        ...m,
        wa_accounts: m.wa_accounts ? (accountCache.get(m.wa_accounts.id) ?? m.wa_accounts) : null,
      }));
    }

    const cycleMessageId = randomUUID();
    const alreadySent    = schedule.retry_until
      ? await getAlreadySentIds(schedule)
      : new Set<string>();

    if (alreadySent.size > 0) {
      console.log(`[dedup] ${alreadySent.size} account(s) já enviaram neste ciclo — pulando.`);
    }

    const results = await dispatchToGroup(schedule, group, alreadySent, cycleMessageId);
    await updateScheduleAfterDispatch(schedule, results, now, cycleMessageId);

  } finally {
    firingNow.delete(scheduleId);
  }
}

/* ─────────────────────────────────────────────────────────────────────────────
   TIMER DE PRECISÃO + PRE-FETCH + SNIPER
   ───────────────────────────────────────────────────────────────────────────── */
function scheduleTimer(scheduleId: string, nextRunAt: string): void {
  const delay = new Date(nextRunAt).getTime() - Date.now();

  if (delay < -5_000) {
    console.warn(`[timer] Schedule ${scheduleId} ignorado — muito no passado (${nextRunAt})`);
    return;
  }

  const prev = scheduledTimers.get(scheduleId);
  if (prev) clearTimeout(prev);
  const prevPrefetch = prefetchTimers.get(scheduleId);
  if (prevPrefetch) { clearTimeout(prevPrefetch); prefetchTimers.delete(scheduleId); }
  const prevSniper = sniperTimers.get(scheduleId);
  if (prevSniper) { clearTimeout(prevSniper); sniperTimers.delete(scheduleId); }

  const effectiveDelay = Math.max(0, delay);

  // Pre-fetch 800ms antes
  if (effectiveDelay > PREFETCH_BEFORE_MS) {
    const prefetchDelay = effectiveDelay - PREFETCH_BEFORE_MS;
    const pt = setTimeout(async () => {
      prefetchTimers.delete(scheduleId);
      try {
        const { data, error } = await supabase
          .from("wa_schedules")
          .select(SCHEDULE_SELECT)
          .eq("id", scheduleId)
          .eq("is_active", true)
          .single();

        if (error || !data) {
          console.warn(`[prefetch] Schedule ${scheduleId} inativo — ignorando`);
          return;
        }

        const s = data as unknown as WaSchedule;
        if (s.wa_groups?.wa_group_members) {
          s.wa_groups.wa_group_members = s.wa_groups.wa_group_members.map(m => ({
            ...m,
            wa_accounts: m.wa_accounts ? (accountCache.get(m.wa_accounts.id) ?? m.wa_accounts) : null,
          }));
        }

        schedulePrefetchCache.set(scheduleId, s);
        console.log(`[prefetch] ✅ Schedule ${scheduleId} pré-carregado`);
      } catch (err: any) {
        console.warn(`[prefetch] Falha ao pré-carregar ${scheduleId}: ${err.message}`);
      }
    }, prefetchDelay);
    prefetchTimers.set(scheduleId, pt);
  }

  // Sniper SNIPER_BEFORE_MS antes
  if (effectiveDelay > SNIPER_BEFORE_MS) {
    const sniperDelay = effectiveDelay - SNIPER_BEFORE_MS;
    const st = setTimeout(async () => {
      sniperTimers.delete(scheduleId);
      try {
        await sniperFireClosed(scheduleId);
      } catch (err) {
        console.error(`[sniper] Erro inesperado ao disparar ${scheduleId}:`, err);
      }
    }, sniperDelay);
    sniperTimers.set(scheduleId, st);
    console.log(`[sniper] ⏰ Sniper agendado para ${scheduleId} em ${Math.round(sniperDelay / 1_000)}s`);
  }

  // Fire no horário exato (fallback/guard)
  const timer = setTimeout(async () => {
    scheduledTimers.delete(scheduleId);
    try {
      await fireSchedule(scheduleId);
    } catch (err) {
      console.error(`[timer] Erro inesperado ao disparar ${scheduleId}:`, err);
    }
  }, effectiveDelay);

  scheduledTimers.set(scheduleId, timer);

  const fireAt = new Date(Date.now() + effectiveDelay).toISOString();
  console.log(`[timer] ⏰ Schedule ${scheduleId} — dispara em ${Math.round(effectiveDelay / 1_000)}s (${fireAt})`);
}

/* ─────────────────────────────────────────────────────────────────────────────
   RELOAD PERIÓDICO
   ───────────────────────────────────────────────────────────────────────────── */
async function reloadSchedules(): Promise<void> {
  const now          = new Date();
  const nowISO       = now.toISOString();
  const lookaheadISO = new Date(now.getTime() + LOOKAHEAD_MS).toISOString();

  const [
    { data: futureSchedules },
    { data: retrySchedules },
    { data: expiredRetries },
  ] = await Promise.all([
    supabase.from("wa_schedules")
      .select("id, next_run_at")
      .eq("is_active", true)
      .is("retry_until", null)
      .lte("next_run_at", lookaheadISO),

    supabase.from("wa_schedules")
      .select(SCHEDULE_SELECT)
      .eq("is_active", true)
      .not("retry_until", "is", null)
      .gt("retry_until", nowISO),

    supabase.from("wa_schedules")
      .select("id, cron_expression")
      .eq("is_active", true)
      .not("retry_until", "is", null)
      .lte("retry_until", nowISO),
  ]);

  await Promise.all((expiredRetries ?? []).map(async expired => {
    console.warn(`[reload] Schedule ${expired.id}: retry expirou sem sucesso.`);
    let nextRun: string;
    try { nextRun = nextWeeklyOccurrence(expired.cron_expression); }
    catch {
      await supabase.from("wa_schedules").update({ is_active: false }).eq("id", expired.id);
      return;
    }
    await supabase.from("wa_schedules").update({
      next_run_at:         nextRun,
      last_run_at:         nowISO,
      retry_until:         null,
      retry_count:         0,
      last_attempt_at:     nowISO,
      last_attempt_status: "failed",
      last_attempt_error:  "Retry expirou sem sucesso total",
    }).eq("id", expired.id);
    scheduleTimer(expired.id, nextRun);
  }));

  for (const s of futureSchedules ?? []) {
    if (!scheduledTimers.has(s.id)) {
      scheduleTimer(s.id, s.next_run_at);
    }
  }

  for (const s of retrySchedules ?? []) {
    const schedule = s as unknown as WaSchedule;
    if (
      isRetryDue(schedule, now) &&
      !scheduledTimers.has(schedule.id) &&
      !firingNow.has(schedule.id) &&
      !sniperFiringNow.has(schedule.id)
    ) {
      console.log(`[reload] Schedule ${schedule.id} em retry — disparando agora.`);
      const cycleMessageId = randomUUID();
      const group          = schedule.wa_groups;
      const alreadySent    = await getAlreadySentIds(schedule);
      dispatchToGroup(schedule, group, alreadySent, cycleMessageId)
        .then(results => updateScheduleAfterDispatch(schedule, results, now, cycleMessageId))
        .catch(err => console.error(`[reload] Erro no retry ${schedule.id}:`, err));
    }
  }
}

/* ─────────────────────────────────────────────────────────────────────────────
   PRE-WARM
   ───────────────────────────────────────────────────────────────────────────── */
async function prewarmAccounts(): Promise<void> {
  const { data, error } = await supabase
    .from("wa_accounts")
    .select("id, name, phone_number, creds_json, is_active")
    .eq("is_active", true);

  if (error) { console.warn("[prewarm] Falha ao buscar contas:", error.message); return; }

  const accounts = (data ?? []) as WaAccount[];
  for (const account of accounts) accountCache.set(account.id, account);

  console.log(`[prewarm] Conectando ${accounts.length} conta(s) WA...`);

  await Promise.allSettled(accounts.map(async account => {
    // Pula contas sem creds reais (apenas QR pendente ou nulo)
    if (!account.creds_json || (account.creds_json as any).qr) {
      console.warn(`[prewarm] ${account.phone_number} sem creds — precisa escanear QR`);
      return;
    }
    try {
      await getSocket(account);
      console.log(`[prewarm] ✓ ${account.phone_number} pronto`);
    } catch (err: any) {
      console.warn(`[prewarm] Falha ao conectar ${account.phone_number}: ${err.message}`);
    }
  }));

  console.log("[prewarm] ✓ Concluído");
}

/* ─────────────────────────────────────────────────────────────────────────────
   HTTP SERVER
   ───────────────────────────────────────────────────────────────────────────── */
function jsonResponse(res: http.ServerResponse, status: number, body: unknown) {
  res.writeHead(status, { "Content-Type": "application/json" });
  res.end(JSON.stringify(body));
}

const httpServer = http.createServer(async (req, res) => {
  if (WORKER_SECRET && req.headers["x-worker-secret"] !== WORKER_SECRET) {
    return jsonResponse(res, 401, { error: "Unauthorized" });
  }

  const url = new URL(req.url ?? "/", `http://localhost:${WORKER_PORT}`);

  // GET /accounts/:id/groups
  const groupsMatch = url.pathname.match(/^\/accounts\/([^/]+)\/groups$/);
  if (req.method === "GET" && groupsMatch) {
    const accountId = groupsMatch[1];
    const account = accountCache.get(accountId);
    if (!account) return jsonResponse(res, 404, { error: "Conta não encontrada no cache" });

    if (!socketReady.get(accountId)) {
      return jsonResponse(res, 503, { error: "Conta não conectada — tente novamente em instantes" });
    }

    try {
      const sock    = await getSocket(account);
      const groups_ = await sock.groupFetchAllParticipating();
      const list    = Object.values(groups_).map(g => ({
        id:   g.id,
        name: g.subject,
        size: g.size,
      })).sort((a, b) => a.name.localeCompare(b.name));
      return jsonResponse(res, 200, list);
    } catch (err: any) {
      return jsonResponse(res, 500, { error: err.message });
    }
  }

  // POST /accounts/:id/reload
  const reloadMatch = url.pathname.match(/^\/accounts\/([^/]+)\/reload$/);
  if (req.method === "POST" && reloadMatch) {
    const accountId = reloadMatch[1];
    const { data: row, error } = await supabase
      .from("wa_accounts")
      .select("id, name, phone_number, creds_json, is_active")
      .eq("id", accountId)
      .single();

    if (error || !row) return jsonResponse(res, 404, { error: "Conta não encontrada" });

    const account = row as WaAccount;
    accountCache.set(accountId, account);

    if (!account.is_active) {
      return jsonResponse(res, 200, { ok: true, skipped: true, reason: "conta inativa" });
    }

    // Derruba socket anterior
    const old = sockets.get(accountId);
    if (old) {
      try { old.end(undefined); } catch {}
      sockets.delete(accountId);
      socketReady.set(accountId, false);
    }

    // FIX v2: conta sem creds reais → inicia em background para gerar QR
    // Sem esse tratamento, o /reload retornava "skipped" e o QR nunca era gerado
    if (!account.creds_json || (account.creds_json as any).qr) {
      getSocket(account).catch(err =>
        console.warn(`[reload] Falha ao iniciar QR para ${account.phone_number}: ${err.message}`)
      );
      console.log(`[http] /reload → QR iniciado para ${account.phone_number}`);
      return jsonResponse(res, 200, { ok: true, qr_pending: true });
    }

    try {
      await getSocket(account);
      console.log(`[http] /reload ✓ ${account.phone_number}`);
      return jsonResponse(res, 200, { ok: true });
    } catch (err: any) {
      return jsonResponse(res, 500, { error: err.message });
    }
  }

  // POST /groups/:id/dispatch
  const dispatchMatch = url.pathname.match(/^\/groups\/([^/]+)\/dispatch$/);
  if (req.method === "POST" && dispatchMatch) {
    const groupId = dispatchMatch[1];

    try {
      const { data, error } = await supabase
        .from("wa_groups")
        .select(`
          id, name, wa_chat_id, wa_chat_name, group_type,
          wa_group_members(
            id, message_text, position, is_active,
            wa_accounts(id, name, phone_number, creds_json, is_active)
          )
        `)
        .eq("id", groupId)
        .single();

      if (error || !data) return jsonResponse(res, 404, { error: "Grupo não encontrado" });

      const group          = data as unknown as WaGroup;
      const cycleMessageId = randomUUID();
      const results        = await dispatchToGroup(
        { id: `manual-${Date.now()}`, user_id: "", group_id: groupId } as any,
        group,
        new Set(),
        cycleMessageId
      );

      const sent   = results.filter(r => r.status === "sent").length;
      const failed = results.filter(r => r.status === "failed").length;
      return jsonResponse(res, 200, { ok: true, sent, failed, results });
    } catch (err: any) {
      return jsonResponse(res, 500, { error: err.message });
    }
  }

  // GET /health
  if (req.method === "GET" && url.pathname === "/health") {
    return jsonResponse(res, 200, {
      ok:       true,
      accounts: sockets.size,
      ready:    [...socketReady.entries()].filter(([, v]) => v).length,
      timers:   scheduledTimers.size,
    });
  }

  jsonResponse(res, 404, { error: "Not found" });
});

httpServer.listen(WORKER_PORT, () => {
  console.log(`[worker-wa] HTTP interno escutando na porta ${WORKER_PORT}`);
});

/* ─────────────────────────────────────────────────────────────────────────────
   GRACEFUL SHUTDOWN
   ───────────────────────────────────────────────────────────────────────────── */
async function shutdown() {
  console.log("[worker-wa] Encerrando...");
  for (const t of prefetchTimers.values()) clearTimeout(t);
  for (const t of sniperTimers.values())   clearTimeout(t);
  for (const t of scheduledTimers.values()) clearTimeout(t);
  httpServer.close();
  await Promise.all([...sockets.entries()].map(async ([id, sock]) => {
    try { sock.end(undefined); } catch {}
    console.log(`[connect] Desconectado: ${id}`);
  }));
  sockets.clear();
  process.exit(0);
}
process.on("SIGTERM", shutdown);
process.on("SIGINT",  shutdown);

/* ─────────────────────────────────────────────────────────────────────────────
   INICIALIZAÇÃO
   ───────────────────────────────────────────────────────────────────────────── */
async function init(): Promise<void> {
  console.log("[worker-wa] Iniciando...");
  await prewarmAccounts();
  await reloadSchedules();
  setInterval(async () => {
    try {
      await reloadSchedules();
    } catch (err) {
      console.error("[reload] Erro no reload periódico:", err);
    }
  }, RELOAD_INTERVAL_MS);
  console.log("[worker-wa] Pronto.");
}

init().catch(err => {
  console.error("[worker-wa] Falha na inicialização:", err);
  process.exit(1);
});
