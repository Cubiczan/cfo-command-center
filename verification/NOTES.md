# Verification notes — CFO Command Center sync control core

**Model:** `Sync.lean` (Lean 4.34.1, core library only, no Mathlib, no
`sorry`/`admit`/custom axioms; compiles with `~/.elan/bin/lean Sync.lean`,
exit 0, no warnings). 31 theorems. No source files were modified.

**Scope, stated plainly.** This repository is mostly dashboards and
read-only analysis. Per its own README (README.md, "Note" block at the
top), it is "the Notion dashboard layer for ClosedLoop" and "the agent
logic lives in ClosedLoop." There is **no treasury-approval workflow,
no payment execution, and no compliance state machine in this
codebase**: the four agents (`src/agents/*.py`) only read Notion
databases and write back computed fields — e.g.
`PaymentOptimizationAgent._update_queue` (payment_optimization.py:
187–198) writes recommendation/priority/savings fields, and the
payment lifecycle strings (`Queued`, `Approved`, `Processing`,
`Completed`) appear only as Notion select values the agents filter on
(payment_optimization.py:63–70) and as keyword extraction in the NL
router (tools/executor.py:183; schema enum in tools/registry.py:124). Nothing in the repo transitions them.

The one genuine control core is the **ERP → Notion sync lifecycle**,
and that is what is modeled:

| Stage | Code | Shape |
|---|---|---|
| 1 | `BaseConnector.full_sync` | connect gate → extract → transform → derived status |
| 2 | `SyncPipeline.sync_direct` | validation gate → per-record writes → derived status → audit |
| 3 | `SyncPipeline.sync_entity` / `sync_all_entities` | summation + aggregate status |
| 4 | retry loops in the REST connector and Notion client | bounded retry, first decisive outcome wins |

---

## Theorem → source mapping

### Helpers
- `sumN_append`, `sumN_eq_zero_iff` — local Nat-list lemmas used by the
  aggregation proofs (core library only, so no Mathlib `List.sum`).

### Stage 1 — `full_sync` (`src/connectors/base.py`)
Source anchors: `SyncStatus` enum ll. 36–41; `SyncResult` ll. 91–131
(`success_rate` ll. 109–114); `full_sync` ll. 196–266 (initial
`FAILED` l. 205; connect gate ll. 207–212; dataset extraction
ll. 215–221; counting loop ll. 223–237; counter assignments ll. 238–244;
status derivation ll. 246–249; exception handler ll. 251–253);
`_safe_extract` ll. 267–279; `_transform_records` ll. 281–287.

- `deriveStatus` — the status formula of ll. 246–249, error count kept
  explicit so its reachability can be analyzed.
- `deriveStatus_of_pos`, `deriveStatus_of_zero` — the formula with an
  empty error list reduces to SUCCESS (total > 0) / SKIPPED (total = 0).
- `deriveStatus_errors_zero_ne_partial` — with an empty error list the
  formula never yields PARTIAL.
- `fullSync` / `fullSyncRun` / `fullSync_completed` — the template
  method as a function of its three endings (connect gate failed /
  exception escaped the loop / completed). Error count at the
  derivation point is 0 because nothing in the `try` block appends to
  `result.errors`; transform is the as-shipped identity (no adapter in
  this repo overrides `_transform_records`, verified by grep), hence
  the code's `records_written = total_transformed` (l. 240).
- `fullSync_never_partial` — **PARTIAL is unreachable from
  `full_sync`** (see Finding 2).
- `fullSync_failed_iff` — FAILED survives iff the run never reached the
  derivation point: the connect gate (ll. 207–212) or a crash. FAILED
  is the initial value (l. 205); reaching derivation always overwrites
  it with SUCCESS or SKIPPED.
- `fullSync_counts_conserve` — on the completed path,
  written = transformed = extracted (ll. 238–244).
- `fullSync_success_iff`, `fullSync_skipped_iff` — exact
  characterizations: SUCCESS ⟺ total extracted > 0; SKIPPED ⟺ 0.
- `swallowed_failure_invisible` *(counterexample, by `rfl`)* — outcomes
  `[empty, data 3]` yield `⟨SUCCESS, 3, 3, 3⟩`, even when `empty` is an
  extractor that raised (see Finding 4).
- `all_extracts_failed_looks_skipped` *(counterexample, by `rfl`)* —
  four failed datasets yield SKIPPED, not FAILED.
- `absent_empty_indistinguishable` — `None` (not implemented) and `[]`
  (empty or failed) are indistinguishable to the counting loop.

### Stage 2 — `sync_direct` (`src/connectors/pipeline.py`)
Source anchors: `sync_direct` ll. 214–278 (initial `FAILED` l. 236;
`records_extracted` l. 238; validation gate ll. 241–250, with
`valid_records` at l. 244 and the invalid-count warning at ll. 247–248;
no-normalizer passthrough ll. 251–253; batch/write loop ll. 255–265;
status overwrite l. 269; audit record ll. 272–285).
Normalizer: `src/connectors/normalizer.py` — `ValidationResult`
ll. 91–96; `normalize` ll. 136–170 (passthrough `(records, [])` return
l. 149; one validation per record ll. 155–163).

- `GateMode` / `gateValid` — the three gate behaviors: passthrough
  (all pass), mapped `v` (exactly the `is_valid` records pass),
  unmapped (the empty validation list passes nothing).
- `countTrue_add_countFalse` — one write outcome per gated record
  partitions into written + write-errors.
- `syncDirect`, `syncDirect_status` — the function and its status
  projection (initial FAILED is always overwritten, l. 269).
- `syncDirect_never_failed_skipped` — **FAILED and SKIPPED are
  unreachable from `sync_direct`** (see Finding 3).
- `syncDirect_success_iff` — SUCCESS ⟺ zero write errors.
- `syncDirect_conservation` — written + write-errors = transformed,
  hence **written ≤ gate-valid**: nothing is written that did not pass
  the validation gate. (Assumes one outcome per gated record, as the
  loop at ll. 255–265 produces.)
- `syncDirect_all_invalid_success` *(counterexample, by `rfl`)* —
  every record invalid ⇒ still SUCCESS with 0 written (Finding 7).
- `syncDirect_unmapped_drops_all` *(counterexample, by `rfl`)* —
  normalizer present, dataset unmapped ⇒ SUCCESS with all input
  records dropped (Finding 6).

### Stage 3 — aggregation (`src/connectors/pipeline.py`)
Source anchors: `sync_entity` ll. 116–155 (disabled connectors skipped
ll. 141–144; totals ll. 146–148); `sync_all_entities` ll. 158–202
(aggregate status `"success"` iff `total_errors == 0`, else `"partial"`).

- `aggTotals`, `pipeStatus` — the two-level summation and the string
  status rule.
- `aggTotals_append` — aggregation over a concatenation is the sum of
  the aggregations (totals conserve across any partitioning of units).
- `pipe_success_iff` — the pipeline reports "success" **iff every unit
  reported zero errors**: aggregation neither hides nor invents errors.
- `agg_fst_filter_le`, `agg_snd_filter_le` — filtering out disabled
  units (ll. 141–144) can only lower the record/error totals.

### Stage 4 — bounded retry (`src/connectors/adapters/rest.py`, `src/notion_client.py`)
Source anchors: REST `RETRYABLE_STATUS = {429, 500, 502, 503, 504}`
rest.py:38–39; `_read_with_retry` rest.py:109–143 (attempt budget
l. 112; HTTPError branch ll. 118–130; URLError branch ll. 131–140);
Notion client `_request` notion_client.py:55–93, with the semantics
comment "`retry_attempts` is the number of *additional* tries after the
first" at ll. 44–45.

- `retryRun` — the loop over a sequence of per-try outcomes
  (`ok` / `retryable` / `fatal`); stops at the first decisive outcome;
  an all-retryable sequence ends in `retryable` (the re-raised error).
- `retryRun_tries_le`, `retryRun_bound` — tries ≤ budget; in the code's
  terms, ≤ `retry_attempts + 1`.
- `retryRun_fatal_first` — a non-retryable outcome is never retried:
  exactly one try.
- `retryRun_all_retryable` — an all-retryable budget is consumed
  exactly and fails.
- `retryRun_first_decisive` — after `k` retryable outcomes, the first
  decisive outcome is the result, at exactly try `k + 1`: retries
  cannot skip, reorder, or alter the decisive outcome.
- `retryRun_ok_mem` — a successful run implies an `ok` outcome
  actually occurred; the loop cannot manufacture success.

---

## Discrepancies and risks

1. **README vs. repo contents (scope).** The README says the agent
   logic lives in ClosedLoop and this repo is the dashboard layer.
   The code agrees — the in-repo agents are read-only analyzers. Any
   claim that this repo performs treasury operations, payment
   approval, or compliance gating is not supported by the code; the
   sync lifecycle modeled here is the entire control surface.

2. **PARTIAL is dead in `full_sync`** (proved,
   `fullSync_never_partial`). The derivation at base.py:247 consults
   `len(result.errors)`, but no statement inside the `try` block ever
   appends to `result.errors` — `_safe_extract` logs and converts
   errors into `None`/`[]` return values. The status exists in the
   enum and is produced by `sync_direct`, but the template method can
   never emit it.

3. **FAILED is dead in `sync_direct`** (proved,
   `syncDirect_never_failed_skipped`). The result is created with
   `status=FAILED` (pipeline.py:236) and then unconditionally
   overwritten at l. 269 with SUCCESS/PARTIAL. A `sync_direct` run in
   which every write failed is PARTIAL, never FAILED.

4. **Extraction failures are invisible** (proved counterexamples
   `swallowed_failure_invisible`,
   `all_extracts_failed_looks_skipped`,
   `absent_empty_indistinguishable`). `_safe_extract` (base.py:
   267–279) returns `[]` on any exception — identical to a genuinely
   empty dataset — and never records an error. Consequences: a
   connector with three of four extractors raising reports SUCCESS if
   the fourth returns data; a connector with all four raising reports
   SKIPPED ("No records extracted"), not FAILED. There is no signal
   distinguishing "ERP was empty" from "ERP call failed."

5. **`records_written` on the pipeline path is not a write count, and
   nothing is written.** `full_sync` sets
   `records_written = total_transformed` (base.py:240) despite writing
   nothing anywhere; the transformed records are local variables and
   are discarded. `SyncPipeline._sync_connector` (pipeline.py:312,
   318–326) then iterates the dataset counts and only *logs* "Writing
   N records to Notion," with a comment claiming "the entity's write
   method" handles the write — no entity method consumes this data
   (Entity/EntityRegistry expose only config and database maps). So
   `sync_entity`'s `total_records` sums relabeled transform counts,
   and the only code path that actually creates Notion pages is
   `sync_direct`. Knock-on: `SyncResult.success_rate`
   (base.py:109–114, written/extracted) is vacuously 100% on the
   `full_sync` path whenever anything was extracted, and 0.0 for a
   healthy SKIPPED run (proved shape: `fullSync_counts_conserve`).

6. **Unmapped dataset + normalizer = silent total drop, reported
   SUCCESS** (proved, `syncDirect_unmapped_drops_all`). When a
   normalizer is passed but the dataset has no registered mappings,
   `Normalizer.normalize` returns `(records, [])`
   (normalizer.py:147–149). `sync_direct` builds `valid_records` from
   the (empty) validation list (pipeline.py:244), so every record is
   dropped; `invalid_count` computes `0 - 0 = 0`, so not even the
   warning fires (ll. 247–248); the run ends SUCCESS with
   `records_written = 0`, and an audit record is appended whose
   checksum covers the empty list (ll. 272–285).

7. **All-invalid batches report SUCCESS** (proved,
   `syncDirect_all_invalid_success`). Validation failures are only a
   warning (pipeline.py:247–248); the status rule (l. 269) looks
   solely at write errors, of which there are none when nothing passes
   the gate. A batch in which 100% of records failed validation is
   indistinguishable in status from a perfect batch.

8. **Advertised delta detection is not implemented.** The module and
   class docstrings (pipeline.py:1–10, 66–76) claim "Delta detection
   (only sync changed records)" / "Delta detection via content
   hashing." No code path compares a record's hash against a previous
   sync to skip unchanged records; `_compute_checksum`
   (pipeline.py:352–355) is used only to stamp the `sync_direct` audit
   record. Every sync reprocesses and (in `sync_direct`) rewrites
   everything.

9. **Two status vocabularies, and pipeline-level failure is masked.**
   `sync_all_entities` reports the strings `"success"` / `"partial"` /
   `"error"` (pipeline.py:158–202), disjoint from `SyncStatus`. A run
   in which every connector FAILED surfaces as `"partial"` (their
   error lists make `total_errors > 0`), with no aggregate "failed"
   outcome; `sync_entity` result dicts carry no status field at all.
   Also, the `.get("total_records", 0)` / `.get("total_errors", 0)`
   defaults (ll. 191–192) make an error-dict result from `sync_entity`
   contribute silent zeros.

10. **Webhook signature gate is opt-in.** `WebhookHandler.do_POST`
    verifies the HMAC signature only `if WEBHOOK_SECRET`
    (webhook_server.py:41), and `_verify_signature` returns `True`
    when no secret is set (ll. 76–77). With the secret unset, any
    unsigned POST is accepted and triggers agent runs. (When a secret
    *is* set, verification uses `hmac.compare_digest`, l. 84 — fine.)
    Separately, the `db_agents` dict in `_handle_page_updated`
    (ll. 113–118) is dead code: it maps every key to the same page id
    and is never consulted.

11. **Retry count naming is an off-by-one trap; one dead code path.**
    `retry_attempts` means *additional* tries, so the default 3 yields
    4 total tries — documented only in notion_client.py:44–45; the
    `ConnectorConfig` field (base.py, `ConnectorConfig` ll. 44–88)
    carries no such note. The two implementations are behaviorally
    consistent (bound proved as `retryRun_bound`). The post-loop
    `raise` at the end of rest.py's `_read_with_retry` (ll. 141–143)
    is unreachable: every iteration returns, continues, or raises, and
    the last iteration cannot `continue`.

12. **Lifecycle asymmetry.** `BaseConnector`'s documented lifecycle
    ends with `disconnect()` (base.py:148–156), but `full_sync` never
    disconnects; only `SyncPipeline._sync_connector` does
    (pipeline.py:328). Standalone `full_sync` use leaks the session,
    and `full_sync` also trusts a stale `_connected = True` flag
    without re-verification — combined with Finding 4, a dead session
    presents as SKIPPED/SUCCESS.

13. **`batch_size = 0` crashes `sync_direct` without a result.**
    `range(0, len(valid_records), batch_size)` (pipeline.py:257)
    raises `ValueError` for `batch_size = 0`; `sync_direct` has no
    guard and no `try` around the write loop, so the exception
    propagates and neither a `SyncResult` nor an audit record is
    produced. (Config default is 100; the model assumes
    `batch_size ≥ 1`.)

## Model assumptions (explicit)

- The four fixed datasets of `full_sync` are generalized to an
  arbitrary list of outcomes; all Stage-1 theorems are list-generic,
  so they apply to the code's 4-element case.
- Transform is modeled as the identity, which is the as-shipped
  behavior (base `_transform_records`, base.py:281–287; no override
  exists in this repo). A future override that drops records would
  weaken `fullSync_counts_conserve` to `transformed ≤ extracted`; the
  status theorems do not depend on the transform.
- Money is not modeled: the sync core moves record *counts*, not
  amounts, so "money conservation" reduces here to the counting
  conservation laws proved in Stages 1–3. The dollar figures in the
  agents' reports are computed from Notion data by read-only formulas
  and are outside the sync core.
- Timestamps, durations, and log output are abstracted away; write
  outcomes are modeled as one independent `Bool` per gated record,
  matching the per-call `try` in pipeline.py:259–265.
