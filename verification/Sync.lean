/-
  CFO Command Center — Lean 4 model of the sync control core.

  The repository is, by its own README, the Notion dashboard layer for
  ClosedLoop: the in-repo "agents" are read-only analyzers over Notion
  data, and there is no treasury-approval, payment-execution, or
  compliance state machine in this codebase (see NOTES.md).  The one
  genuine control core is the ERP -> Notion **sync lifecycle**:

    * `BaseConnector.full_sync`        src/connectors/base.py:196-266
    * `SyncPipeline.sync_direct`       src/connectors/pipeline.py:214-278
    * `SyncPipeline.sync_all_entities` src/connectors/pipeline.py:158-202
    * the bounded retry loop shared by src/connectors/adapters/rest.py:109-140
      and src/notion_client.py:55-93.

  This file models that lifecycle as pure functions over counts and
  per-stage outcomes, and proves: the status each path can and cannot
  produce, the counting-conservation laws, the validation-gate bound
  (nothing is written that did not pass the gate), the aggregation law
  for the multi-entity pipeline, and the retry bound.  Several
  theorems are *counterexamples by computation* (`rfl` proofs) that
  formalize silent-failure modes found in the code; they are labelled
  as such.

  Core library only; no Mathlib; no sorry/admit/custom axioms.
  (The status constructor is spelled `partial_` because `partial` is a
  Lean keyword; it is `SyncStatus.PARTIAL` in the Python source.)
-/

namespace CfoSync

/-! ## Small Nat-list helpers (kept local so the file needs only core Lean) -/

/-- Sum of a list of naturals. -/
def sumN : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumN xs

theorem sumN_append (a b : List Nat) : sumN (a ++ b) = sumN a + sumN b := by
  induction a with
  | nil => simp [sumN]
  | cons x xs ih => simp only [List.cons_append, sumN, ih, Nat.add_assoc]

theorem sumN_eq_zero_iff {l : List Nat} : sumN l = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp [sumN]
  | cons x xs ih =>
      rw [sumN, Nat.add_eq_zero_iff, ih]
      constructor
      · rintro ⟨hx, hxs⟩ y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hxs y hy
      · intro h
        exact ⟨h x List.mem_cons_self,
               fun y hy => h y (List.mem_cons_of_mem x hy)⟩

/-! ## The sync status vocabulary (base.py:36-41) -/

inductive SyncStatus where
  | success
  | partial_
  | failed
  | skipped
deriving DecidableEq, Repr

/-- The four counters a sync reports (base.py:91-107, pipeline.py `SyncResult`). -/
structure SyncCounts where
  status : SyncStatus
  extracted : Nat
  transformed : Nat
  written : Nat
deriving DecidableEq, Repr

/-! ## Stage 1: `full_sync` (base.py:196-266)

  Control flow of the template method:
    1. the result is created with status FAILED (base.py:205);
    2. if not connected and `connect()` fails, return FAILED at once
       (base.py:207-212) -- the connect gate;
    3. otherwise extract the four datasets through `_safe_extract`
       (base.py:215-221), count and transform them (base.py:223-244);
    4. the status is then *derived* from the totals (base.py:246-249);
    5. an exception escaping the counting loop (only possible from a
       `_transform_records` override: `_safe_extract` swallows its own
       exceptions, base.py:267-279) leaves the initial FAILED in place
       and the counters at 0, because the counter assignments sit after
       the loop (base.py:251-253, 238-244).

  An `Extract` value is what the counting loop can observe about one
  dataset.  Crucially, `_safe_extract` returns `[]` both for a genuinely
  empty dataset and for one whose extractor raised (base.py:276-279);
  the loop cannot distinguish the two, and neither can this model --
  that is the point of `swallowed_failure_invisible` below. -/

inductive Extract where
  | absent : Extract        -- `_safe_extract` returned `None` (NotImplementedError; base.py:273-275)
  | empty : Extract         -- returned `[]`: genuinely empty OR a swallowed exception
  | data : Nat → Extract    -- returned that many records
deriving DecidableEq, Repr

def Extract.count : Extract → Nat
  | .absent => 0
  | .empty => 0
  | .data n => n

def totalExtracted (ds : List Extract) : Nat := sumN (ds.map Extract.count)

/-- The status formula of base.py:246-249, with the error count left
    explicit so its reachability can be analysed. -/
def deriveStatus (total errors : Nat) : SyncStatus :=
  if total = 0 then .skipped
  else if errors = 0 then .success
  else .partial_

theorem deriveStatus_of_pos (t : Nat) (ht : t ≠ 0) : deriveStatus t 0 = .success := by
  simp [deriveStatus, ht]

theorem deriveStatus_of_zero (t : Nat) (ht : t = 0) : deriveStatus t 0 = .skipped := by
  simp [deriveStatus, ht]

theorem deriveStatus_errors_zero_ne_partial (t : Nat) :
    deriveStatus t 0 ≠ .partial_ := by
  by_cases ht : t = 0
  · rw [deriveStatus_of_zero t ht]; exact SyncStatus.noConfusion
  · rw [deriveStatus_of_pos t ht]; exact SyncStatus.noConfusion

/-- The three ways a `full_sync` call can end. -/
inductive FullSyncOutcome where
  | connectFailed : FullSyncOutcome
  | crashed : FullSyncOutcome
  | completed : List Extract → FullSyncOutcome

/-- The `completed` branch of `full_sync`.  The error count at the
    derivation point is 0: nothing inside the `try` block of
    base.py:214-250 ever appends to `result.errors` (`_safe_extract`
    logs and returns `None`/`[]` instead), and with the base
    `_transform_records` (identity, base.py:281-287; no adapter in this
    repo overrides it) transformed = extracted and the code *sets*
    `records_written = total_transformed` (base.py:240). -/
def fullSyncRun (ds : List Extract) : SyncCounts :=
  ⟨deriveStatus (totalExtracted ds) 0, totalExtracted ds, totalExtracted ds,
   totalExtracted ds⟩

def fullSync : FullSyncOutcome → SyncCounts
  | .connectFailed => ⟨.failed, 0, 0, 0⟩
  | .crashed => ⟨.failed, 0, 0, 0⟩
  | .completed ds => fullSyncRun ds

theorem fullSync_completed (ds : List Extract) :
    fullSync (.completed ds) = fullSyncRun ds := rfl

/-- PARTIAL is unreachable from `full_sync`: the only branch that could
    produce it needs a non-empty error list at base.py:247, and the
    error list is provably empty there.  (PARTIAL is produced only by
    `sync_direct`, pipeline.py:269.) -/
theorem fullSync_never_partial (o : FullSyncOutcome) : (fullSync o).status ≠ .partial_ := by
  cases o with
  | connectFailed => exact SyncStatus.noConfusion
  | crashed => exact SyncStatus.noConfusion
  | completed ds =>
      rw [fullSync_completed]
      exact deriveStatus_errors_zero_ne_partial _

/-- FAILED is the initial status, and it survives exactly when the run
    never reaches the derivation point: connect gate or crash. -/
theorem fullSync_failed_iff (o : FullSyncOutcome) :
    (fullSync o).status = .failed ↔ o = .connectFailed ∨ o = .crashed := by
  cases o with
  | connectFailed => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | crashed => exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
  | completed ds =>
      constructor
      · intro h
        rw [fullSync_completed] at h
        exfalso
        by_cases ht : totalExtracted ds = 0
        · have hs : (fullSyncRun ds).status = .skipped := deriveStatus_of_zero _ ht
          rw [hs] at h; exact SyncStatus.noConfusion h
        · have hs : (fullSyncRun ds).status = .success := deriveStatus_of_pos _ ht
          rw [hs] at h; exact SyncStatus.noConfusion h
      · rintro (h | h) <;> cases h

/-- Counting conservation for `full_sync` (with the as-shipped identity
    transform): written = transformed = extracted.  Note this also makes
    `SyncResult.success_rate` (base.py:109-114) vacuously 100% on this
    path whenever anything was extracted. -/
theorem fullSync_counts_conserve (ds : List Extract) :
    (fullSync (.completed ds)).extracted = totalExtracted ds ∧
    (fullSync (.completed ds)).transformed = totalExtracted ds ∧
    (fullSync (.completed ds)).written = totalExtracted ds :=
  ⟨rfl, rfl, rfl⟩

theorem fullSync_success_iff (ds : List Extract) :
    (fullSync (.completed ds)).status = .success ↔ 0 < totalExtracted ds := by
  rw [fullSync_completed]
  constructor
  · intro h
    by_cases ht : totalExtracted ds = 0
    · exfalso
      have hs : (fullSyncRun ds).status = .skipped := deriveStatus_of_zero _ ht
      rw [hs] at h; exact SyncStatus.noConfusion h
    · omega
  · intro h
    have hs : (fullSyncRun ds).status = .success :=
      deriveStatus_of_pos _ (by omega)
    exact hs

theorem fullSync_skipped_iff (ds : List Extract) :
    (fullSync (.completed ds)).status = .skipped ↔ totalExtracted ds = 0 := by
  rw [fullSync_completed]
  constructor
  · intro h
    by_cases ht : totalExtracted ds = 0
    · exact ht
    · exfalso
      have hs : (fullSyncRun ds).status = .success := deriveStatus_of_pos _ ht
      rw [hs] at h; exact SyncStatus.noConfusion h
  · intro h
    have hs : (fullSyncRun ds).status = .skipped := deriveStatus_of_zero _ h
    exact hs

/-- COUNTEREXAMPLE (by computation): one dataset's extractor raised
    (swallowed to `[]` by `_safe_extract`) and another returned 3
    records.  `full_sync` reports SUCCESS -- the failure is invisible.
    (base.py:267-279 + 246-249.) -/
theorem swallowed_failure_invisible :
    fullSync (.completed [.empty, .data 3]) = ⟨.success, 3, 3, 3⟩ := rfl

/-- COUNTEREXAMPLE (by computation): *every* extractor raised.  The run
    is reported SKIPPED ("No records extracted from any data source"),
    not FAILED. -/
theorem all_extracts_failed_looks_skipped :
    fullSync (.completed [.empty, .empty, .empty, .empty]) = ⟨.skipped, 0, 0, 0⟩ := rfl

/-- `absent` (not implemented) and `empty` (empty or failed) are
    indistinguishable to the counting loop. -/
theorem absent_empty_indistinguishable (ds : List Extract) :
    fullSync (.completed (.absent :: ds)) = fullSync (.completed (.empty :: ds)) := rfl

/-! ## Stage 2: `sync_direct` (pipeline.py:214-278)

  Control flow:
    1. result created with status FAILED and `records_extracted` set to
       the input size (pipeline.py:236-238);
    2. the validation gate: with a normalizer, only records whose
       `ValidationResult.is_valid` holds pass (pipeline.py:244); without
       one, everything passes (pipeline.py:251-253);
    3. gated records are written to Notion one by one; each failed write
       appends exactly one error (pipeline.py:255-265);
    4. the status is then *unconditionally* overwritten:
       SUCCESS iff no write errors, else PARTIAL (pipeline.py:269).
    5. an audit record is appended (pipeline.py:272-285).

  The gate has three modes.  `mapped v`: the normalizer has mappings
  for the dataset and `v` of the records validated (normalizer.py:155-158
  produces exactly one validation per record, so `v ≤ n`).
  `unmapped`: the dataset has no mappings, and `Normalizer.normalize`
  returns `(records, [])` (normalizer.py:147-149) -- the gate's filter
  over the empty validation list passes *nothing*. -/

inductive GateMode where
  | passthrough : GateMode
  | mapped : Nat → GateMode
  | unmapped : GateMode

/-- Records that pass the validation gate. -/
def gateValid : GateMode → Nat → Nat
  | .passthrough, n => n
  | .mapped v, _ => v
  | .unmapped, _ => 0

/-- Number of `true`s / `false`s in a per-record write-outcome list. -/
def countTrue : List Bool → Nat
  | [] => 0
  | true :: xs => countTrue xs + 1
  | false :: xs => countTrue xs

def countFalse : List Bool → Nat
  | [] => 0
  | true :: xs => countFalse xs
  | false :: xs => countFalse xs + 1

theorem countTrue_add_countFalse (l : List Bool) :
    countTrue l + countFalse l = l.length := by
  induction l with
  | nil => rfl
  | cons b xs ih => cases b <;> simp only [countTrue, countFalse, List.length_cons] <;> omega

/-- `sync_direct` as a function of the gate mode, the input size, and
    the per-record write outcomes (one `Bool` per gated record:
    `true` = page created, `false` = write raised and was logged). -/
def syncDirect (mode : GateMode) (n : Nat) (writes : List Bool) : SyncCounts :=
  let valid := gateValid mode n
  let written := countTrue writes
  let errs := countFalse writes
  ⟨if errs = 0 then .success else .partial_, n, valid, written⟩

theorem syncDirect_status (mode : GateMode) (n : Nat) (writes : List Bool) :
    (syncDirect mode n writes).status =
      if countFalse writes = 0 then .success else .partial_ := rfl

/-- FAILED and SKIPPED are unreachable from `sync_direct`: the initial
    FAILED (pipeline.py:236) is unconditionally overwritten at
    pipeline.py:269.  Mirror image of `fullSync_never_partial`. -/
theorem syncDirect_never_failed_skipped (mode : GateMode) (n : Nat) (writes : List Bool) :
    (syncDirect mode n writes).status ≠ .failed ∧
    (syncDirect mode n writes).status ≠ .skipped := by
  rw [syncDirect_status]
  split <;> exact ⟨SyncStatus.noConfusion, SyncStatus.noConfusion⟩

theorem syncDirect_success_iff (mode : GateMode) (n : Nat) (writes : List Bool) :
    (syncDirect mode n writes).status = .success ↔ countFalse writes = 0 := by
  rw [syncDirect_status]
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun hs => absurd hs (by decide), fun h0 => absurd h0 h⟩

/-- Counting conservation for `sync_direct`: assuming one write outcome
    per gated record (as the loop at pipeline.py:255-265 produces),
    written + write-errors = transformed, so in particular nothing is
    written that did not pass the gate: written ≤ gateValid. -/
theorem syncDirect_conservation (mode : GateMode) (n : Nat) (writes : List Bool)
    (h : writes.length = gateValid mode n) :
    (syncDirect mode n writes).written + countFalse writes = gateValid mode n ∧
    (syncDirect mode n writes).written ≤ gateValid mode n := by
  have key := countTrue_add_countFalse writes
  constructor
  · show countTrue writes + countFalse writes = gateValid mode n
    rw [key, h]
  · show countTrue writes ≤ gateValid mode n
    omega

/-- COUNTEREXAMPLE (by computation): in mapped mode with *every* record
    invalid, the gate passes nothing, nothing is written, and the run
    still reports SUCCESS -- invalid records only ever produce a
    warning (pipeline.py:247-248), never an error. -/
theorem syncDirect_all_invalid_success (n : Nat) :
    syncDirect (.mapped 0) n [] = ⟨.success, n, 0, 0⟩ := rfl

/-- COUNTEREXAMPLE (by computation): a normalizer is supplied but the
    dataset has no registered mappings.  `normalize` returns an empty
    validation list (normalizer.py:149), the gate therefore passes zero
    records, the invalid-count warning computes 0 - 0 = 0 and does not
    fire either (pipeline.py:245-248), and the run reports SUCCESS with
    all `n` input records silently dropped. -/
theorem syncDirect_unmapped_drops_all (n : Nat) :
    syncDirect .unmapped n [] = ⟨.success, n, 0, 0⟩ := rfl

/-! ## Stage 3: pipeline aggregation (pipeline.py:116-202)

  `sync_entity` sums the per-connector `records_written` and error
  counts over the entity's *enabled* connectors (pipeline.py:141-148);
  `sync_all_entities` sums those per-entity totals again and reports
  the string status "success" iff the grand total of errors is 0, else
  "partial" (pipeline.py:158-202).  (Note the second status vocabulary:
  strings, not `SyncStatus`, and no "failed" outcome at this level.) -/

/-- (records, errors) pairs, one per synced unit. -/
def aggTotals (rs : List (Nat × Nat)) : Nat × Nat :=
  (sumN (rs.map Prod.fst), sumN (rs.map Prod.snd))

def pipeStatus (totalErrors : Nat) : String :=
  if totalErrors = 0 then "success" else "partial"

theorem aggTotals_append (a b : List (Nat × Nat)) :
    aggTotals (a ++ b) =
      ((aggTotals a).1 + (aggTotals b).1, (aggTotals a).2 + (aggTotals b).2) := by
  simp only [aggTotals, List.map_append, sumN_append]

/-- The pipeline reports "success" iff every unit reported zero errors:
    aggregation neither hides nor invents errors. -/
theorem pipe_success_iff (rs : List (Nat × Nat)) :
    pipeStatus (aggTotals rs).2 = "success" ↔ ∀ r ∈ rs, r.2 = 0 := by
  have hsum : (aggTotals rs).2 = 0 ↔ ∀ r ∈ rs, r.2 = 0 := by
    constructor
    · intro h r hr
      exact (sumN_eq_zero_iff).mp h r.2 (List.mem_map_of_mem hr)
    · intro h
      apply (sumN_eq_zero_iff).mpr
      intro x hx
      rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
      exact h r hr
  by_cases he : (aggTotals rs).2 = 0
  · have hstat : pipeStatus (aggTotals rs).2 = "success" := by
      unfold pipeStatus; rw [ite_eq_left he]
    rw [hstat]; exact ⟨fun _ => hsum.mp he, fun _ => rfl⟩
  · have hstat : pipeStatus (aggTotals rs).2 = "partial" := by
      unfold pipeStatus; rw [ite_eq_right he]
    rw [hstat]
    exact ⟨fun hs => False.elim ((by decide : ("partial" : String) ≠ "success") hs),
           fun h => absurd (hsum.mpr h) he⟩

/-- Disabled units contribute nothing: filtering units out (the
    enabled-checks at pipeline.py:141-144 and 176-178) can only lower
    the aggregated record total, never raise it. -/
theorem agg_fst_filter_le (p : (Nat × Nat) → Bool) (rs : List (Nat × Nat)) :
    sumN ((rs.filter p).map Prod.fst) ≤ sumN (rs.map Prod.fst) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
      by_cases h : p r
      · simp only [List.filter_cons_of_pos h, List.map_cons, sumN]
        exact Nat.add_le_add_left ih _
      · simp only [List.filter_cons_of_neg h, List.map_cons, sumN]
        omega

/-- Same for the error total: skipping disabled units never invents
    errors either. -/
theorem agg_snd_filter_le (p : (Nat × Nat) → Bool) (rs : List (Nat × Nat)) :
    sumN ((rs.filter p).map Prod.snd) ≤ sumN (rs.map Prod.snd) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
      by_cases h : p r
      · simp only [List.filter_cons_of_pos h, List.map_cons, sumN]
        exact Nat.add_le_add_left ih _
      · simp only [List.filter_cons_of_neg h, List.map_cons, sumN]
        omega

/-! ## Stage 4: the bounded retry loop (rest.py:109-140, notion_client.py:55-93)

  Both HTTP helpers run the same loop: try the request; on a retryable
  status (429/5xx) or a transport error, sleep and retry while
  `attempt < attempts`; otherwise return or re-raise.  `retry_attempts`
  is the number of *additional* tries after the first
  (notion_client.py:44-45), so the loop body runs at most
  `attempts + 1` times.  Here the sequence of per-try outcomes is
  modelled directly; the loop stops at the first decisive outcome, and
  an all-retryable sequence ends in `retryable`, standing for the
  re-raised last exception. -/

inductive Attempt where
  | ok : Attempt
  | retryable : Attempt
  | fatal : Attempt
deriving DecidableEq, Repr

def retryRun : List Attempt → Attempt × Nat
  | [] => (.retryable, 0)
  | .ok :: _ => (.ok, 1)
  | .fatal :: _ => (.fatal, 1)
  | .retryable :: xs => let r := retryRun xs; (r.1, r.2 + 1)

/-- The loop never tries more often than the outcome budget allows. -/
theorem retryRun_tries_le (l : List Attempt) : (retryRun l).2 ≤ l.length := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
      cases a <;> simp only [retryRun, List.length_cons] <;> omega

/-- Corollary in the code's own terms: with `attempts` additional tries
    configured, at most `attempts + 1` tries happen. -/
theorem retryRun_bound (attempts : Nat) (l : List Attempt) (h : l.length = attempts + 1) :
    (retryRun l).2 ≤ attempts + 1 := by
  rw [← h]; exact retryRun_tries_le l

/-- A fatal outcome stops the loop after exactly one try: non-retryable
    errors are never retried (rest.py:119-130). -/
theorem retryRun_fatal_first (xs : List Attempt) :
    retryRun (.fatal :: xs) = (.fatal, 1) := rfl

/-- If every try is retryable, the loop consumes the whole budget and
    fails: exactly `l.length` tries. -/
theorem retryRun_all_retryable (l : List Attempt) (h : ∀ a ∈ l, a = .retryable) :
    retryRun l = (.retryable, l.length) := by
  induction l with
  | nil => rfl
  | cons a xs ih =>
      have ha : a = .retryable := h a List.mem_cons_self
      have hxs : ∀ b ∈ xs, b = .retryable :=
        fun b hb => h b (List.mem_cons_of_mem a hb)
      have step : retryRun (.retryable :: xs) = ((retryRun xs).1, (retryRun xs).2 + 1) := rfl
      rw [ha, step, ih hxs]
      rfl

/-- After `k` retryable outcomes, the first decisive outcome `x` is the
    loop's result, reached after exactly `k + 1` tries: retries cannot
    skip, reorder, or alter the decisive outcome. -/
theorem retryRun_first_decisive (k : Nat) (x : Attempt) (rest : List Attempt)
    (hx : x ≠ .retryable) :
    retryRun (List.replicate k .retryable ++ x :: rest) = (x, k + 1) := by
  induction k with
  | zero =>
      cases x with
      | ok => rfl
      | fatal => rfl
      | retryable => exact absurd rfl hx
  | succ k ih =>
      have step : retryRun (.retryable :: (List.replicate k .retryable ++ x :: rest)) =
          ((retryRun (List.replicate k .retryable ++ x :: rest)).1,
           (retryRun (List.replicate k .retryable ++ x :: rest)).2 + 1) := rfl
      rw [List.replicate_succ, List.cons_append, step, ih]

/-- A successful run means an `ok` outcome actually occurred: the loop
    cannot manufacture success. -/
theorem retryRun_ok_mem (l : List Attempt) (h : (retryRun l).1 = .ok) : .ok ∈ l := by
  induction l with
  | nil => simp [retryRun] at h
  | cons a xs ih =>
      cases a with
      | ok => exact List.mem_cons_self
      | fatal => simp [retryRun] at h
      | retryable =>
          have h' : (retryRun xs).1 = .ok := h
          exact List.mem_cons_of_mem _ (ih h')

end CfoSync
