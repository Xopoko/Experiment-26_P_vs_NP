import Paperproof
import PvNP.Core.Defs
import PvNP.Core.Graph


namespace PvNP

-- Q43 work-in-progress Lean proofs (real code, not doc-comments).
-- Q43.S139-polym-avoids-thm41-branch: IsPoly is monotone under pointwise upper bounds.
theorem Q43_IsPoly_of_le {t s : Nat -> Nat} (hpoly : IsPoly t) (hle : ∀ n, s n <= t n) :
    IsPoly s := by
  rcases hpoly with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro n
  exact Nat.le_trans (hle n) (hk n)

-- Q43.S140-polym-below-threshold: explicit polynomial bounds imply IsPoly.
theorem Q43_IsPoly_of_le_pow {s : Nat -> Nat} (k : Nat) (hle : ∀ n, s n <= n ^ k) :
    IsPoly s := by
  refine ⟨k, ?_⟩
  intro n
  exact Nat.le_trans (hle n) (Nat.le_succ _)

-- Q43.S170-explicit-c1c2-thm41: package explicit constants for Thm. 4.1.
def Q43_thm41_c2 (A : Nat) : Nat := 8 * A * 152

def Q43_thm41_c1 (A : Nat) : Nat := 16 * 152 * Q43_thm41_c2 A

-- Q43.S171-check-thm41-threshold: exp base 2 for HR'22 conventions.
def Q43_exp2 (x : Nat) : Nat := 2 ^ x

-- Q43.S172-exp2-consistency: generic exp base for clarity.
def Q43_exp_base (b x : Nat) : Nat := b ^ x

theorem Q43_exp2_eq_base (x : Nat) : Q43_exp2 x = Q43_exp_base 2 x := by
  rfl

-- Q43.S173-exp2-c1c2-rescale: constants already in base-2 conventions.
def Q43_thm41_c2_exp2 (A : Nat) : Nat := Q43_thm41_c2 A

def Q43_thm41_c1_exp2 (A : Nat) : Nat := Q43_thm41_c1 A

theorem Q43_thm41_c1_exp2_eq (A : Nat) : Q43_thm41_c1_exp2 A = Q43_thm41_c1 A := by
  rfl

theorem Q43_thm41_c2_exp2_eq (A : Nat) : Q43_thm41_c2_exp2 A = Q43_thm41_c2 A := by
  rfl

-- Q43.S174-exp2-threshold-sweep: base-2 large-M threshold helper.
def Q43_largeM_threshold (n alpha : Nat) : Nat := Q43_exp2 (n ^ alpha)

theorem Q43_largeM_threshold_def (n alpha : Nat) :
    Q43_largeM_threshold n alpha = Q43_exp2 (n ^ alpha) := by
  rfl

-- Q43.S175-exp2-quote-annotation: exp in source interpreted as base 2.
-- Q43.S176-exp2-quote-sweep: record that exp quotes are annotated with base 2.
-- Q43.S177-exp2-quote-scan-core: base-2 note in core citations.
-- Q43.S178-exp2-quote-scan-remaining: base-2 notes in core/summary.
-- Q43.S179-exp2-quote-scan-analytic: base-e notes in analytic steps.

-- Q43.S196-flat-eval-size-metric-formalize: size metrics for line-based proofs.
def Q43_lineSize {α : Type} (line : List α) : Nat :=
  line.length

def Q43_proofSize {α : Type} : List (List α) -> Nat
  | [] => 0
  | line :: rest => Q43_lineSize line + Q43_proofSize rest

def Q43_lineCount {α : Type} (proof : List (List α)) : Nat :=
  proof.length

def Q43_lineMax {α : Type} : List (List α) -> Nat
  | [] => 0
  | line :: rest => max (Q43_lineSize line) (Q43_lineMax rest)

theorem Q43_lineSize_le_proofSize {α : Type} {line : List α} {proof : List (List α)} :
    line ∈ proof -> Q43_lineSize line <= Q43_proofSize proof := by
  intro hmem
  induction proof with
  | nil =>
      cases hmem
  | cons hd tl ih =>
      simp [Q43_proofSize, Q43_lineSize] at hmem ⊢
      cases hmem with
      | inl h =>
          subst h
          exact Nat.le_add_right _ _
      | inr h =>
          have h' := ih h
          exact Nat.le_trans h' (Nat.le_add_left _ _)

-- Q43.S197-flat-eval-size-metric-tparam: t parameter from line size.
def Q43_tParam (M : Nat) : Nat :=
  Nat.log2 M

theorem Q43_tParam_le (M : Nat) : Q43_tParam M <= M := by
  simpa [Q43_tParam] using (Nat.log2_le_self M)

-- Q43.S198-flat-eval-tparam-usage: connect t=log2 M to proof size.
theorem Q43_lineMax_le_proofSize {α : Type} (proof : List (List α)) :
    Q43_lineMax proof <= Q43_proofSize proof := by
  induction proof with
  | nil =>
      simp [Q43_lineMax, Q43_proofSize]
  | cons hd tl ih =>
      have h1 : Q43_lineSize hd <= Q43_lineSize hd + Q43_proofSize tl :=
        Nat.le_add_right _ _
      have h2 : Q43_lineMax tl <= Q43_lineSize hd + Q43_proofSize tl :=
        Nat.le_trans ih (Nat.le_add_left _ _)
      exact (Nat.max_le).2 ⟨h1, h2⟩

theorem Q43_tParam_le_proofSize {α : Type} (proof : List (List α)) :
    Q43_tParam (Q43_lineMax proof) <= Q43_proofSize proof := by
  exact Nat.le_trans (Q43_tParam_le (Q43_lineMax proof)) (Q43_lineMax_le_proofSize proof)

-- Q43.S199-flat-eval-tparam-ologs: log2 monotone bound for proof size.
theorem Q43_log2_mono {a b : Nat} (h : a <= b) : Nat.log2 a <= Nat.log2 b := by
  by_cases hb : b = 0
  · have ha : a = 0 := Nat.eq_zero_of_le_zero (by simpa [hb] using h)
    simp [ha, hb]
  · by_cases ha : a = 0
    · simp [ha]
    · have hpow_le_a : 2 ^ Nat.log2 a <= a := Nat.log2_self_le ha
      have hpow_le_b : 2 ^ Nat.log2 a <= b := Nat.le_trans hpow_le_a h
      exact (Nat.le_log2 hb).2 hpow_le_b

theorem Q43_tParam_le_log2_proofSize {α : Type} (proof : List (List α)) :
    Q43_tParam (Q43_lineMax proof) <= Nat.log2 (Q43_proofSize proof) := by
  simpa [Q43_tParam] using (Q43_log2_mono (Q43_lineMax_le_proofSize proof))

-- Q43.S202-flat-eval-hr-compat-polylog: unfolded depth parameter t'=(2s+1)t.
def Q43_tPrime (s t : Nat -> Nat) : Nat -> Nat :=
  fun n => (2 * s n + 1) * t n

theorem Q43_tPrime_ge (s t : Nat -> Nat) (n : Nat) :
    t n <= Q43_tPrime s t n := by
  have h : 1 <= 2 * s n + 1 := by
    exact Nat.succ_le_succ (Nat.zero_le _)
  calc
    t n = 1 * t n := by
      simp
    _ <= (2 * s n + 1) * t n := by
      exact Nat.mul_le_mul_right _ h

-- Q43.S203-flat-eval-hr-param-check: HR threshold predicate for t' and s.
def Q43_hrThreshold (n t s : Nat) : Prop :=
  t <= n / 16 ∧ s <= n / 32

theorem Q43_hrThreshold_of_le {n t s : Nat} (ht : t <= n / 16) (hs : s <= n / 32) :
    Q43_hrThreshold n t s := by
  exact And.intro ht hs

-- Q43.S204-flat-eval-hr-neta-threshold: one-step HR recursion placeholder.
def Q43_hrDenom (A t logc : Nat) : Nat := A * t * logc

def Q43_neta_step (n A t logc : Nat) : Nat :=
  n / Q43_hrDenom A t logc

theorem Q43_neta_step_le (n A t logc : Nat) :
    Q43_neta_step n A t logc <= n := by
  simpa [Q43_neta_step, Q43_hrDenom] using (Nat.div_le_self n (A * t * logc))

def Q43_neta_iter (n A t logc : Nat) : Nat -> Nat
  | 0 => n
  | Nat.succ k => Q43_neta_step (Q43_neta_iter n A t logc k) A t logc

theorem Q43_neta_iter_le (n A t logc : Nat) : ∀ k, Q43_neta_iter n A t logc k <= n := by
  intro k
  induction k with
  | zero =>
      simp [Q43_neta_iter]
  | succ k ih =>
      simp [Q43_neta_iter]
      have hstep :
          Q43_neta_step (Q43_neta_iter n A t logc k) A t logc
            <= Q43_neta_iter n A t logc k := by
        exact Q43_neta_step_le _ _ _ _
      exact Nat.le_trans hstep ih

-- Q43.S206-flat-eval-hr-neta-range: eta-range predicate for HR recursion.
def Q43_etaRange (n eta : Nat) : Prop :=
  eta <= Nat.log2 n

theorem Q43_etaRange_mono {n m eta : Nat} (h : n <= m) (hEta : Q43_etaRange n eta) :
    Q43_etaRange m eta := by
  unfold Q43_etaRange at *
  exact Nat.le_trans hEta (Q43_log2_mono h)

-- Q43.S207-flat-eval-hr-level-count: level count is the proof depth parameter d.
def Q43_levelCount (d : Nat) : Nat := d

theorem Q43_levelCount_le {d n : Nat} (h : d <= n) : Q43_levelCount d <= n := by
  simpa [Q43_levelCount] using h

-- Q43.S208-flat-eval-hr-depth-range: strict eta-range bound from HR recursion.
def Q43_etaRangeStrict (n a c1 eta : Nat) : Prop :=
  eta <= Nat.log2 n / (2 * (a + c1 + 1) * Nat.log2 (Nat.log2 n))

theorem Q43_etaRange_of_strict {n a c1 eta : Nat} (h : Q43_etaRangeStrict n a c1 eta) :
    Q43_etaRange n eta := by
  unfold Q43_etaRangeStrict at h
  unfold Q43_etaRange
  have hdiv :
      Nat.log2 n / (2 * (a + c1 + 1) * Nat.log2 (Nat.log2 n)) <= Nat.log2 n := by
    simpa using
      (Nat.div_le_self (Nat.log2 n) (2 * (a + c1 + 1) * Nat.log2 (Nat.log2 n)))
  exact Nat.le_trans h hdiv

-- Q43.S209-flat-eval-hr-depth-range-constants: placeholders for implicit HR constants.
structure Q43_switchingConstants where
  A : Nat
  C : Nat
  n0 : Nat

theorem Q43_add_16_mul (s : Nat) : s + 16 * s = 17 * s := by
  calc
    s + 16 * s = 1 * s + 16 * s := by
      simp
    _ = (1 + 16) * s := by
      simpa using (Nat.add_mul 1 16 s).symm
    _ = 17 * s := by
      have h : (1 + 16) = 17 := by decide
      simp [h]

theorem Q43_add_16_mul_add (s : Nat) : s + 16 * s + s = 18 * s := by
  calc
    s + 16 * s + s = (s + 16 * s) + s := by
      simp [Nat.add_assoc]
    _ = 17 * s + s := by
      simp [Q43_add_16_mul]
    _ = 18 * s := by
      have h : (17 + 1) = 18 := by decide
      simpa [h] using (Nat.add_mul 17 1 s).symm

-- Q43.S210-flat-eval-hr-depth-range-constants-recount: coarse explicit bounds from Lemma 6.9 algebra.
theorem Q43_Lemma69_A3_bound {s t : Nat} (ht : t <= s) :
    s + 16 * t + s / 4 <= 18 * s := by
  have h1 : 16 * t <= 16 * s := Nat.mul_le_mul_left 16 ht
  have h2 : s / 4 <= s := Nat.div_le_self s 4
  have h3 : s + 16 * t + s / 4 <= s + 16 * s + s := by
    exact Nat.add_le_add (Nat.add_le_add_left h1 s) h2
  exact Nat.le_trans h3 (Nat.le_of_eq (Q43_add_16_mul_add s))

theorem Q43_Lemma69_A4_bound {s t : Nat} (ht : t <= s) :
    s / 4 + 16 * t <= 17 * s := by
  have h1 : 16 * t <= 16 * s := Nat.mul_le_mul_left 16 ht
  have h2 : s / 4 <= s := Nat.div_le_self s 4
  have h3 : s / 4 + 16 * t <= s + 16 * s := by
    exact Nat.add_le_add h2 h1
  exact Nat.le_trans h3 (Nat.le_of_eq (Q43_add_16_mul s))

-- Q43.S211-flat-eval-hr-depth-range-constants-a1a2: combine A1/A2 with explicit A3/A4 bounds.
theorem Q43_Lemma69_A12_bound {s t A1 A2 : Nat} (ht : t <= s) :
    9 * (s / 4 + 16 * t) + A1 * (s / 4 + 16 * t) + A2 * (s / 4 + 16 * t) +
        (s + 16 * t + s / 4)
      <= (9 + A1 + A2) * (17 * s) + 18 * s := by
  have hS : s / 4 + 16 * t <= 17 * s := Q43_Lemma69_A4_bound ht
  have hT : s + 16 * t + s / 4 <= 18 * s := Q43_Lemma69_A3_bound ht
  have h9 : 9 * (s / 4 + 16 * t) <= 9 * (17 * s) := Nat.mul_le_mul_left 9 hS
  have hA1 : A1 * (s / 4 + 16 * t) <= A1 * (17 * s) := Nat.mul_le_mul_left A1 hS
  have hA2 : A2 * (s / 4 + 16 * t) <= A2 * (17 * s) := Nat.mul_le_mul_left A2 hS
  have hsum :
      9 * (s / 4 + 16 * t) + A1 * (s / 4 + 16 * t) + A2 * (s / 4 + 16 * t) +
          (s + 16 * t + s / 4)
        <= 9 * (17 * s) + A1 * (17 * s) + A2 * (17 * s) + 18 * s := by
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h9 hA1) hA2) hT
  calc
    9 * (s / 4 + 16 * t) + A1 * (s / 4 + 16 * t) + A2 * (s / 4 + 16 * t) +
          (s + 16 * t + s / 4)
        <= 9 * (17 * s) + A1 * (17 * s) + A2 * (17 * s) + 18 * s := hsum
    _ = (9 + A1 + A2) * (17 * s) + 18 * s := by
      simp [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

-- Q43.S212-flat-eval-hr-depth-range-constants-a0: explicit A0 wrapper for log term.
theorem Q43_Lemma69_A0_bound {a b A0 logn delta : Nat} :
    (A0 * logn) * (delta ^ a) * (delta ^ b) = (A0 * logn) * (delta ^ (a + b)) := by
  simp [Nat.pow_add, Nat.mul_assoc]

-- Q43.S213-flat-eval-hr-depth-range-constants-a0-extract:
-- explicit A0 from Lemma 5.5 (A0 := 78*C).
def Q43_A0_from_C (C : Nat) : Nat := 78 * C

theorem Q43_A0_from_C_bound {a b C logn delta : Nat} :
    (Q43_A0_from_C C * logn) * (delta ^ a) * (delta ^ b)
      = (Q43_A0_from_C C * logn) * (delta ^ (a + b)) := by
  simpa [Q43_A0_from_C] using
    (Q43_Lemma69_A0_bound (a:=a) (b:=b) (A0:=78 * C) (logn:=logn) (delta:=delta))

-- Q43.S214-flat-eval-hr-depth-range-constants-a0-explicit-c:
-- explicit Chernoff constant for exp = e^x and log = ln, then A0 = 78*C.
def Q43_C_chernoff_ln : Nat := 120000

def Q43_A0_chernoff_ln : Nat := Q43_A0_from_C Q43_C_chernoff_ln

theorem Q43_A0_chernoff_ln_eval : Q43_A0_chernoff_ln = 9360000 := by
  decide

theorem Q43_A0_chernoff_ln_bound {a b logn delta : Nat} :
    (Q43_A0_chernoff_ln * logn) * (delta ^ a) * (delta ^ b)
      = (Q43_A0_chernoff_ln * logn) * (delta ^ (a + b)) := by
  simpa [Q43_A0_chernoff_ln] using
    (Q43_A0_from_C_bound (a:=a) (b:=b) (C:=Q43_C_chernoff_ln)
      (logn:=logn) (delta:=delta))

-- Q43.S215-flat-eval-hr-depth-range-constants-a0-propagate-explicit-a0:
-- rewrite the A0 log factor using the explicit A0 value.
theorem Q43_A0_chernoff_ln_bound_explicit {a b logn delta : Nat} :
    (Q43_A0_chernoff_ln * logn) * (delta ^ a) * (delta ^ b)
      = (9360000 * logn) * (delta ^ (a + b)) := by
  simpa [Q43_A0_chernoff_ln_eval] using
    (Q43_A0_chernoff_ln_bound (a:=a) (b:=b) (logn:=logn) (delta:=delta))

-- Q43.S216-flat-eval-hr-depth-range-constants-a0-c1c2-explicit:
-- explicit c1,c2 from the numeric A0 (exp = e^x, log = ln).
def Q43_thm41_c2_chernoff_ln : Nat := Q43_thm41_c2 Q43_A0_chernoff_ln

def Q43_thm41_c1_chernoff_ln : Nat := Q43_thm41_c1 Q43_A0_chernoff_ln

theorem Q43_thm41_c2_chernoff_ln_eval : Q43_thm41_c2_chernoff_ln = 11381760000 := by
  decide

theorem Q43_thm41_c1_chernoff_ln_eval : Q43_thm41_c1_chernoff_ln = 27680440320000 := by
  decide

-- Q43.S217-flat-eval-hr-depth-range-constants-a0-c1c2-apply-thm41:
-- log2-threshold predicate with explicit c1,c2 for Thm. 4.1.
def Q43_thm41_log2_denom_c2 (n : Nat) : Nat :=
  Q43_thm41_c2_chernoff_ln * (Nat.log2 n) ^ 4

theorem Q43_thm41_log2_denom_c2_explicit (n : Nat) :
    Q43_thm41_log2_denom_c2 n = 11381760000 * (Nat.log2 n) ^ 4 := by
  simp [Q43_thm41_log2_denom_c2, Q43_thm41_c2_chernoff_ln_eval]

def Q43_thm41_log2_threshold_c1 (n : Nat) : Prop :=
  Nat.log2 n <= n / (Q43_thm41_c1_chernoff_ln * (Nat.log2 n) ^ 4)

theorem Q43_thm41_log2_threshold_c1_explicit (n : Nat) :
    Q43_thm41_log2_threshold_c1 n
      ↔ Nat.log2 n <= n / (27680440320000 * (Nat.log2 n) ^ 4) := by
  simp [Q43_thm41_log2_threshold_c1, Q43_thm41_c1_chernoff_ln_eval]

-- Q43.S218-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime:
-- translate log2 bounds to |F| for grid size |F| = n^2.
def Q43_grid_size (n : Nat) : Nat := n * n

theorem Q43_log2_le_log2_grid_size {n : Nat} (hn : 1 <= n) :
    Nat.log2 n <= Nat.log2 (Q43_grid_size n) := by
  have hmul : n <= Q43_grid_size n := by
    calc
      n = n * 1 := by simp
      _ <= n * n := by
        exact Nat.mul_le_mul_left n hn
  exact Q43_log2_mono hmul

-- Q43.S219-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-final:
-- restate log2 threshold for |F| = n^2 with explicit c1.
def Q43_thm41_log2_threshold_c1_grid (n : Nat) : Prop :=
  Nat.log2 (Q43_grid_size n)
    <= Q43_grid_size n / (Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4)

theorem Q43_thm41_log2_threshold_c1_grid_explicit (n : Nat) :
    Q43_thm41_log2_threshold_c1_grid n
      ↔ Nat.log2 (Q43_grid_size n) <=
          Q43_grid_size n / (27680440320000 * (Nat.log2 (Q43_grid_size n)) ^ 4) := by
  simp [Q43_thm41_log2_threshold_c1_grid, Q43_thm41_c1_chernoff_ln_eval]

-- Q43.S220-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d:
-- turn the log2 threshold into a multiplication form (for regime checks).
def Q43_thm41_log2_threshold_c1_grid_mul (n : Nat) : Prop :=
  Nat.log2 (Q43_grid_size n) *
      (Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4)
    <= Q43_grid_size n

theorem Q43_thm41_log2_threshold_c1_grid_iff_mul {n : Nat}
    (hlog : 1 <= Nat.log2 (Q43_grid_size n)) :
    Q43_thm41_log2_threshold_c1_grid n ↔ Q43_thm41_log2_threshold_c1_grid_mul n := by
  have hposlog : 0 < Nat.log2 (Q43_grid_size n) := (Nat.succ_le_iff).1 hlog
  have hpow : 0 < (Nat.log2 (Q43_grid_size n)) ^ 4 := Nat.pow_pos hposlog
  have hc1 : 0 < Q43_thm41_c1_chernoff_ln := by decide
  have hpos :
      0 < Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4 :=
    Nat.mul_pos hc1 hpow
  unfold Q43_thm41_log2_threshold_c1_grid Q43_thm41_log2_threshold_c1_grid_mul
  simpa using (Nat.le_div_iff_mul_le hpos)

-- Q43.S221-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-asymptotic:
-- log2(|F|) is at least 1 for grid size |F| = n^2 when n >= 2.
theorem Q43_log2_grid_ge_one {n : Nat} (hn : 2 <= n) :
    1 <= Nat.log2 (Q43_grid_size n) := by
  have hn1 : 1 <= n := Nat.le_trans (by decide : 1 <= 2) hn
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hlogn : 1 <= Nat.log2 n := by
    have hpow : 2 ^ 1 <= n := by
      simpa using hn
    exact (Nat.le_log2 hn0).2 hpow
  exact Nat.le_trans hlogn (Q43_log2_le_log2_grid_size (n:=n) hn1)

-- Q43.S222-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-asymptotic-apply:
-- apply the asymptotic log2 condition to the multiplicative threshold.
theorem Q43_thm41_log2_threshold_c1_grid_iff_mul_asymptotic {n : Nat} (hn : 2 <= n) :
    Q43_thm41_log2_threshold_c1_grid n ↔ Q43_thm41_log2_threshold_c1_grid_mul n := by
  exact Q43_thm41_log2_threshold_c1_grid_iff_mul (Q43_log2_grid_ge_one (n:=n) hn)

-- Q43.S223-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion:
-- rewrite the multiplicative threshold using a single log2^5 term.
def Q43_thm41_log2_threshold_c1_grid_mul_pow5 (n : Nat) : Prop :=
  Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 5 <= Q43_grid_size n

theorem Q43_thm41_log2_threshold_c1_grid_mul_iff_pow5 {n : Nat} :
    Q43_thm41_log2_threshold_c1_grid_mul n
      ↔ Q43_thm41_log2_threshold_c1_grid_mul_pow5 n := by
  unfold Q43_thm41_log2_threshold_c1_grid_mul
  unfold Q43_thm41_log2_threshold_c1_grid_mul_pow5
  constructor <;> intro h
  · simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  · simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

-- Q43.S224-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-use:
-- use the log2^5 criterion to recover the original threshold when n >= 2.
theorem Q43_thm41_log2_threshold_c1_grid_of_pow5 {n : Nat} (hn : 2 <= n)
    (hpow5 : Q43_thm41_log2_threshold_c1_grid_mul_pow5 n) :
    Q43_thm41_log2_threshold_c1_grid n := by
  have hmul : Q43_thm41_log2_threshold_c1_grid_mul n :=
    (Q43_thm41_log2_threshold_c1_grid_mul_iff_pow5 (n:=n)).2 hpow5
  exact (Q43_thm41_log2_threshold_c1_grid_iff_mul_asymptotic (n:=n) hn).mpr hmul

-- Q43.S225-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound:
-- the log2^5 criterion implies the explicit lower bound |F| >= c1.
theorem Q43_thm41_log2_threshold_c1_grid_bound {n : Nat} (hn : 2 <= n)
    (hpow5 : Q43_thm41_log2_threshold_c1_grid_mul_pow5 n) :
    Q43_thm41_c1_chernoff_ln <= Q43_grid_size n := by
  have hlog : 1 <= Nat.log2 (Q43_grid_size n) :=
    Q43_log2_grid_ge_one (n:=n) hn
  have hpow_pos : 0 < (Nat.log2 (Q43_grid_size n)) ^ 5 := by
    exact Nat.pow_pos (Nat.succ_le_iff.mp hlog)
  have hpow_ge_one : 1 <= (Nat.log2 (Q43_grid_size n)) ^ 5 :=
    (Nat.succ_le_iff).2 hpow_pos
  have hmul : Q43_thm41_c1_chernoff_ln * 1
      <= Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 5 := by
    exact Nat.mul_le_mul_left _ hpow_ge_one
  have hmul' : Q43_thm41_c1_chernoff_ln
      <= Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 5 := by
    simpa using hmul
  exact Nat.le_trans hmul' hpow5

-- Q43.S226-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply:
-- package the log2^5 criterion into the regime-d threshold + bound bundle.
def Q43_thm41_regime_d_ok (n : Nat) : Prop :=
  Q43_thm41_log2_threshold_c1_grid n ∧ Q43_thm41_c1_chernoff_ln <= Q43_grid_size n

theorem Q43_thm41_regime_d_ok_of_pow5 {n : Nat} (hn : 2 <= n)
    (hpow5 : Q43_thm41_log2_threshold_c1_grid_mul_pow5 n) :
    Q43_thm41_regime_d_ok n := by
  refine ⟨?_, ?_⟩
  · exact Q43_thm41_log2_threshold_c1_grid_of_pow5 (n:=n) hn hpow5
  · exact Q43_thm41_log2_threshold_c1_grid_bound (n:=n) hn hpow5

-- Q43.S227-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params:
-- apply the regime-d bundle to parameter N via log2 monotonicity.
def Q43_thm41_log2_threshold_c1_grid_param (n N : Nat) : Prop :=
  Nat.log2 N
    <= Q43_grid_size n / (Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4)

theorem Q43_thm41_log2_threshold_c1_grid_param_of_le {n N : Nat}
    (hN : N <= Q43_grid_size n)
    (hth : Q43_thm41_log2_threshold_c1_grid n) :
    Q43_thm41_log2_threshold_c1_grid_param n N := by
  have hlog : Nat.log2 N <= Nat.log2 (Q43_grid_size n) := Q43_log2_mono hN
  exact Nat.le_trans hlog hth

def Q43_thm41_regime_d_ok_param (n N : Nat) : Prop :=
  Q43_thm41_log2_threshold_c1_grid_param n N ∧ Q43_thm41_c1_chernoff_ln <= Q43_grid_size n

theorem Q43_thm41_regime_d_ok_param_of_le {n N : Nat}
    (hN : N <= Q43_grid_size n)
    (hok : Q43_thm41_regime_d_ok n) :
    Q43_thm41_regime_d_ok_param n N := by
  rcases hok with ⟨hth, hbound⟩
  refine ⟨?_, hbound⟩
  exact Q43_thm41_log2_threshold_c1_grid_param_of_le (n:=n) (N:=N) hN hth

-- Q43.S228-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly:
-- polynomial regime for N in terms of |F| and log2 monotonicity.
def Q43_polyN (n N C : Nat) : Prop :=
  N <= (Q43_grid_size n) ^ C

theorem Q43_log2_le_log2_grid_pow {n N C : Nat} (hN : Q43_polyN n N C) :
    Nat.log2 N <= Nat.log2 ((Q43_grid_size n) ^ C) := by
  exact Q43_log2_mono hN

-- Q43.S229-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-m:
-- polynomial regime for M and t = log2 M in terms of |F|.
def Q43_polyM (n M K : Nat) : Prop :=
  M <= (Q43_grid_size n) ^ K

theorem Q43_tParam_le_log2_grid_pow {n M K : Nat} (hM : Q43_polyM n M K) :
    Q43_tParam M <= Nat.log2 ((Q43_grid_size n) ^ K) := by
  simpa [Q43_tParam] using (Q43_log2_mono hM)

-- Q43.S230-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-m-link:
-- combine poly N and poly M regimes as bundled hypotheses.
def Q43_polyNM (n N C M K : Nat) : Prop :=
  Q43_polyN n N C ∧ Q43_polyM n M K

theorem Q43_polyNM_log2_bounds {n N C M K : Nat} (h : Q43_polyNM n N C M K) :
    Nat.log2 N <= Nat.log2 ((Q43_grid_size n) ^ C) ∧
    Q43_tParam M <= Nat.log2 ((Q43_grid_size n) ^ K) := by
  rcases h with ⟨hN, hM⟩
  exact ⟨Q43_log2_le_log2_grid_pow (n:=n) (N:=N) (C:=C) hN,
    Q43_tParam_le_log2_grid_pow (n:=n) (M:=M) (K:=K) hM⟩

-- Q43.S231-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-threshold:
-- bundle the regime-d criterion with poly N/M log2 bounds.
theorem Q43_regime_d_ok_polyNM_bounds {n N C M K : Nat} (hn : 2 <= n)
    (hpow5 : Q43_thm41_log2_threshold_c1_grid_mul_pow5 n)
    (hpoly : Q43_polyNM n N C M K) :
    Q43_thm41_regime_d_ok n ∧
      Nat.log2 N <= Nat.log2 ((Q43_grid_size n) ^ C) ∧
      Q43_tParam M <= Nat.log2 ((Q43_grid_size n) ^ K) := by
  have hreg : Q43_thm41_regime_d_ok n :=
    Q43_thm41_regime_d_ok_of_pow5 (n:=n) hn hpow5
  have hbounds :
      Nat.log2 N <= Nat.log2 ((Q43_grid_size n) ^ C) ∧
      Q43_tParam M <= Nat.log2 ((Q43_grid_size n) ^ K) :=
    Q43_polyNM_log2_bounds (n:=n) (N:=N) (C:=C) (M:=M) (K:=K) hpoly
  exact ⟨hreg, hbounds⟩

theorem Q43_pow_le_pow_of_le {a b n : Nat} (h : a <= b) : a ^ n <= b ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Nat.pow_succ] using (Nat.mul_le_mul ih h)

theorem Q43_log2_pow_le_mul_succ (a C : Nat) :
    Nat.log2 (a ^ C) <= (Nat.log2 a + 1) * C := by
  by_cases ha : a = 0
  · cases C with
    | zero =>
        have hlog1 : Nat.log2 1 = 0 := by decide
        simp [ha, hlog1]
    | succ C =>
        simp [ha, Nat.log2_zero]
  · have hlt : a < 2 ^ (Nat.log2 a + 1) :=
      (Nat.log2_lt ha).1 (Nat.lt_succ_self _)
    have hle : a <= 2 ^ (Nat.log2 a + 1) := Nat.le_of_lt hlt
    have hpow : a ^ C <= (2 ^ (Nat.log2 a + 1)) ^ C :=
      Q43_pow_le_pow_of_le hle
    have hpow' : a ^ C <= 2 ^ ((Nat.log2 a + 1) * C) := by
      calc
        a ^ C <= (2 ^ (Nat.log2 a + 1)) ^ C := hpow
        _ = 2 ^ ((Nat.log2 a + 1) * C) := by
          simpa using (Nat.pow_mul 2 (Nat.log2 a + 1) C).symm
    have hlog : Nat.log2 (a ^ C) <= Nat.log2 (2 ^ ((Nat.log2 a + 1) * C)) :=
      Q43_log2_mono hpow'
    simpa [Nat.log2_two_pow] using hlog

-- Q43.S232-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-compare:
-- bound log2(|F|^C) by (log2|F| + 1) * C.
theorem Q43_log2_grid_pow_le_mul_succ (n C : Nat) :
    Nat.log2 ((Q43_grid_size n) ^ C) <= (Nat.log2 (Q43_grid_size n) + 1) * C := by
  simpa using (Q43_log2_pow_le_mul_succ (a:=Q43_grid_size n) (C:=C))

theorem Q43_log2_grid_succ_le_twice {n : Nat} (hn : 2 <= n) :
    Nat.log2 (Q43_grid_size n) + 1 <= 2 * Nat.log2 (Q43_grid_size n) := by
  have hlog : 1 <= Nat.log2 (Q43_grid_size n) := Q43_log2_grid_ge_one (n:=n) hn
  have hsum :
      Nat.log2 (Q43_grid_size n) + 1
        <= Nat.log2 (Q43_grid_size n) + Nat.log2 (Q43_grid_size n) :=
    Nat.add_le_add_left hlog _
  simpa [Nat.two_mul] using hsum

theorem Q43_log2_grid_pow_le_twice_mul {n C : Nat} (hn : 2 <= n) :
    Nat.log2 ((Q43_grid_size n) ^ C) <= 2 * Nat.log2 (Q43_grid_size n) * C := by
  have h1 := Q43_log2_grid_pow_le_mul_succ (n:=n) (C:=C)
  have h2 :
      (Nat.log2 (Q43_grid_size n) + 1) * C
        <= (2 * Nat.log2 (Q43_grid_size n)) * C := by
    exact Nat.mul_le_mul_right _ (Q43_log2_grid_succ_le_twice (n:=n) hn)
  exact Nat.le_trans h1 h2

-- Q43.S233-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-compare-threshold:
-- use a scaled log2^5 criterion to bound log2(|F|^C).
def Q43_thm41_log2_threshold_c1_grid_powC (n C : Nat) : Prop :=
  Nat.log2 ((Q43_grid_size n) ^ C)
    <= Q43_grid_size n / (Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4)

def Q43_thm41_log2_threshold_c1_grid_powC_mul (n C : Nat) : Prop :=
  Nat.log2 ((Q43_grid_size n) ^ C) *
      (Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4)
    <= Q43_grid_size n

def Q43_thm41_log2_threshold_c1_grid_pow5_scaled (n C : Nat) : Prop :=
  (2 * Nat.log2 (Q43_grid_size n) * C) *
      (Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4)
    <= Q43_grid_size n

-- Q43.S234-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-compare-final:
-- rewrite the scaled log2^5 criterion as 2*C*c1*log2^5|F| <= |F|.
def Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple (n C : Nat) : Prop :=
  (2 * C * Q43_thm41_c1_chernoff_ln) * (Nat.log2 (Q43_grid_size n)) ^ 5
    <= Q43_grid_size n

instance (n C : Nat) : Decidable (Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C) := by
  unfold Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple
  infer_instance

theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_iff_simple {n C : Nat} :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled n C ↔
      Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C := by
  unfold Q43_thm41_log2_threshold_c1_grid_pow5_scaled
  unfold Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple
  let L := Nat.log2 (Q43_grid_size n)
  have hpow : L ^ 5 = L * L ^ 4 := by
    calc
      L ^ 5 = L ^ 4 * L := by simp [Nat.pow_succ]
      _ = L * L ^ 4 := by exact Nat.mul_comm _ _
  have hrewrite :
      (2 * L * C) * (Q43_thm41_c1_chernoff_ln * L ^ 4)
        = (2 * C * Q43_thm41_c1_chernoff_ln) * (L * L ^ 4) := by
    ac_rfl
  constructor
  · intro h
    have h' :
        (2 * C * Q43_thm41_c1_chernoff_ln) * (L * L ^ 4)
          <= Q43_grid_size n := by
      simpa [hrewrite, L] using h
    simpa [← hpow, L] using h'
  · intro h
    have h' :
        (2 * C * Q43_thm41_c1_chernoff_ln) * (L * L ^ 4)
          <= Q43_grid_size n := by
      simpa [hpow, L] using h
    simpa [hrewrite, L] using h'

theorem Q43_thm41_log2_threshold_c1_grid_powC_iff_mul {n C : Nat}
    (hlog : 1 <= Nat.log2 (Q43_grid_size n)) :
    Q43_thm41_log2_threshold_c1_grid_powC n C ↔
      Q43_thm41_log2_threshold_c1_grid_powC_mul n C := by
  have hposlog : 0 < Nat.log2 (Q43_grid_size n) := (Nat.succ_le_iff).1 hlog
  have hpow : 0 < (Nat.log2 (Q43_grid_size n)) ^ 4 := Nat.pow_pos hposlog
  have hc1 : 0 < Q43_thm41_c1_chernoff_ln := by decide
  have hpos :
      0 < Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4 :=
    Nat.mul_pos hc1 hpow
  unfold Q43_thm41_log2_threshold_c1_grid_powC Q43_thm41_log2_threshold_c1_grid_powC_mul
  simpa using (Nat.le_div_iff_mul_le hpos)

theorem Q43_thm41_log2_threshold_c1_grid_powC_mul_of_scaled {n C : Nat} (hn : 2 <= n)
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled n C) :
    Q43_thm41_log2_threshold_c1_grid_powC_mul n C := by
  have hlog : Nat.log2 ((Q43_grid_size n) ^ C) <= 2 * Nat.log2 (Q43_grid_size n) * C :=
    Q43_log2_grid_pow_le_twice_mul (n:=n) (C:=C) hn
  have hmul :
      Nat.log2 ((Q43_grid_size n) ^ C) *
          (Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4)
        <= (2 * Nat.log2 (Q43_grid_size n) * C) *
            (Q43_thm41_c1_chernoff_ln * (Nat.log2 (Q43_grid_size n)) ^ 4) := by
    exact Nat.mul_le_mul hlog (Nat.le_refl _)
  exact Nat.le_trans hmul hscale

theorem Q43_thm41_log2_threshold_c1_grid_powC_of_scaled {n C : Nat} (hn : 2 <= n)
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled n C) :
    Q43_thm41_log2_threshold_c1_grid_powC n C := by
  have hmul :
      Q43_thm41_log2_threshold_c1_grid_powC_mul n C :=
    Q43_thm41_log2_threshold_c1_grid_powC_mul_of_scaled (n:=n) (C:=C) hn hscale
  have hlog : 1 <= Nat.log2 (Q43_grid_size n) := Q43_log2_grid_ge_one (n:=n) hn
  exact (Q43_thm41_log2_threshold_c1_grid_powC_iff_mul (n:=n) (C:=C) hlog).2 hmul

-- Q43.S235-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0:
-- toy explicit threshold for C=1.
def Q43_toy_n0_C1 : Nat := 2 ^ 40

theorem Q43_toy_n0_C1_ok :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple Q43_toy_n0_C1 1 := by
  decide

-- Q43.S236-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-general:
-- monotone in C: larger C makes the inequality harder.
theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_mono_C {n C1 C2 : Nat}
    (hC : C1 <= C2)
    (h : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C2) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C1 := by
  unfold Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple at *
  have hC' : 2 * C1 <= 2 * C2 := Nat.mul_le_mul_left _ hC
  have hC'' :
      2 * C1 * Q43_thm41_c1_chernoff_ln <= 2 * C2 * Q43_thm41_c1_chernoff_ln := by
    exact Nat.mul_le_mul_right _ hC'
  have hmul :
      (2 * C1 * Q43_thm41_c1_chernoff_ln) * (Nat.log2 (Q43_grid_size n)) ^ 5
        <= (2 * C2 * Q43_thm41_c1_chernoff_ln) * (Nat.log2 (Q43_grid_size n)) ^ 5 := by
    exact Nat.mul_le_mul_right _ hC''
  exact Nat.le_trans hmul h

-- Q43.S237-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-formula:
-- constant-range explicit threshold for C <= 6.
def Q43_toy_Cmax : Nat := 6

theorem Q43_toy_n0_Cmax_ok :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple Q43_toy_n0_C1 Q43_toy_Cmax := by
  decide

theorem Q43_toy_n0_C_le_Cmax {C : Nat} (hC : C <= Q43_toy_Cmax) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple Q43_toy_n0_C1 C := by
  exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_mono_C hC Q43_toy_n0_Cmax_ok

-- Q43.S238-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-monon-grid:
-- grid size is monotone in n.
theorem Q43_grid_size_mono {n m : Nat} (h : n <= m) :
    Q43_grid_size n <= Q43_grid_size m := by
  unfold Q43_grid_size
  exact Nat.mul_le_mul h h

-- Q43.S239-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-monon-log2:
-- log2 |F| is monotone in n for |F|=n^2.
theorem Q43_log2_grid_size_mono {n m : Nat} (h : n <= m) :
    Nat.log2 (Q43_grid_size n) <= Nat.log2 (Q43_grid_size m) := by
  exact Q43_log2_mono (Q43_grid_size_mono h)

-- Q43.S240-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-monon-log2-lift:
-- log2 |F|^5 is monotone in n for |F|=n^2.
theorem Q43_log2_grid_size_pow5_mono {n m : Nat} (h : n <= m) :
    (Nat.log2 (Q43_grid_size n)) ^ 5 <= (Nat.log2 (Q43_grid_size m)) ^ 5 := by
  exact Q43_pow_le_pow_of_le (Q43_log2_grid_size_mono h)

-- Q43.S241-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-threshold-lift:
-- scaled log2^5 term is monotone in n for |F|=n^2.
theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_lhs_mono {n m C : Nat}
    (h : n <= m) :
    (2 * C * Q43_thm41_c1_chernoff_ln) * (Nat.log2 (Q43_grid_size n)) ^ 5
      <= (2 * C * Q43_thm41_c1_chernoff_ln) * (Nat.log2 (Q43_grid_size m)) ^ 5 := by
  exact Nat.mul_le_mul_left _ (Q43_log2_grid_size_pow5_mono h)

-- Q43.S242-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-threshold-lift-combine:
-- bundle LHS/RHS monotonicity for the scaled log2^5 threshold.
theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_sides_mono {n m C : Nat}
    (h : n <= m) :
    (2 * C * Q43_thm41_c1_chernoff_ln) * (Nat.log2 (Q43_grid_size n)) ^ 5
      <= (2 * C * Q43_thm41_c1_chernoff_ln) * (Nat.log2 (Q43_grid_size m)) ^ 5 ∧
    Q43_grid_size n <= Q43_grid_size m := by
  exact ⟨Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_lhs_mono (n:=n) (m:=m) (C:=C) h,
    Q43_grid_size_mono h⟩

-- Q43.S243-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-threshold-lift-finish:
-- rewrite the scaled log2^5 threshold as a ratio bound.
theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_iff_ratio {n C : Nat}
    (hpos : 0 < (Nat.log2 (Q43_grid_size n)) ^ 5) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C
      ↔ 2 * C * Q43_thm41_c1_chernoff_ln
          <= Q43_grid_size n / (Nat.log2 (Q43_grid_size n)) ^ 5 := by
  unfold Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple
  have h :
      2 * C * Q43_thm41_c1_chernoff_ln
          <= Q43_grid_size n / (Nat.log2 (Q43_grid_size n)) ^ 5
        ↔ (2 * C * Q43_thm41_c1_chernoff_ln) * (Nat.log2 (Q43_grid_size n)) ^ 5
            <= Q43_grid_size n := by
    simpa using (Nat.le_div_iff_mul_le hpos)
  exact h.symm

-- Q43.S244-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-ratio-mono-counterexample-2047-2048:
-- Nat.log2 floor makes the ratio non-monotone across the 2^k jump.
def Q43_grid_ratio (n : Nat) : Nat :=
  Q43_grid_size n / (Nat.log2 (Q43_grid_size n)) ^ 5

theorem Q43_grid_ratio_drop_2047_2048 :
    Q43_grid_ratio 2048 < Q43_grid_ratio 2047 := by
  decide

-- Q43.S245-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-ratio-lift-piecewise-log2-jump:
-- ratio is monotone on subranges where log2 |F| is constant.
theorem Q43_grid_ratio_mono_of_log2_eq {n m : Nat} (h : n <= m)
    (hlog : Nat.log2 (Q43_grid_size n) = Nat.log2 (Q43_grid_size m)) :
    Q43_grid_ratio n <= Q43_grid_ratio m := by
  unfold Q43_grid_ratio
  have hgrid : Q43_grid_size n <= Q43_grid_size m := Q43_grid_size_mono h
  simpa [hlog] using
    (Nat.div_le_div_right (c := (Nat.log2 (Q43_grid_size m)) ^ 5) hgrid)

-- Q43.S246-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-ratio-lift-piecewise-intervals:
-- a concrete plateau: for n in [2^k, (5/4)·2^k] (k≥2), log2 |F| is constant for |F|=n^2.
theorem Q43_log2_grid_size_eq_double_of_range {k n : Nat} (hk : 2 <= k)
    (hlo : 2 ^ k <= n) (hhi : n <= 5 * 2 ^ (k - 2)) :
    Nat.log2 (Q43_grid_size n) = 2 * k := by
  have hpowpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hnpos : 0 < n := Nat.lt_of_lt_of_le hpowpos hlo
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hne : Q43_grid_size n ≠ 0 := by
    simpa [Q43_grid_size] using (Nat.mul_ne_zero hnne hnne)
  have hpow : (2 ^ k) ^ 2 <= n ^ 2 :=
    Q43_pow_le_pow_of_le (a := 2 ^ k) (b := n) (n := 2) hlo
  have hlow : 2 ^ (2 * k) <= Q43_grid_size n := by
    have hpow2 : 2 ^ (2 * k) = (2 ^ k) ^ 2 := by
      simpa [Nat.mul_comm] using (Nat.pow_mul 2 k 2)
    simpa [hpow2, Q43_grid_size, Nat.pow_two] using hpow
  have hpow_hi : n ^ 2 <= (5 * 2 ^ (k - 2)) ^ 2 :=
    Q43_pow_le_pow_of_le (a := n) (b := 5 * 2 ^ (k - 2)) (n := 2) hhi
  have hbound : (5 * 2 ^ (k - 2)) ^ 2 < 2 ^ (2 * k + 1) := by
    let t : Nat := 2 ^ (k - 2)
    have htpos : 0 < t := by
      simpa [t] using (Nat.pow_pos (by decide) : 0 < 2 ^ (k - 2))
    have hcoeff : 25 < 32 := by decide
    have h1 : 25 * t < 32 * t := (Nat.mul_lt_mul_right (a0 := htpos)).2 hcoeff
    have h2 : 25 * t * t < 32 * t * t := (Nat.mul_lt_mul_right (a0 := htpos)).2 h1
    have hpowt : 2 ^ (2 * (k - 2)) = t * t := by
      have hpow' : 2 ^ ((k - 2) * 2) = (2 ^ (k - 2)) ^ 2 :=
        Nat.pow_mul 2 (k - 2) 2
      simpa [t, Nat.mul_comm, Nat.pow_two] using hpow'
    have hle : 4 <= 2 * k := by
      have hle' : 2 * 2 <= 2 * k := Nat.mul_le_mul_left 2 hk
      simpa using hle'
    have hexp : 2 * (k - 2) + 5 = 2 * k + 1 := by
      calc
        2 * (k - 2) + 5 = (2 * k - 4) + 5 := by
          simp [Nat.mul_sub_left_distrib, Nat.mul_comm]
        _ = (2 * k - 4) + 4 + 1 := by simp [Nat.add_assoc]
        _ = 2 * k + 1 := by
          have hsub : (2 * k - 4) + 4 = 2 * k := Nat.sub_add_cancel hle
          simp [hsub]
    have hpow32 : 2 ^ (2 * k + 1) = 32 * t * t := by
      calc
        2 ^ (2 * k + 1) = 2 ^ (2 * (k - 2) + 5) := by simp [hexp]
        _ = 2 ^ (2 * (k - 2)) * 2 ^ 5 := by
          simp [Nat.pow_add]
        _ = 32 * t * t := by
          simp [t, hpowt, Nat.mul_comm, Nat.mul_assoc]
    have hpow5 : (5 * t) ^ 2 = 25 * t * t := by
      simp [Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm]
    simpa [t, hpow5, hpow32] using h2
  have hupper : Q43_grid_size n < 2 ^ (2 * k + 1) := by
    have hpow_hi' : Q43_grid_size n <= (5 * 2 ^ (k - 2)) ^ 2 := by
      simpa [Q43_grid_size, Nat.pow_two] using hpow_hi
    exact Nat.lt_of_le_of_lt hpow_hi' hbound
  exact (Nat.log2_eq_iff hne).2 ⟨hlow, hupper⟩

-- Q43.S247-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-ratio-lift-piecewise-intervals-apply:
-- apply the plateau lemma to the ratio monotonicity on the sub-interval.
theorem Q43_grid_ratio_mono_on_plateau {k n m : Nat} (hk : 2 <= k)
    (hn : 2 ^ k <= n) (hm : 2 ^ k <= m)
    (hn_hi : n <= 5 * 2 ^ (k - 2)) (hm_hi : m <= 5 * 2 ^ (k - 2))
    (h : n <= m) :
    Q43_grid_ratio n <= Q43_grid_ratio m := by
  have hlogn : Nat.log2 (Q43_grid_size n) = 2 * k :=
    Q43_log2_grid_size_eq_double_of_range (k:=k) (n:=n) hk hn hn_hi
  have hlogm : Nat.log2 (Q43_grid_size m) = 2 * k :=
    Q43_log2_grid_size_eq_double_of_range (k:=k) (n:=m) hk hm hm_hi
  have hlog : Nat.log2 (Q43_grid_size n) = Nat.log2 (Q43_grid_size m) := by
    simp [hlogn, hlogm]
  exact Q43_grid_ratio_mono_of_log2_eq (n:=n) (m:=m) h hlog

-- Q43.S248-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-intervals-cover:
-- upper plateau: for n in [(3/2)·2^k, 2^(k+1)) (k≥2), log2 |F| = 2k+1 for |F|=n^2.
theorem Q43_log2_grid_size_eq_double_succ_of_range {k n : Nat} (hk : 2 <= k)
    (hlo : 3 * 2 ^ (k - 1) <= n) (hhi : n < 2 ^ (k + 1)) :
    Nat.log2 (Q43_grid_size n) = 2 * k + 1 := by
  let t : Nat := 2 ^ (k - 1)
  have htpos : 0 < t := by
    simpa [t] using (Nat.pow_pos (by decide) : 0 < 2 ^ (k - 1))
  have h3pos : 0 < 3 * t := Nat.mul_pos (by decide) htpos
  have hlo' : 3 * t <= n := by simpa [t] using hlo
  have hnpos : 0 < n := Nat.lt_of_lt_of_le h3pos hlo'
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hne : Q43_grid_size n ≠ 0 := by
    simpa [Q43_grid_size] using (Nat.mul_ne_zero hnne hnne)
  have hpow_lo : (3 * t) ^ 2 <= n ^ 2 := Q43_pow_le_pow_of_le hlo'
  have hpowt : 2 ^ (2 * (k - 1)) = t * t := by
    have hpow' : 2 ^ ((k - 1) * 2) = (2 ^ (k - 1)) ^ 2 := Nat.pow_mul 2 (k - 1) 2
    simpa [t, Nat.mul_comm, Nat.pow_two] using hpow'
  have hk1 : 1 <= k := Nat.le_trans (by decide : 1 <= 2) hk
  have hk1' : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  have hexp : 2 * (k - 1) + 3 = 2 * k + 1 := by
    calc
      2 * (k - 1) + 3 = (2 * (k - 1) + 2) + 1 := by
        simp [Nat.add_assoc]
      _ = 2 * ((k - 1) + 1) + 1 := by
        simp [Nat.mul_add, Nat.add_assoc]
      _ = 2 * k + 1 := by
        simp [hk1']
  have hpow8 : 2 ^ (2 * k + 1) = 8 * t * t := by
    calc
      2 ^ (2 * k + 1) = 2 ^ (2 * (k - 1) + 3) := by
        simp [hexp]
      _ = 2 ^ (2 * (k - 1)) * 2 ^ 3 := by
        simp [Nat.pow_add]
      _ = (t * t) * 8 := by
        simp [hpowt]
      _ = 8 * t * t := by
        simp [Nat.mul_comm, Nat.mul_assoc]
  have hpow3 : (3 * t) ^ 2 = 9 * t * t := by
    simp [Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm]
  have hcoeff : 8 <= 9 := by decide
  have hmul : 8 * t * t <= 9 * t * t := by
    have hmul' : 8 * (t * t) <= 9 * (t * t) := Nat.mul_le_mul_right _ hcoeff
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul'
  have hlow' : 2 ^ (2 * k + 1) <= (3 * t) ^ 2 := by
    calc
      2 ^ (2 * k + 1) = 8 * t * t := hpow8
      _ <= 9 * t * t := hmul
      _ = (3 * t) ^ 2 := hpow3.symm
  have hlow : 2 ^ (2 * k + 1) <= Q43_grid_size n := by
    have hlow'' : 2 ^ (2 * k + 1) <= n ^ 2 := Nat.le_trans hlow' hpow_lo
    simpa [Q43_grid_size, Nat.pow_two] using hlow''
  let u : Nat := 2 ^ (k + 1)
  have hup : n < u := by simpa [u] using hhi
  have htpos_u : 0 < u := by
    simpa [u] using (Nat.pow_pos (by decide) : 0 < 2 ^ (k + 1))
  have h1 : n * n < n * u := by
    have h1' : n * n < u * n := (Nat.mul_lt_mul_right (a0 := hnpos)).2 hup
    simpa [Nat.mul_comm] using h1'
  have h2 : n * u < u * u := by
    exact (Nat.mul_lt_mul_right (a0 := htpos_u)).2 hup
  have hmul' : n * n < u * u := Nat.lt_trans h1 h2
  have hpow_hi : n ^ 2 < u ^ 2 := by
    simpa [Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul'
  have hexp_u : (k + 1) * 2 = 2 * k + 2 := by
    calc
      (k + 1) * 2 = k * 2 + 1 * 2 := by
        simp [Nat.add_mul]
      _ = 2 * k + 2 := by
        simp [Nat.mul_comm]
  have hu2 : u ^ 2 = 2 ^ (2 * k + 2) := by
    have hpow' : 2 ^ ((k + 1) * 2) = (2 ^ (k + 1)) ^ 2 := Nat.pow_mul 2 (k + 1) 2
    calc
      u ^ 2 = (2 ^ (k + 1)) ^ 2 := by rfl
      _ = 2 ^ ((k + 1) * 2) := by
        symm
        exact hpow'
      _ = 2 ^ (2 * k + 2) := by
        simp [hexp_u]
  have hupper : Q43_grid_size n < 2 ^ (2 * k + 2) := by
    have hpow_hi' : n ^ 2 < 2 ^ (2 * k + 2) := by
      simpa [hu2] using hpow_hi
    simpa [Q43_grid_size, Nat.pow_two] using hpow_hi'
  exact (Nat.log2_eq_iff hne).2 ⟨hlow, hupper⟩

-- apply the upper plateau to the ratio monotonicity on [3·2^(k-1), 2^(k+1)).
theorem Q43_grid_ratio_mono_on_plateau_upper {k n m : Nat} (hk : 2 <= k)
    (hn : 3 * 2 ^ (k - 1) <= n) (hm : 3 * 2 ^ (k - 1) <= m)
    (hn_hi : n < 2 ^ (k + 1)) (hm_hi : m < 2 ^ (k + 1))
    (h : n <= m) :
    Q43_grid_ratio n <= Q43_grid_ratio m := by
  have hlogn : Nat.log2 (Q43_grid_size n) = 2 * k + 1 :=
    Q43_log2_grid_size_eq_double_succ_of_range (k:=k) (n:=n) hk hn hn_hi
  have hlogm : Nat.log2 (Q43_grid_size m) = 2 * k + 1 :=
    Q43_log2_grid_size_eq_double_succ_of_range (k:=k) (n:=m) hk hm hm_hi
  have hlog : Nat.log2 (Q43_grid_size n) = Nat.log2 (Q43_grid_size m) := by
    simp [hlogn, hlogm]
  exact Q43_grid_ratio_mono_of_log2_eq (n:=n) (m:=m) h hlog

-- Q43.S249-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-bridge:
-- counterexample inside the gap [5*2^(k-2), 3*2^(k-1)) for k=12.
def Q43_gap_k : Nat := 12
def Q43_gap_n : Nat := 5792
def Q43_gap_n_succ : Nat := 5793
theorem Q43_gap_n_succ_eq : Q43_gap_n + 1 = Q43_gap_n_succ := by
  decide
def Q43_gap_end_lo_k (k : Nat) : Nat := 5 * 2 ^ (k - 2)
def Q43_gap_end_hi_k (k : Nat) : Nat := 3 * 2 ^ (k - 1)
def Q43_gap_range_list_k (k : Nat) : List Nat :=
  (List.range (Q43_gap_end_hi_k k - Q43_gap_end_lo_k k)).map (fun i => Q43_gap_end_lo_k k + i)
def Q43_gap_min_ratio_k (_k n0 : Nat) : Nat := Q43_grid_ratio n0

theorem Q43_gap_range :
    5 * 2 ^ (Q43_gap_k - 2) <= Q43_gap_n ∧
    5 * 2 ^ (Q43_gap_k - 2) <= Q43_gap_n_succ ∧
    Q43_gap_n_succ < 3 * 2 ^ (Q43_gap_k - 1) := by
  decide

theorem Q43_grid_ratio_drop_gap :
    Q43_grid_ratio Q43_gap_n_succ < Q43_grid_ratio Q43_gap_n := by
  decide

-- Q43.S282-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k41:
-- counterexample inside the gap for k=41.
def Q43_gap_k41 : Nat := 41
def Q43_gap_n41 : Nat := 3109888511975
def Q43_gap_n41_succ : Nat := 3109888511976

theorem Q43_gap_range_k41 :
    Q43_gap_end_lo_k Q43_gap_k41 <= Q43_gap_n41 ∧
    Q43_gap_end_lo_k Q43_gap_k41 <= Q43_gap_n41_succ ∧
    Q43_gap_n41_succ < Q43_gap_end_hi_k Q43_gap_k41 := by
  decide

theorem Q43_grid_ratio_drop_gap_k41 :
    Q43_grid_ratio Q43_gap_n41_succ < Q43_grid_ratio Q43_gap_n41 := by
  decide

-- Q43.S283-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k42:
-- counterexample inside the gap for k=42.
def Q43_gap_k42 : Nat := 42
def Q43_gap_n42 : Nat := 6219777023950
def Q43_gap_n42_succ : Nat := 6219777023951

theorem Q43_gap_range_k42 :
    Q43_gap_end_lo_k Q43_gap_k42 <= Q43_gap_n42 ∧
    Q43_gap_end_lo_k Q43_gap_k42 <= Q43_gap_n42_succ ∧
    Q43_gap_n42_succ < Q43_gap_end_hi_k Q43_gap_k42 := by
  decide

theorem Q43_grid_ratio_drop_gap_k42 :
    Q43_grid_ratio Q43_gap_n42_succ < Q43_grid_ratio Q43_gap_n42 := by
  decide

-- Q43.S284-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k43:
-- counterexample inside the gap for k=43.
def Q43_gap_k43 : Nat := 43
def Q43_gap_n43 : Nat := 12439554047901
def Q43_gap_n43_succ : Nat := 12439554047902

theorem Q43_gap_range_k43 :
    Q43_gap_end_lo_k Q43_gap_k43 <= Q43_gap_n43 ∧
    Q43_gap_end_lo_k Q43_gap_k43 <= Q43_gap_n43_succ ∧
    Q43_gap_n43_succ < Q43_gap_end_hi_k Q43_gap_k43 := by
  decide

theorem Q43_grid_ratio_drop_gap_k43 :
    Q43_grid_ratio Q43_gap_n43_succ < Q43_grid_ratio Q43_gap_n43 := by
  decide

-- Q43.S285-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k44:
-- counterexample inside the gap for k=44.
def Q43_gap_k44 : Nat := 44
def Q43_gap_n44 : Nat := 24879108095803
def Q43_gap_n44_succ : Nat := 24879108095804

theorem Q43_gap_range_k44 :
    Q43_gap_end_lo_k Q43_gap_k44 <= Q43_gap_n44 ∧
    Q43_gap_end_lo_k Q43_gap_k44 <= Q43_gap_n44_succ ∧
    Q43_gap_n44_succ < Q43_gap_end_hi_k Q43_gap_k44 := by
  decide

theorem Q43_grid_ratio_drop_gap_k44 :
    Q43_grid_ratio Q43_gap_n44_succ < Q43_grid_ratio Q43_gap_n44 := by
  decide

-- Q43.S286-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k45:
-- counterexample inside the gap for k=45.
def Q43_gap_k45 : Nat := 45
def Q43_gap_n45 : Nat := 49758216191607
def Q43_gap_n45_succ : Nat := 49758216191608

theorem Q43_gap_range_k45 :
    Q43_gap_end_lo_k Q43_gap_k45 <= Q43_gap_n45 ∧
    Q43_gap_end_lo_k Q43_gap_k45 <= Q43_gap_n45_succ ∧
    Q43_gap_n45_succ < Q43_gap_end_hi_k Q43_gap_k45 := by
  decide

theorem Q43_grid_ratio_drop_gap_k45 :
    Q43_grid_ratio Q43_gap_n45_succ < Q43_grid_ratio Q43_gap_n45 := by
  decide

-- Q43.S287-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k46:
-- counterexample inside the gap for k=46.
def Q43_gap_k46 : Nat := 46
def Q43_gap_n46 : Nat := 99516432383215
def Q43_gap_n46_succ : Nat := 99516432383216

theorem Q43_gap_range_k46 :
    Q43_gap_end_lo_k Q43_gap_k46 <= Q43_gap_n46 ∧
    Q43_gap_end_lo_k Q43_gap_k46 <= Q43_gap_n46_succ ∧
    Q43_gap_n46_succ < Q43_gap_end_hi_k Q43_gap_k46 := by
  decide

theorem Q43_grid_ratio_drop_gap_k46 :
    Q43_grid_ratio Q43_gap_n46_succ < Q43_grid_ratio Q43_gap_n46 := by
  decide

-- Q43.S288-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k47:
-- counterexample inside the gap for k=47.
def Q43_gap_k47 : Nat := 47
def Q43_gap_n47 : Nat := 199032864766430
def Q43_gap_n47_succ : Nat := 199032864766431

theorem Q43_gap_range_k47 :
    Q43_gap_end_lo_k Q43_gap_k47 <= Q43_gap_n47 ∧
    Q43_gap_end_lo_k Q43_gap_k47 <= Q43_gap_n47_succ ∧
    Q43_gap_n47_succ < Q43_gap_end_hi_k Q43_gap_k47 := by
  decide

theorem Q43_grid_ratio_drop_gap_k47 :
    Q43_grid_ratio Q43_gap_n47_succ < Q43_grid_ratio Q43_gap_n47 := by
  decide

-- Q43.S289-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k48:
-- counterexample inside the gap for k=48.
def Q43_gap_k48 : Nat := 48
def Q43_gap_n48 : Nat := 398065729532860
def Q43_gap_n48_succ : Nat := 398065729532861

theorem Q43_gap_range_k48 :
    Q43_gap_end_lo_k Q43_gap_k48 <= Q43_gap_n48 ∧
    Q43_gap_end_lo_k Q43_gap_k48 <= Q43_gap_n48_succ ∧
    Q43_gap_n48_succ < Q43_gap_end_hi_k Q43_gap_k48 := by
  decide

theorem Q43_grid_ratio_drop_gap_k48 :
    Q43_grid_ratio Q43_gap_n48_succ < Q43_grid_ratio Q43_gap_n48 := by
  decide

-- Q43.S290-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k49:
-- counterexample inside the gap for k=49.
def Q43_gap_k49 : Nat := 49
def Q43_gap_n49 : Nat := 796131459065721
def Q43_gap_n49_succ : Nat := 796131459065722

theorem Q43_gap_range_k49 :
    Q43_gap_end_lo_k Q43_gap_k49 <= Q43_gap_n49 ∧
    Q43_gap_end_lo_k Q43_gap_k49 <= Q43_gap_n49_succ ∧
    Q43_gap_n49_succ < Q43_gap_end_hi_k Q43_gap_k49 := by
  decide

theorem Q43_grid_ratio_drop_gap_k49 :
    Q43_grid_ratio Q43_gap_n49_succ < Q43_grid_ratio Q43_gap_n49 := by
  decide

-- Q43.S291-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k50:
-- counterexample inside the gap for k=50.
def Q43_gap_k50 : Nat := 50
def Q43_gap_n50 : Nat := 1592262918131443
def Q43_gap_n50_succ : Nat := 1592262918131444

theorem Q43_gap_range_k50 :
    Q43_gap_end_lo_k Q43_gap_k50 <= Q43_gap_n50 ∧
    Q43_gap_end_lo_k Q43_gap_k50 <= Q43_gap_n50_succ ∧
    Q43_gap_n50_succ < Q43_gap_end_hi_k Q43_gap_k50 := by
  decide

theorem Q43_grid_ratio_drop_gap_k50 :
    Q43_grid_ratio Q43_gap_n50_succ < Q43_grid_ratio Q43_gap_n50 := by
  decide

-- Q43.S292-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k51:
-- counterexample inside the gap for k=51.
def Q43_gap_k51 : Nat := 51
def Q43_gap_n51 : Nat := 3184525836262886
def Q43_gap_n51_succ : Nat := 3184525836262887

theorem Q43_gap_range_k51 :
    Q43_gap_end_lo_k Q43_gap_k51 <= Q43_gap_n51 ∧
    Q43_gap_end_lo_k Q43_gap_k51 <= Q43_gap_n51_succ ∧
    Q43_gap_n51_succ < Q43_gap_end_hi_k Q43_gap_k51 := by
  decide

theorem Q43_grid_ratio_drop_gap_k51 :
    Q43_grid_ratio Q43_gap_n51_succ < Q43_grid_ratio Q43_gap_n51 := by
  decide

-- Q43.S293-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k52:
-- counterexample inside the gap for k=52.
def Q43_gap_k52 : Nat := 52
def Q43_gap_n52 : Nat := 6369051672525772
def Q43_gap_n52_succ : Nat := 6369051672525773

theorem Q43_gap_range_k52 :
    Q43_gap_end_lo_k Q43_gap_k52 <= Q43_gap_n52 ∧
    Q43_gap_end_lo_k Q43_gap_k52 <= Q43_gap_n52_succ ∧
    Q43_gap_n52_succ < Q43_gap_end_hi_k Q43_gap_k52 := by
  decide

theorem Q43_grid_ratio_drop_gap_k52 :
    Q43_grid_ratio Q43_gap_n52_succ < Q43_grid_ratio Q43_gap_n52 := by
  decide

-- Q43.S294-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k53:
-- counterexample inside the gap for k=53.
def Q43_gap_k53 : Nat := 53
def Q43_gap_n53 : Nat := 12738103345051545
def Q43_gap_n53_succ : Nat := 12738103345051546

theorem Q43_gap_range_k53 :
    Q43_gap_end_lo_k Q43_gap_k53 <= Q43_gap_n53 ∧
    Q43_gap_end_lo_k Q43_gap_k53 <= Q43_gap_n53_succ ∧
    Q43_gap_n53_succ < Q43_gap_end_hi_k Q43_gap_k53 := by
  decide

theorem Q43_grid_ratio_drop_gap_k53 :
    Q43_grid_ratio Q43_gap_n53_succ < Q43_grid_ratio Q43_gap_n53 := by
  decide

-- Q43.S295-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k54:
-- counterexample inside the gap for k=54.
def Q43_gap_k54 : Nat := 54
def Q43_gap_n54 : Nat := 25476206690103090
def Q43_gap_n54_succ : Nat := 25476206690103091

theorem Q43_gap_range_k54 :
    Q43_gap_end_lo_k Q43_gap_k54 <= Q43_gap_n54 ∧
    Q43_gap_end_lo_k Q43_gap_k54 <= Q43_gap_n54_succ ∧
    Q43_gap_n54_succ < Q43_gap_end_hi_k Q43_gap_k54 := by
  decide

theorem Q43_grid_ratio_drop_gap_k54 :
    Q43_grid_ratio Q43_gap_n54_succ < Q43_grid_ratio Q43_gap_n54 := by
  decide

-- Q43.S296-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k55:
-- counterexample inside the gap for k=55.
def Q43_gap_k55 : Nat := 55
def Q43_gap_n55 : Nat := 50952413380206180
def Q43_gap_n55_succ : Nat := 50952413380206181

theorem Q43_gap_range_k55 :
    Q43_gap_end_lo_k Q43_gap_k55 <= Q43_gap_n55 ∧
    Q43_gap_end_lo_k Q43_gap_k55 <= Q43_gap_n55_succ ∧
    Q43_gap_n55_succ < Q43_gap_end_hi_k Q43_gap_k55 := by
  decide

theorem Q43_grid_ratio_drop_gap_k55 :
    Q43_grid_ratio Q43_gap_n55_succ < Q43_grid_ratio Q43_gap_n55 := by
  decide

-- Q43.S297-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k56:
-- counterexample inside the gap for k=56.
def Q43_gap_k56 : Nat := 56
def Q43_gap_n56 : Nat := 101904826760412361
def Q43_gap_n56_succ : Nat := 101904826760412362

theorem Q43_gap_range_k56 :
    Q43_gap_end_lo_k Q43_gap_k56 <= Q43_gap_n56 ∧
    Q43_gap_end_lo_k Q43_gap_k56 <= Q43_gap_n56_succ ∧
    Q43_gap_n56_succ < Q43_gap_end_hi_k Q43_gap_k56 := by
  decide

theorem Q43_grid_ratio_drop_gap_k56 :
    Q43_grid_ratio Q43_gap_n56_succ < Q43_grid_ratio Q43_gap_n56 := by
  decide

-- Q43.S298-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k57:
-- counterexample inside the gap for k=57.
def Q43_gap_k57 : Nat := 57
def Q43_gap_n57 : Nat := 203809653520824722
def Q43_gap_n57_succ : Nat := 203809653520824723

theorem Q43_gap_range_k57 :
    Q43_gap_end_lo_k Q43_gap_k57 <= Q43_gap_n57 ∧
    Q43_gap_end_lo_k Q43_gap_k57 <= Q43_gap_n57_succ ∧
    Q43_gap_n57_succ < Q43_gap_end_hi_k Q43_gap_k57 := by
  decide

theorem Q43_grid_ratio_drop_gap_k57 :
    Q43_grid_ratio Q43_gap_n57_succ < Q43_grid_ratio Q43_gap_n57 := by
  decide

-- Q43.S299-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k58:
-- counterexample inside the gap for k=58.
def Q43_gap_k58 : Nat := 58
def Q43_gap_n58 : Nat := 407619307041649444
def Q43_gap_n58_succ : Nat := 407619307041649445

theorem Q43_gap_range_k58 :
    Q43_gap_end_lo_k Q43_gap_k58 <= Q43_gap_n58 ∧
    Q43_gap_end_lo_k Q43_gap_k58 <= Q43_gap_n58_succ ∧
    Q43_gap_n58_succ < Q43_gap_end_hi_k Q43_gap_k58 := by
  decide

theorem Q43_grid_ratio_drop_gap_k58 :
    Q43_grid_ratio Q43_gap_n58_succ < Q43_grid_ratio Q43_gap_n58 := by
  decide

-- Q43.S300-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k59:
-- counterexample inside the gap for k=59.
def Q43_gap_k59 : Nat := 59
def Q43_gap_n59 : Nat := 815238614083298888
def Q43_gap_n59_succ : Nat := 815238614083298889

theorem Q43_gap_range_k59 :
    Q43_gap_end_lo_k Q43_gap_k59 <= Q43_gap_n59 ∧
    Q43_gap_end_lo_k Q43_gap_k59 <= Q43_gap_n59_succ ∧
    Q43_gap_n59_succ < Q43_gap_end_hi_k Q43_gap_k59 := by
  decide

theorem Q43_grid_ratio_drop_gap_k59 :
    Q43_grid_ratio Q43_gap_n59_succ < Q43_grid_ratio Q43_gap_n59 := by
  decide

-- Q43.S301-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k60:
-- counterexample inside the gap for k=60.
def Q43_gap_k60 : Nat := 60
def Q43_gap_n60 : Nat := 1630477228166597776
def Q43_gap_n60_succ : Nat := 1630477228166597777

theorem Q43_gap_range_k60 :
    Q43_gap_end_lo_k Q43_gap_k60 <= Q43_gap_n60 ∧
    Q43_gap_end_lo_k Q43_gap_k60 <= Q43_gap_n60_succ ∧
    Q43_gap_n60_succ < Q43_gap_end_hi_k Q43_gap_k60 := by
  decide

theorem Q43_grid_ratio_drop_gap_k60 :
    Q43_grid_ratio Q43_gap_n60_succ < Q43_grid_ratio Q43_gap_n60 := by
  decide

-- Q43.S302-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k61:
-- counterexample inside the gap for k=61.
def Q43_gap_k61 : Nat := 61
def Q43_gap_n61 : Nat := 3260954456333195553
def Q43_gap_n61_succ : Nat := 3260954456333195554

theorem Q43_gap_range_k61 :
    Q43_gap_end_lo_k Q43_gap_k61 <= Q43_gap_n61 ∧
    Q43_gap_end_lo_k Q43_gap_k61 <= Q43_gap_n61_succ ∧
    Q43_gap_n61_succ < Q43_gap_end_hi_k Q43_gap_k61 := by
  decide

theorem Q43_grid_ratio_drop_gap_k61 :
    Q43_grid_ratio Q43_gap_n61_succ < Q43_grid_ratio Q43_gap_n61 := by
  decide

-- Q43.S303-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k62:
-- counterexample inside the gap for k=62.
def Q43_gap_k62 : Nat := 62
def Q43_gap_n62 : Nat := 6521908912666391106
def Q43_gap_n62_succ : Nat := 6521908912666391107

theorem Q43_gap_range_k62 :
    Q43_gap_end_lo_k Q43_gap_k62 <= Q43_gap_n62 ∧
    Q43_gap_end_lo_k Q43_gap_k62 <= Q43_gap_n62_succ ∧
    Q43_gap_n62_succ < Q43_gap_end_hi_k Q43_gap_k62 := by
  decide

theorem Q43_grid_ratio_drop_gap_k62 :
    Q43_grid_ratio Q43_gap_n62_succ < Q43_grid_ratio Q43_gap_n62 := by
  decide

-- Q43.S304-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k63:
-- counterexample inside the gap for k=63.
def Q43_gap_k63 : Nat := 63
def Q43_gap_n63 : Nat := 13043817825332782212
def Q43_gap_n63_succ : Nat := 13043817825332782213

theorem Q43_gap_range_k63 :
    Q43_gap_end_lo_k Q43_gap_k63 <= Q43_gap_n63 ∧
    Q43_gap_end_lo_k Q43_gap_k63 <= Q43_gap_n63_succ ∧
    Q43_gap_n63_succ < Q43_gap_end_hi_k Q43_gap_k63 := by
  decide

theorem Q43_grid_ratio_drop_gap_k63 :
    Q43_grid_ratio Q43_gap_n63_succ < Q43_grid_ratio Q43_gap_n63 := by
  decide

-- Q43.S305-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k64:
-- counterexample inside the gap for k=64.
def Q43_gap_k64 : Nat := 64
def Q43_gap_n64 : Nat := 26087635650665564424
def Q43_gap_n64_succ : Nat := 26087635650665564425

theorem Q43_gap_range_k64 :
    Q43_gap_end_lo_k Q43_gap_k64 <= Q43_gap_n64 ∧
    Q43_gap_end_lo_k Q43_gap_k64 <= Q43_gap_n64_succ ∧
    Q43_gap_n64_succ < Q43_gap_end_hi_k Q43_gap_k64 := by
  decide

theorem Q43_grid_ratio_drop_gap_k64 :
    Q43_grid_ratio Q43_gap_n64_succ < Q43_grid_ratio Q43_gap_n64 := by
  decide

-- Q43.S306-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k65:
-- counterexample inside the gap for k=65.
def Q43_gap_k65 : Nat := 65
def Q43_gap_n65 : Nat := 52175271301331128849
def Q43_gap_n65_succ : Nat := 52175271301331128850

theorem Q43_gap_range_k65 :
    Q43_gap_end_lo_k Q43_gap_k65 <= Q43_gap_n65 ∧
    Q43_gap_end_lo_k Q43_gap_k65 <= Q43_gap_n65_succ ∧
    Q43_gap_n65_succ < Q43_gap_end_hi_k Q43_gap_k65 := by
  decide

theorem Q43_grid_ratio_drop_gap_k65 :
    Q43_grid_ratio Q43_gap_n65_succ < Q43_grid_ratio Q43_gap_n65 := by
  decide

-- Q43.S307-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k66:
-- counterexample inside the gap for k=66.
def Q43_gap_k66 : Nat := 66
def Q43_gap_n66 : Nat := 104350542602662257698
def Q43_gap_n66_succ : Nat := 104350542602662257699

theorem Q43_gap_range_k66 :
    Q43_gap_end_lo_k Q43_gap_k66 <= Q43_gap_n66 ∧
    Q43_gap_end_lo_k Q43_gap_k66 <= Q43_gap_n66_succ ∧
    Q43_gap_n66_succ < Q43_gap_end_hi_k Q43_gap_k66 := by
  decide

theorem Q43_grid_ratio_drop_gap_k66 :
    Q43_grid_ratio Q43_gap_n66_succ < Q43_grid_ratio Q43_gap_n66 := by
  decide

-- Q43.S308-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k67:
-- counterexample inside the gap for k=67.
def Q43_gap_k67 : Nat := 67
def Q43_gap_n67 : Nat := 208701085205324515397
def Q43_gap_n67_succ : Nat := 208701085205324515398

theorem Q43_gap_range_k67 :
    Q43_gap_end_lo_k Q43_gap_k67 <= Q43_gap_n67 ∧
    Q43_gap_end_lo_k Q43_gap_k67 <= Q43_gap_n67_succ ∧
    Q43_gap_n67_succ < Q43_gap_end_hi_k Q43_gap_k67 := by
  decide

theorem Q43_grid_ratio_drop_gap_k67 :
    Q43_grid_ratio Q43_gap_n67_succ < Q43_grid_ratio Q43_gap_n67 := by
  decide

-- Q43.S309-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k68:
-- counterexample inside the gap for k=68.
def Q43_gap_k68 : Nat := 68
def Q43_gap_n68 : Nat := 417402170410649030795
def Q43_gap_n68_succ : Nat := 417402170410649030796

theorem Q43_gap_range_k68 :
    Q43_gap_end_lo_k Q43_gap_k68 <= Q43_gap_n68 ∧
    Q43_gap_end_lo_k Q43_gap_k68 <= Q43_gap_n68_succ ∧
    Q43_gap_n68_succ < Q43_gap_end_hi_k Q43_gap_k68 := by
  decide

theorem Q43_grid_ratio_drop_gap_k68 :
    Q43_grid_ratio Q43_gap_n68_succ < Q43_grid_ratio Q43_gap_n68 := by
  decide

-- Q43.S310-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k69:
-- counterexample inside the gap for k=69.
def Q43_gap_k69 : Nat := 69
def Q43_gap_n69 : Nat := 834804340821298061590
def Q43_gap_n69_succ : Nat := 834804340821298061591

theorem Q43_gap_range_k69 :
    Q43_gap_end_lo_k Q43_gap_k69 <= Q43_gap_n69 ∧
    Q43_gap_end_lo_k Q43_gap_k69 <= Q43_gap_n69_succ ∧
    Q43_gap_n69_succ < Q43_gap_end_hi_k Q43_gap_k69 := by
  decide

theorem Q43_grid_ratio_drop_gap_k69 :
    Q43_grid_ratio Q43_gap_n69_succ < Q43_grid_ratio Q43_gap_n69 := by
  decide

-- Q43.S311-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k70:
-- counterexample inside the gap for k=70.
def Q43_gap_k70 : Nat := 70
def Q43_gap_n70 : Nat := 1669608681642596123180
def Q43_gap_n70_succ : Nat := 1669608681642596123181

theorem Q43_gap_range_k70 :
    Q43_gap_end_lo_k Q43_gap_k70 <= Q43_gap_n70 ∧
    Q43_gap_end_lo_k Q43_gap_k70 <= Q43_gap_n70_succ ∧
    Q43_gap_n70_succ < Q43_gap_end_hi_k Q43_gap_k70 := by
  decide

theorem Q43_grid_ratio_drop_gap_k70 :
    Q43_grid_ratio Q43_gap_n70_succ < Q43_grid_ratio Q43_gap_n70 := by
  decide

-- Q43.S312-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k71:
-- counterexample inside the gap for k=71.
def Q43_gap_k71 : Nat := 71
def Q43_gap_n71 : Nat := 3339217363285192246361
def Q43_gap_n71_succ : Nat := 3339217363285192246362

theorem Q43_gap_range_k71 :
    Q43_gap_end_lo_k Q43_gap_k71 <= Q43_gap_n71 ∧
    Q43_gap_end_lo_k Q43_gap_k71 <= Q43_gap_n71_succ ∧
    Q43_gap_n71_succ < Q43_gap_end_hi_k Q43_gap_k71 := by
  decide

theorem Q43_grid_ratio_drop_gap_k71 :
    Q43_grid_ratio Q43_gap_n71_succ < Q43_grid_ratio Q43_gap_n71 := by
  decide

-- Q43.S313-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k72:
-- counterexample inside the gap for k=72.
def Q43_gap_k72 : Nat := 72
def Q43_gap_n72 : Nat := 6678434726570384492722
def Q43_gap_n72_succ : Nat := 6678434726570384492723

theorem Q43_gap_range_k72 :
    Q43_gap_end_lo_k Q43_gap_k72 <= Q43_gap_n72 ∧
    Q43_gap_end_lo_k Q43_gap_k72 <= Q43_gap_n72_succ ∧
    Q43_gap_n72_succ < Q43_gap_end_hi_k Q43_gap_k72 := by
  decide

theorem Q43_grid_ratio_drop_gap_k72 :
    Q43_grid_ratio Q43_gap_n72_succ < Q43_grid_ratio Q43_gap_n72 := by
  decide

-- Q43.S314-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k73:
-- counterexample inside the gap for k=73.
def Q43_gap_k73 : Nat := 73
def Q43_gap_n73 : Nat := 13356869453140768985445
def Q43_gap_n73_succ : Nat := 13356869453140768985446

theorem Q43_gap_range_k73 :
    Q43_gap_end_lo_k Q43_gap_k73 <= Q43_gap_n73 ∧
    Q43_gap_end_lo_k Q43_gap_k73 <= Q43_gap_n73_succ ∧
    Q43_gap_n73_succ < Q43_gap_end_hi_k Q43_gap_k73 := by
  decide

theorem Q43_grid_ratio_drop_gap_k73 :
    Q43_grid_ratio Q43_gap_n73_succ < Q43_grid_ratio Q43_gap_n73 := by
  decide

-- Q43.S315-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k74:
-- counterexample inside the gap for k=74.
def Q43_gap_k74 : Nat := 74
def Q43_gap_n74 : Nat := 26713738906281537970891
def Q43_gap_n74_succ : Nat := 26713738906281537970892

theorem Q43_gap_range_k74 :
    Q43_gap_end_lo_k Q43_gap_k74 <= Q43_gap_n74 ∧
    Q43_gap_end_lo_k Q43_gap_k74 <= Q43_gap_n74_succ ∧
    Q43_gap_n74_succ < Q43_gap_end_hi_k Q43_gap_k74 := by
  decide

theorem Q43_grid_ratio_drop_gap_k74 :
    Q43_grid_ratio Q43_gap_n74_succ < Q43_grid_ratio Q43_gap_n74 := by
  decide

-- Q43.S316-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k75:
-- counterexample inside the gap for k=75.
def Q43_gap_k75 : Nat := 75
def Q43_gap_n75 : Nat := 53427477812563075941783
def Q43_gap_n75_succ : Nat := 53427477812563075941784

theorem Q43_gap_range_k75 :
    Q43_gap_end_lo_k Q43_gap_k75 <= Q43_gap_n75 ∧
    Q43_gap_end_lo_k Q43_gap_k75 <= Q43_gap_n75_succ ∧
    Q43_gap_n75_succ < Q43_gap_end_hi_k Q43_gap_k75 := by
  decide

theorem Q43_grid_ratio_drop_gap_k75 :
    Q43_grid_ratio Q43_gap_n75_succ < Q43_grid_ratio Q43_gap_n75 := by
  decide

-- Q43.S317-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k76:
-- counterexample inside the gap for k=76.
def Q43_gap_k76 : Nat := 76
def Q43_gap_n76 : Nat := 106854955625126151883567
def Q43_gap_n76_succ : Nat := 106854955625126151883568

theorem Q43_gap_range_k76 :
    Q43_gap_end_lo_k Q43_gap_k76 <= Q43_gap_n76 ∧
    Q43_gap_end_lo_k Q43_gap_k76 <= Q43_gap_n76_succ ∧
    Q43_gap_n76_succ < Q43_gap_end_hi_k Q43_gap_k76 := by
  decide

theorem Q43_grid_ratio_drop_gap_k76 :
    Q43_grid_ratio Q43_gap_n76_succ < Q43_grid_ratio Q43_gap_n76 := by
  decide

-- Q43.S318-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k77:
-- counterexample inside the gap for k=77.
def Q43_gap_k77 : Nat := 77
def Q43_gap_n77 : Nat := 213709911250252303767135
def Q43_gap_n77_succ : Nat := 213709911250252303767136

theorem Q43_gap_range_k77 :
    Q43_gap_end_lo_k Q43_gap_k77 <= Q43_gap_n77 ∧
    Q43_gap_end_lo_k Q43_gap_k77 <= Q43_gap_n77_succ ∧
    Q43_gap_n77_succ < Q43_gap_end_hi_k Q43_gap_k77 := by
  decide

theorem Q43_grid_ratio_drop_gap_k77 :
    Q43_grid_ratio Q43_gap_n77_succ < Q43_grid_ratio Q43_gap_n77 := by
  decide

-- Q43.S319-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k78:
-- counterexample inside the gap for k=78.
def Q43_gap_k78 : Nat := 78
def Q43_gap_n78 : Nat := 427419822500504607534270
def Q43_gap_n78_succ : Nat := 427419822500504607534271

theorem Q43_gap_range_k78 :
    Q43_gap_end_lo_k Q43_gap_k78 <= Q43_gap_n78 ∧
    Q43_gap_end_lo_k Q43_gap_k78 <= Q43_gap_n78_succ ∧
    Q43_gap_n78_succ < Q43_gap_end_hi_k Q43_gap_k78 := by
  decide

theorem Q43_grid_ratio_drop_gap_k78 :
    Q43_grid_ratio Q43_gap_n78_succ < Q43_grid_ratio Q43_gap_n78 := by
  decide

-- Q43.S320-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k79:
-- counterexample inside the gap for k=79.
def Q43_gap_k79 : Nat := 79
def Q43_gap_n79 : Nat := 854839645001009215068541
def Q43_gap_n79_succ : Nat := 854839645001009215068542

theorem Q43_gap_range_k79 :
    Q43_gap_end_lo_k Q43_gap_k79 <= Q43_gap_n79 ∧
    Q43_gap_end_lo_k Q43_gap_k79 <= Q43_gap_n79_succ ∧
    Q43_gap_n79_succ < Q43_gap_end_hi_k Q43_gap_k79 := by
  decide

theorem Q43_grid_ratio_drop_gap_k79 :
    Q43_grid_ratio Q43_gap_n79_succ < Q43_grid_ratio Q43_gap_n79 := by
  decide

-- Q43.S321-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k80:
-- counterexample inside the gap for k=80.
def Q43_gap_k80 : Nat := 80
def Q43_gap_n80 : Nat := 1709679290002018430137083
def Q43_gap_n80_succ : Nat := 1709679290002018430137084

theorem Q43_gap_range_k80 :
    Q43_gap_end_lo_k Q43_gap_k80 <= Q43_gap_n80 ∧
    Q43_gap_end_lo_k Q43_gap_k80 <= Q43_gap_n80_succ ∧
    Q43_gap_n80_succ < Q43_gap_end_hi_k Q43_gap_k80 := by
  decide

theorem Q43_grid_ratio_drop_gap_k80 :
    Q43_grid_ratio Q43_gap_n80_succ < Q43_grid_ratio Q43_gap_n80 := by
  decide

-- Q43.S322-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k81:
-- counterexample inside the gap for k=81.
def Q43_gap_k81 : Nat := 81
def Q43_gap_n81 : Nat := 3419358580004036860274166
def Q43_gap_n81_succ : Nat := 3419358580004036860274167

theorem Q43_gap_range_k81 :
    Q43_gap_end_lo_k Q43_gap_k81 <= Q43_gap_n81 ∧
    Q43_gap_end_lo_k Q43_gap_k81 <= Q43_gap_n81_succ ∧
    Q43_gap_n81_succ < Q43_gap_end_hi_k Q43_gap_k81 := by
  decide

theorem Q43_grid_ratio_drop_gap_k81 :
    Q43_grid_ratio Q43_gap_n81_succ < Q43_grid_ratio Q43_gap_n81 := by
  decide

-- Q43.S323-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k82:
-- counterexample inside the gap for k=82.
def Q43_gap_k82 : Nat := 82
def Q43_gap_n82 : Nat := 6838717160008073720548332
def Q43_gap_n82_succ : Nat := 6838717160008073720548333

theorem Q43_gap_range_k82 :
    Q43_gap_end_lo_k Q43_gap_k82 <= Q43_gap_n82 ∧
    Q43_gap_end_lo_k Q43_gap_k82 <= Q43_gap_n82_succ ∧
    Q43_gap_n82_succ < Q43_gap_end_hi_k Q43_gap_k82 := by
  decide

theorem Q43_grid_ratio_drop_gap_k82 :
    Q43_grid_ratio Q43_gap_n82_succ < Q43_grid_ratio Q43_gap_n82 := by
  decide

-- Q43.S324-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k83:
-- counterexample inside the gap for k=83.
def Q43_gap_k83 : Nat := 83
def Q43_gap_n83 : Nat := 13677434320016147441096664
def Q43_gap_n83_succ : Nat := 13677434320016147441096665

theorem Q43_gap_range_k83 :
    Q43_gap_end_lo_k Q43_gap_k83 <= Q43_gap_n83 ∧
    Q43_gap_end_lo_k Q43_gap_k83 <= Q43_gap_n83_succ ∧
    Q43_gap_n83_succ < Q43_gap_end_hi_k Q43_gap_k83 := by
  decide

theorem Q43_grid_ratio_drop_gap_k83 :
    Q43_grid_ratio Q43_gap_n83_succ < Q43_grid_ratio Q43_gap_n83 := by
  decide

-- Q43.S325-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k84:
-- counterexample inside the gap for k=84.
def Q43_gap_k84 : Nat := 84
def Q43_gap_n84 : Nat := 27354868640032294882193329
def Q43_gap_n84_succ : Nat := 27354868640032294882193330

theorem Q43_gap_range_k84 :
    Q43_gap_end_lo_k Q43_gap_k84 <= Q43_gap_n84 ∧
    Q43_gap_end_lo_k Q43_gap_k84 <= Q43_gap_n84_succ ∧
    Q43_gap_n84_succ < Q43_gap_end_hi_k Q43_gap_k84 := by
  decide

theorem Q43_grid_ratio_drop_gap_k84 :
    Q43_grid_ratio Q43_gap_n84_succ < Q43_grid_ratio Q43_gap_n84 := by
  decide

-- Q43.S326-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k85:
-- counterexample inside the gap for k=85.
def Q43_gap_k85 : Nat := 85
def Q43_gap_n85 : Nat := 54709737280064589764386658
def Q43_gap_n85_succ : Nat := 54709737280064589764386659

theorem Q43_gap_range_k85 :
    Q43_gap_end_lo_k Q43_gap_k85 <= Q43_gap_n85 ∧
    Q43_gap_end_lo_k Q43_gap_k85 <= Q43_gap_n85_succ ∧
    Q43_gap_n85_succ < Q43_gap_end_hi_k Q43_gap_k85 := by
  decide

theorem Q43_grid_ratio_drop_gap_k85 :
    Q43_grid_ratio Q43_gap_n85_succ < Q43_grid_ratio Q43_gap_n85 := by
  decide

-- Q43.S327-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k86:
-- counterexample inside the gap for k=86.
def Q43_gap_k86 : Nat := 86
def Q43_gap_n86 : Nat := 109419474560129179528773316
def Q43_gap_n86_succ : Nat := 109419474560129179528773317

theorem Q43_gap_range_k86 :
    Q43_gap_end_lo_k Q43_gap_k86 <= Q43_gap_n86 ∧
    Q43_gap_end_lo_k Q43_gap_k86 <= Q43_gap_n86_succ ∧
    Q43_gap_n86_succ < Q43_gap_end_hi_k Q43_gap_k86 := by
  decide

theorem Q43_grid_ratio_drop_gap_k86 :
    Q43_grid_ratio Q43_gap_n86_succ < Q43_grid_ratio Q43_gap_n86 := by
  decide

-- Q43.S328-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k87:
-- counterexample inside the gap for k=87.
def Q43_gap_k87 : Nat := 87
def Q43_gap_n87 : Nat := 218838949120258359057546633
def Q43_gap_n87_succ : Nat := 218838949120258359057546634

theorem Q43_gap_range_k87 :
    Q43_gap_end_lo_k Q43_gap_k87 <= Q43_gap_n87 ∧
    Q43_gap_end_lo_k Q43_gap_k87 <= Q43_gap_n87_succ ∧
    Q43_gap_n87_succ < Q43_gap_end_hi_k Q43_gap_k87 := by
  decide

theorem Q43_grid_ratio_drop_gap_k87 :
    Q43_grid_ratio Q43_gap_n87_succ < Q43_grid_ratio Q43_gap_n87 := by
  decide

-- Q43.S329-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k88:
-- counterexample inside the gap for k=88.
def Q43_gap_k88 : Nat := 88
def Q43_gap_n88 : Nat := 437677898240516718115093267
def Q43_gap_n88_succ : Nat := 437677898240516718115093268

theorem Q43_gap_range_k88 :
    Q43_gap_end_lo_k Q43_gap_k88 <= Q43_gap_n88 ∧
    Q43_gap_end_lo_k Q43_gap_k88 <= Q43_gap_n88_succ ∧
    Q43_gap_n88_succ < Q43_gap_end_hi_k Q43_gap_k88 := by
  decide

theorem Q43_grid_ratio_drop_gap_k88 :
    Q43_grid_ratio Q43_gap_n88_succ < Q43_grid_ratio Q43_gap_n88 := by
  decide

-- Q43.S330-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k89:
-- counterexample inside the gap for k=89.
def Q43_gap_k89 : Nat := 89
def Q43_gap_n89 : Nat := 875355796481033436230186534
def Q43_gap_n89_succ : Nat := 875355796481033436230186535

theorem Q43_gap_range_k89 :
    Q43_gap_end_lo_k Q43_gap_k89 <= Q43_gap_n89 ∧
    Q43_gap_end_lo_k Q43_gap_k89 <= Q43_gap_n89_succ ∧
    Q43_gap_n89_succ < Q43_gap_end_hi_k Q43_gap_k89 := by
  decide

theorem Q43_grid_ratio_drop_gap_k89 :
    Q43_grid_ratio Q43_gap_n89_succ < Q43_grid_ratio Q43_gap_n89 := by
  decide

-- Q43.S331-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k90:
-- counterexample inside the gap for k=90.
def Q43_gap_k90 : Nat := 90
def Q43_gap_n90 : Nat := 1750711592962066872460373069
def Q43_gap_n90_succ : Nat := 1750711592962066872460373070

theorem Q43_gap_range_k90 :
    Q43_gap_end_lo_k Q43_gap_k90 <= Q43_gap_n90 ∧
    Q43_gap_end_lo_k Q43_gap_k90 <= Q43_gap_n90_succ ∧
    Q43_gap_n90_succ < Q43_gap_end_hi_k Q43_gap_k90 := by
  decide

theorem Q43_grid_ratio_drop_gap_k90 :
    Q43_grid_ratio Q43_gap_n90_succ < Q43_grid_ratio Q43_gap_n90 := by
  decide

-- Q43.S332-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k91:
-- counterexample inside the gap for k=91.
def Q43_gap_k91 : Nat := 91
def Q43_gap_n91 : Nat := 3501423185924133744920746139
def Q43_gap_n91_succ : Nat := 3501423185924133744920746140

theorem Q43_gap_range_k91 :
    Q43_gap_end_lo_k Q43_gap_k91 <= Q43_gap_n91 ∧
    Q43_gap_end_lo_k Q43_gap_k91 <= Q43_gap_n91_succ ∧
    Q43_gap_n91_succ < Q43_gap_end_hi_k Q43_gap_k91 := by
  decide

theorem Q43_grid_ratio_drop_gap_k91 :
    Q43_grid_ratio Q43_gap_n91_succ < Q43_grid_ratio Q43_gap_n91 := by
  decide

-- Q43.S333-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k92:
-- counterexample inside the gap for k=92.
def Q43_gap_k92 : Nat := 92
def Q43_gap_n92 : Nat := 7002846371848267489841492278
def Q43_gap_n92_succ : Nat := 7002846371848267489841492279

theorem Q43_gap_range_k92 :
    Q43_gap_end_lo_k Q43_gap_k92 <= Q43_gap_n92 ∧
    Q43_gap_end_lo_k Q43_gap_k92 <= Q43_gap_n92_succ ∧
    Q43_gap_n92_succ < Q43_gap_end_hi_k Q43_gap_k92 := by
  decide

theorem Q43_grid_ratio_drop_gap_k92 :
    Q43_grid_ratio Q43_gap_n92_succ < Q43_grid_ratio Q43_gap_n92 := by
  decide

-- Q43.S334-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k93:
-- counterexample inside the gap for k=93.
def Q43_gap_k93 : Nat := 93
def Q43_gap_n93 : Nat := 14005692743696534979682984556
def Q43_gap_n93_succ : Nat := 14005692743696534979682984557

theorem Q43_gap_range_k93 :
    Q43_gap_end_lo_k Q43_gap_k93 <= Q43_gap_n93 ∧
    Q43_gap_end_lo_k Q43_gap_k93 <= Q43_gap_n93_succ ∧
    Q43_gap_n93_succ < Q43_gap_end_hi_k Q43_gap_k93 := by
  decide

theorem Q43_grid_ratio_drop_gap_k93 :
    Q43_grid_ratio Q43_gap_n93_succ < Q43_grid_ratio Q43_gap_n93 := by
  decide

-- Q43.S335-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k94:
-- counterexample inside the gap for k=94.
def Q43_gap_k94 : Nat := 94
def Q43_gap_n94 : Nat := 28011385487393069959365969113
def Q43_gap_n94_succ : Nat := 28011385487393069959365969114

theorem Q43_gap_range_k94 :
    Q43_gap_end_lo_k Q43_gap_k94 <= Q43_gap_n94 ∧
    Q43_gap_end_lo_k Q43_gap_k94 <= Q43_gap_n94_succ ∧
    Q43_gap_n94_succ < Q43_gap_end_hi_k Q43_gap_k94 := by
  decide

theorem Q43_grid_ratio_drop_gap_k94 :
    Q43_grid_ratio Q43_gap_n94_succ < Q43_grid_ratio Q43_gap_n94 := by
  decide

-- Q43.S336-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k95:
-- counterexample inside the gap for k=95.
def Q43_gap_k95 : Nat := 95
def Q43_gap_n95 : Nat := 56022770974786139918731938227
def Q43_gap_n95_succ : Nat := 56022770974786139918731938228

theorem Q43_gap_range_k95 :
    Q43_gap_end_lo_k Q43_gap_k95 <= Q43_gap_n95 ∧
    Q43_gap_end_lo_k Q43_gap_k95 <= Q43_gap_n95_succ ∧
    Q43_gap_n95_succ < Q43_gap_end_hi_k Q43_gap_k95 := by
  decide

theorem Q43_grid_ratio_drop_gap_k95 :
    Q43_grid_ratio Q43_gap_n95_succ < Q43_grid_ratio Q43_gap_n95 := by
  decide

-- Q43.S337-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k96:
-- counterexample inside the gap for k=96.
def Q43_gap_k96 : Nat := 96
def Q43_gap_n96 : Nat := 112045541949572279837463876454
def Q43_gap_n96_succ : Nat := 112045541949572279837463876455

theorem Q43_gap_range_k96 :
    Q43_gap_end_lo_k Q43_gap_k96 <= Q43_gap_n96 ∧
    Q43_gap_end_lo_k Q43_gap_k96 <= Q43_gap_n96_succ ∧
    Q43_gap_n96_succ < Q43_gap_end_hi_k Q43_gap_k96 := by
  decide

theorem Q43_grid_ratio_drop_gap_k96 :
    Q43_grid_ratio Q43_gap_n96_succ < Q43_grid_ratio Q43_gap_n96 := by
  decide

-- Q43.S338-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k97:
-- counterexample inside the gap for k=97.
def Q43_gap_k97 : Nat := 97
def Q43_gap_n97 : Nat := 224091083899144559674927752909
def Q43_gap_n97_succ : Nat := 224091083899144559674927752910

theorem Q43_gap_range_k97 :
    Q43_gap_end_lo_k Q43_gap_k97 <= Q43_gap_n97 ∧
    Q43_gap_end_lo_k Q43_gap_k97 <= Q43_gap_n97_succ ∧
    Q43_gap_n97_succ < Q43_gap_end_hi_k Q43_gap_k97 := by
  decide

theorem Q43_grid_ratio_drop_gap_k97 :
    Q43_grid_ratio Q43_gap_n97_succ < Q43_grid_ratio Q43_gap_n97 := by
  decide

-- Q43.S339-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k98:
-- counterexample inside the gap for k=98.
def Q43_gap_k98 : Nat := 98
def Q43_gap_n98 : Nat := 448182167798289119349855505819
def Q43_gap_n98_succ : Nat := 448182167798289119349855505820

theorem Q43_gap_range_k98 :
    Q43_gap_end_lo_k Q43_gap_k98 <= Q43_gap_n98 ∧
    Q43_gap_end_lo_k Q43_gap_k98 <= Q43_gap_n98_succ ∧
    Q43_gap_n98_succ < Q43_gap_end_hi_k Q43_gap_k98 := by
  decide

theorem Q43_grid_ratio_drop_gap_k98 :
    Q43_grid_ratio Q43_gap_n98_succ < Q43_grid_ratio Q43_gap_n98 := by
  decide

-- Q43.S340-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k99:
-- counterexample inside the gap for k=99.
def Q43_gap_k99 : Nat := 99
def Q43_gap_n99 : Nat := 896364335596578238699711011639
def Q43_gap_n99_succ : Nat := 896364335596578238699711011640

theorem Q43_gap_range_k99 :
    Q43_gap_end_lo_k Q43_gap_k99 <= Q43_gap_n99 ∧
    Q43_gap_end_lo_k Q43_gap_k99 <= Q43_gap_n99_succ ∧
    Q43_gap_n99_succ < Q43_gap_end_hi_k Q43_gap_k99 := by
  decide

theorem Q43_grid_ratio_drop_gap_k99 :
    Q43_grid_ratio Q43_gap_n99_succ < Q43_grid_ratio Q43_gap_n99 := by
  decide

-- Q43.S341-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k100:
-- counterexample inside the gap for k=100.
def Q43_gap_k100 : Nat := 100
def Q43_gap_n100 : Nat := 1792728671193156477399422023278
def Q43_gap_n100_succ : Nat := 1792728671193156477399422023279

theorem Q43_gap_range_k100 :
    Q43_gap_end_lo_k Q43_gap_k100 <= Q43_gap_n100 ∧
    Q43_gap_end_lo_k Q43_gap_k100 <= Q43_gap_n100_succ ∧
    Q43_gap_n100_succ < Q43_gap_end_hi_k Q43_gap_k100 := by
  decide

theorem Q43_grid_ratio_drop_gap_k100 :
    Q43_grid_ratio Q43_gap_n100_succ < Q43_grid_ratio Q43_gap_n100 := by
  decide

-- Q43.S342-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k101:
-- counterexample inside the gap for k=101.
def Q43_gap_k101 : Nat := 101
def Q43_gap_n101 : Nat := 3585457342386312954798844046557
def Q43_gap_n101_succ : Nat := 3585457342386312954798844046558

theorem Q43_gap_range_k101 :
    Q43_gap_end_lo_k Q43_gap_k101 <= Q43_gap_n101 ∧
    Q43_gap_end_lo_k Q43_gap_k101 <= Q43_gap_n101_succ ∧
    Q43_gap_n101_succ < Q43_gap_end_hi_k Q43_gap_k101 := by
  decide

theorem Q43_grid_ratio_drop_gap_k101 :
    Q43_grid_ratio Q43_gap_n101_succ < Q43_grid_ratio Q43_gap_n101 := by
  decide

-- Q43.S343-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k102:
-- counterexample inside the gap for k=102.
def Q43_gap_k102 : Nat := 102
def Q43_gap_n102 : Nat := 7170914684772625909597688093114
def Q43_gap_n102_succ : Nat := 7170914684772625909597688093115

theorem Q43_gap_range_k102 :
    Q43_gap_end_lo_k Q43_gap_k102 <= Q43_gap_n102 ∧
    Q43_gap_end_lo_k Q43_gap_k102 <= Q43_gap_n102_succ ∧
    Q43_gap_n102_succ < Q43_gap_end_hi_k Q43_gap_k102 := by
  decide

theorem Q43_grid_ratio_drop_gap_k102 :
    Q43_grid_ratio Q43_gap_n102_succ < Q43_grid_ratio Q43_gap_n102 := by
  decide

-- Q43.S344-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k103:
-- counterexample inside the gap for k=103.
def Q43_gap_k103 : Nat := 103
def Q43_gap_n103 : Nat := 14341829369545251819195376186229
def Q43_gap_n103_succ : Nat := 14341829369545251819195376186230

theorem Q43_gap_range_k103 :
    Q43_gap_end_lo_k Q43_gap_k103 <= Q43_gap_n103 ∧
    Q43_gap_end_lo_k Q43_gap_k103 <= Q43_gap_n103_succ ∧
    Q43_gap_n103_succ < Q43_gap_end_hi_k Q43_gap_k103 := by
  decide

theorem Q43_grid_ratio_drop_gap_k103 :
    Q43_grid_ratio Q43_gap_n103_succ < Q43_grid_ratio Q43_gap_n103 := by
  decide

-- Q43.S345-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k104:
-- counterexample inside the gap for k=104.
def Q43_gap_k104 : Nat := 104
def Q43_gap_n104 : Nat := 28683658739090503638390752372458
def Q43_gap_n104_succ : Nat := 28683658739090503638390752372459

theorem Q43_gap_range_k104 :
    Q43_gap_end_lo_k Q43_gap_k104 <= Q43_gap_n104 ∧
    Q43_gap_end_lo_k Q43_gap_k104 <= Q43_gap_n104_succ ∧
    Q43_gap_n104_succ < Q43_gap_end_hi_k Q43_gap_k104 := by
  decide

theorem Q43_grid_ratio_drop_gap_k104 :
    Q43_grid_ratio Q43_gap_n104_succ < Q43_grid_ratio Q43_gap_n104 := by
  decide

-- Q43.S250-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-alternative:
-- toy check: ratio at the gap endpoints (k=12) does not drop.
def Q43_gap_end_lo : Nat := Q43_gap_end_lo_k Q43_gap_k
def Q43_gap_end_hi : Nat := Q43_gap_end_hi_k Q43_gap_k

theorem Q43_gap_end_ratio_le :
    Q43_grid_ratio Q43_gap_end_lo <= Q43_grid_ratio Q43_gap_end_hi := by
  decide

-- Q43.S251-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-bound:
-- toy scan over the gap [5*2^(k-2), 3*2^(k-1)) for k=12 to get a uniform lower bound.
def Q43_gap_range_list : List Nat := Q43_gap_range_list_k Q43_gap_k

def Q43_gap_min_ratio : Nat := Q43_gap_min_ratio_k Q43_gap_k Q43_gap_n_succ

-- `decide` recurses through the 1024-element gap list; bump recursion depth locally.
set_option maxRecDepth 8000 in
theorem Q43_gap_min_ratio_le_all :
    ∀ n, n ∈ Q43_gap_range_list → Q43_gap_min_ratio <= Q43_grid_ratio n := by
  decide

-- Q43.S267-log2-jump-lemma:
-- log2 jump from explicit bounds on n^2 and (n+1)^2.
theorem Q43_log2_grid_size_eq_of_bounds {n k : Nat} (hn : 0 < n)
    (hlow : 2 ^ (2 * k) <= Q43_grid_size n)
    (hhigh : Q43_grid_size n < 2 ^ (2 * k + 1)) :
    Nat.log2 (Q43_grid_size n) = 2 * k := by
  have hnne : n ≠ 0 := Nat.ne_of_gt hn
  have hne : Q43_grid_size n ≠ 0 := by
    simpa [Q43_grid_size] using (Nat.mul_ne_zero hnne hnne)
  exact (Nat.log2_eq_iff hne).2 ⟨hlow, hhigh⟩

theorem Q43_log2_grid_size_eq_succ_of_bounds {n k : Nat}
    (hlow : 2 ^ (2 * k + 1) <= Q43_grid_size (n + 1))
    (hhigh : Q43_grid_size (n + 1) < 2 ^ (2 * k + 2)) :
    Nat.log2 (Q43_grid_size (n + 1)) = 2 * k + 1 := by
  have hpos : n + 1 ≠ 0 := Nat.succ_ne_zero n
  have hne : Q43_grid_size (n + 1) ≠ 0 := by
    simpa [Q43_grid_size] using (Nat.mul_ne_zero hpos hpos)
  exact (Nat.log2_eq_iff hne).2 ⟨hlow, hhigh⟩

theorem Q43_log2_grid_size_jump {n k : Nat} (hn : 0 < n)
    (hlow : 2 ^ (2 * k) <= Q43_grid_size n)
    (hhigh : Q43_grid_size n < 2 ^ (2 * k + 1))
    (hlow' : 2 ^ (2 * k + 1) <= Q43_grid_size (n + 1))
    (hhigh' : Q43_grid_size (n + 1) < 2 ^ (2 * k + 2)) :
    Nat.log2 (Q43_grid_size n) = 2 * k ∧
      Nat.log2 (Q43_grid_size (n + 1)) = 2 * k + 1 := by
  refine ⟨Q43_log2_grid_size_eq_of_bounds (n:=n) (k:=k) hn hlow hhigh, ?_⟩
  exact Q43_log2_grid_size_eq_succ_of_bounds (n:=n) (k:=k) hlow' hhigh'

-- Q43.S269-define-floor-sqrt-lean:
-- floor-sqrt defined via the minimal m with n < (m+1)^2.
theorem Q43_exists_sq_upper (n : Nat) : ∃ m, n < (m + 1) ^ 2 := by
  refine ⟨n, ?_⟩
  have hlt : n < n + 1 := Nat.lt_succ_self n
  have hpos : 1 <= n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hmul : n + 1 <= (n + 1) * (n + 1) := by
    simpa [Nat.mul_one] using (Nat.mul_le_mul_left (n + 1) hpos)
  have hlt' : n < (n + 1) * (n + 1) := Nat.lt_of_lt_of_le hlt hmul
  simpa [Nat.pow_two] using hlt'

def Q43_floorSqrt : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let m := Q43_floorSqrt n
      if _ : (m + 1) ^ 2 <= n + 1 then m + 1 else m

-- Q43.S270-floor-sqrt-lower-bound:
theorem Q43_floorSqrt_lower (n : Nat) : (Q43_floorSqrt n) ^ 2 <= n := by
  induction n with
  | zero =>
      simp [Q43_floorSqrt]
  | succ n ih =>
      by_cases h : (Q43_floorSqrt n + 1) ^ 2 <= n + 1
      · simp [Q43_floorSqrt, h]
      ·
        have hle : (Q43_floorSqrt n) ^ 2 <= n + 1 :=
          Nat.le_trans ih (Nat.le_succ n)
        simpa [Q43_floorSqrt, h] using hle

theorem Q43_floorSqrt_upper (n : Nat) : n < (Q43_floorSqrt n + 1) ^ 2 := by
  induction n with
  | zero =>
      simp [Q43_floorSqrt]
  | succ n ih =>
      by_cases h : (Q43_floorSqrt n + 1) ^ 2 <= n + 1
      ·
        have hle : n + 1 <= (Q43_floorSqrt n + 1) ^ 2 :=
          (Nat.succ_le_iff).mpr ih
        have h_eq : n + 1 = (Q43_floorSqrt n + 1) ^ 2 :=
          Nat.le_antisymm hle h
        have hlt : (Q43_floorSqrt n + 1) ^ 2 < (Q43_floorSqrt n + 2) ^ 2 :=
          Nat.pow_lt_pow_left (Nat.lt_succ_self (Q43_floorSqrt n + 1)) (by decide)
        have h' : n + 1 < (Q43_floorSqrt n + 2) ^ 2 := by
          simpa [h_eq] using hlt
        simpa [Q43_floorSqrt, h] using h'
      ·
        have hlt : n + 1 < (Q43_floorSqrt n + 1) ^ 2 :=
          Nat.lt_of_not_ge h
        simpa [Q43_floorSqrt, h] using hlt

theorem Q43_floorSqrt_bounds (n : Nat) :
    (Q43_floorSqrt n) ^ 2 <= n ∧ n < (Q43_floorSqrt n + 1) ^ 2 := by
  exact ⟨Q43_floorSqrt_lower n, Q43_floorSqrt_upper n⟩

-- Q43.S273-log2-jump-nk:
-- define n_k via floor sqrt and show the log2 jump at n_k^2 (k>=1).
theorem Q43_le_floorSqrt_of_sq_le {n m : Nat} (h : m ^ 2 <= n) :
    m <= Q43_floorSqrt n := by
  by_cases hle : m <= Q43_floorSqrt n
  · exact hle
  ·
    have hlt : Q43_floorSqrt n < m := Nat.lt_of_not_ge hle
    have hle' : Q43_floorSqrt n + 1 <= m := (Nat.succ_le_iff).2 hlt
    have hpow : (Q43_floorSqrt n + 1) ^ 2 <= m ^ 2 := Q43_pow_le_pow_of_le hle'
    have hpow' : (Q43_floorSqrt n + 1) ^ 2 <= n := Nat.le_trans hpow h
    have hupper : n < (Q43_floorSqrt n + 1) ^ 2 := Q43_floorSqrt_upper n
    have hcontr : (Q43_floorSqrt n + 1) ^ 2 < (Q43_floorSqrt n + 1) ^ 2 :=
      Nat.lt_of_le_of_lt hpow' hupper
    exact (False.elim (Nat.lt_irrefl _ hcontr))

theorem Q43_floorSqrt_lt_of_lt_sq {n b : Nat} (h : n < b ^ 2) :
    Q43_floorSqrt n < b := by
  by_cases hle : b <= Q43_floorSqrt n
  ·
    have hpow : b ^ 2 <= (Q43_floorSqrt n) ^ 2 := Q43_pow_le_pow_of_le hle
    have hlow : (Q43_floorSqrt n) ^ 2 <= n := Q43_floorSqrt_lower n
    have hle' : b ^ 2 <= n := Nat.le_trans hpow hlow
    have hcontr : b ^ 2 < b ^ 2 := Nat.lt_of_le_of_lt hle' h
    exact (False.elim (Nat.lt_irrefl _ hcontr))
  ·
    exact Nat.lt_of_not_ge hle

theorem Q43_pow_le_pow_succ_sub_one (k : Nat) :
    2 ^ (2 * k) <= 2 ^ (2 * k + 1) - 1 := by
  have hpos : 1 <= 2 ^ (2 * k) := by
    have hpos' : 0 < 2 ^ (2 * k) := Nat.pow_pos (by decide)
    exact (Nat.succ_le_iff).2 hpos'
  have hle_add : 2 ^ (2 * k) + 1 <= 2 ^ (2 * k) + 2 ^ (2 * k) :=
    Nat.add_le_add_left hpos _
  have hle_mul : 2 ^ (2 * k) + 1 <= 2 * 2 ^ (2 * k) := by
    simpa [Nat.two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hle_add
  have hpow_succ : 2 * 2 ^ (2 * k) = 2 ^ (2 * k + 1) := by
    calc
      2 * 2 ^ (2 * k) = 2 ^ (2 * k) * 2 := by
        simp [Nat.mul_comm]
      _ = 2 ^ (2 * k + 1) := by
        simpa using (Nat.pow_succ 2 (2 * k)).symm
  have hle_succ : 2 ^ (2 * k) + 1 <= 2 ^ (2 * k + 1) := by
    simpa [hpow_succ] using hle_mul
  have hlt : 2 ^ (2 * k) < 2 ^ (2 * k + 1) := by
    have hstep : 2 ^ (2 * k) < 2 ^ (2 * k) + 1 := Nat.lt_succ_self _
    exact Nat.lt_of_lt_of_le hstep hle_succ
  exact Nat.le_sub_one_of_lt hlt

def Q43_nk (k : Nat) : Nat := Q43_floorSqrt (2 ^ (2 * k + 1) - 1)

theorem Q43_nk_sq_le (k : Nat) :
    (Q43_nk k) ^ 2 <= 2 ^ (2 * k + 1) - 1 := by
  simpa [Q43_nk] using (Q43_floorSqrt_lower (2 ^ (2 * k + 1) - 1))

theorem Q43_nk_sq_lt (k : Nat) :
    (Q43_nk k) ^ 2 < 2 ^ (2 * k + 1) := by
  have hle : (Q43_nk k) ^ 2 <= 2 ^ (2 * k + 1) - 1 := Q43_nk_sq_le k
  have hpos : 1 <= 2 ^ (2 * k + 1) := by
    have hpos' : 0 < 2 ^ (2 * k + 1) := Nat.pow_pos (by decide)
    exact (Nat.succ_le_iff).2 hpos'
  have hsum : 2 ^ (2 * k + 1) - 1 + 1 = 2 ^ (2 * k + 1) := Nat.sub_add_cancel hpos
  have hlt : 2 ^ (2 * k + 1) - 1 < 2 ^ (2 * k + 1) := by
    have h := Nat.lt_succ_self (2 ^ (2 * k + 1) - 1)
    simpa [hsum] using h
  exact Nat.lt_of_le_of_lt hle hlt

theorem Q43_nk_ge_pow (k : Nat) : 2 ^ k <= Q43_nk k := by
  have hpow2 : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by
    simpa [Nat.mul_comm] using (Nat.pow_mul 2 k 2).symm
  have hle : (2 ^ k) ^ 2 <= 2 ^ (2 * k + 1) - 1 := by
    have hle' : 2 ^ (2 * k) <= 2 ^ (2 * k + 1) - 1 :=
      Q43_pow_le_pow_succ_sub_one k
    simpa [hpow2] using hle'
  exact Q43_le_floorSqrt_of_sq_le (n:=2 ^ (2 * k + 1) - 1) (m:=2 ^ k) hle

theorem Q43_nk_sq_ge (k : Nat) :
    2 ^ (2 * k) <= (Q43_nk k) ^ 2 := by
  have hle : 2 ^ k <= Q43_nk k := Q43_nk_ge_pow k
  have hpow : (2 ^ k) ^ 2 <= (Q43_nk k) ^ 2 := Q43_pow_le_pow_of_le hle
  have hpow2 : 2 ^ (2 * k) = (2 ^ k) ^ 2 := by
    simpa [Nat.mul_comm] using (Nat.pow_mul 2 k 2)
  simpa [hpow2] using hpow

theorem Q43_nk_succ_sq_ge (k : Nat) :
    2 ^ (2 * k + 1) <= (Q43_nk k + 1) ^ 2 := by
  have hupper : 2 ^ (2 * k + 1) - 1 < (Q43_nk k + 1) ^ 2 := by
    simpa [Q43_nk] using (Q43_floorSqrt_upper (2 ^ (2 * k + 1) - 1))
  have hpos : 1 <= 2 ^ (2 * k + 1) := by
    have hpos' : 0 < 2 ^ (2 * k + 1) := Nat.pow_pos (by decide)
    exact (Nat.succ_le_iff).2 hpos'
  have hsum : 2 ^ (2 * k + 1) - 1 + 1 = 2 ^ (2 * k + 1) := Nat.sub_add_cancel hpos
  have hle : 2 ^ (2 * k + 1) - 1 + 1 <= (Q43_nk k + 1) ^ 2 :=
    (Nat.succ_le_iff).2 hupper
  simpa [hsum] using hle

theorem Q43_nk_succ_sq_lt {k : Nat} (hk : 1 <= k) :
    (Q43_nk k + 1) ^ 2 < 2 ^ (2 * k + 2) := by
  let t : Nat := 2 ^ (k - 1)
  have htpos : 0 < t := by
    simpa [t] using (Nat.pow_pos (by decide) : 0 < 2 ^ (k - 1))
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hpowt : 2 ^ (2 * (k - 1)) = t * t := by
    have hpow' : 2 ^ ((k - 1) * 2) = (2 ^ (k - 1)) ^ 2 := Nat.pow_mul 2 (k - 1) 2
    simpa [t, Nat.mul_comm, Nat.pow_two] using hpow'
  have hexp : 2 * (k - 1) + 3 = 2 * k + 1 := by
    calc
      2 * (k - 1) + 3 = (2 * (k - 1) + 2) + 1 := by
        simp [Nat.add_assoc]
      _ = 2 * ((k - 1) + 1) + 1 := by
        simp [Nat.mul_add, Nat.add_assoc]
      _ = 2 * k + 1 := by
        simp [hk1]
  have hpow8 : 2 ^ (2 * k + 1) = 8 * t * t := by
    calc
      2 ^ (2 * k + 1) = 2 ^ (2 * (k - 1) + 3) := by
        simp [hexp]
      _ = 2 ^ (2 * (k - 1)) * 2 ^ 3 := by
        simp [Nat.pow_add]
      _ = (t * t) * 8 := by
        simp [hpowt]
      _ = 8 * t * t := by
        simp [Nat.mul_comm, Nat.mul_assoc]
  have hpow3 : (3 * t) ^ 2 = 9 * t * t := by
    simp [Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm]
  have hcoeff : 8 <= 9 := by decide
  have hmul : 8 * t * t <= 9 * t * t := by
    have hmul' : 8 * (t * t) <= 9 * (t * t) := Nat.mul_le_mul_right _ hcoeff
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul'
  have hle_pow : 2 ^ (2 * k + 1) <= (3 * t) ^ 2 := by
    calc
      2 ^ (2 * k + 1) = 8 * t * t := hpow8
      _ <= 9 * t * t := hmul
      _ = (3 * t) ^ 2 := hpow3.symm
  have hpos_pow : 1 <= 2 ^ (2 * k + 1) := by
    have hpos' : 0 < 2 ^ (2 * k + 1) := Nat.pow_pos (by decide)
    exact (Nat.succ_le_iff).2 hpos'
  have hlt_pow : 2 ^ (2 * k + 1) - 1 < (3 * t) ^ 2 := by
    have hlt : 2 ^ (2 * k + 1) - 1 < 2 ^ (2 * k + 1) := by
      have hsum : 2 ^ (2 * k + 1) - 1 + 1 = 2 ^ (2 * k + 1) :=
        Nat.sub_add_cancel hpos_pow
      have h := Nat.lt_succ_self (2 ^ (2 * k + 1) - 1)
      simpa [hsum] using h
    exact Nat.lt_of_lt_of_le hlt hle_pow
  have hnk_lt : Q43_nk k < 3 * t :=
    Q43_floorSqrt_lt_of_lt_sq (n:=2 ^ (2 * k + 1) - 1) (b:=3 * t) hlt_pow
  have hnk_succ_le : Q43_nk k + 1 <= 3 * t := (Nat.succ_le_iff).2 hnk_lt
  have hpow_succ : (Q43_nk k + 1) ^ 2 <= (3 * t) ^ 2 :=
    Q43_pow_le_pow_of_le hnk_succ_le
  have hexp2 : 2 * (k - 1) + 4 = 2 * k + 2 := by
    calc
      2 * (k - 1) + 4 = (2 * (k - 1) + 2) + 2 := by
        simp [Nat.add_assoc]
      _ = 2 * ((k - 1) + 1) + 2 := by
        simp [Nat.mul_add, Nat.add_assoc]
      _ = 2 * k + 2 := by
        simp [hk1]
  have hpow16 : 2 ^ (2 * k + 2) = 16 * t * t := by
    calc
      2 ^ (2 * k + 2) = 2 ^ (2 * (k - 1) + 4) := by
        simp [hexp2]
      _ = 2 ^ (2 * (k - 1)) * 2 ^ 4 := by
        simp [Nat.pow_add]
      _ = (t * t) * 16 := by
        simp [hpowt]
      _ = 16 * t * t := by
        simp [Nat.mul_comm, Nat.mul_assoc]
  have hcoeff' : 9 < 16 := by decide
  have hmul' : 9 * t * t < 16 * t * t := by
    have htpos2 : 0 < t * t := Nat.mul_pos htpos htpos
    have hmul'' : 9 * (t * t) < 16 * (t * t) :=
      (Nat.mul_lt_mul_right (a0 := htpos2)).2 hcoeff'
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul''
  have hlt_pow2 : (3 * t) ^ 2 < 2 ^ (2 * k + 2) := by
    calc
      (3 * t) ^ 2 = 9 * t * t := hpow3
      _ < 16 * t * t := hmul'
      _ = 2 ^ (2 * k + 2) := hpow16.symm
  exact Nat.lt_of_le_of_lt hpow_succ hlt_pow2

theorem Q43_log2_jump_nk {k : Nat} (hk : 1 <= k) :
    Nat.log2 ((Q43_nk k) ^ 2) = 2 * k ∧
      Nat.log2 ((Q43_nk k + 1) ^ 2) = 2 * k + 1 := by
  have hlow : 2 ^ (2 * k) <= (Q43_nk k) ^ 2 := Q43_nk_sq_ge k
  have hhigh : (Q43_nk k) ^ 2 < 2 ^ (2 * k + 1) := Q43_nk_sq_lt k
  have hlow' : 2 ^ (2 * k + 1) <= (Q43_nk k + 1) ^ 2 := Q43_nk_succ_sq_ge k
  have hhigh' : (Q43_nk k + 1) ^ 2 < 2 ^ (2 * k + 2) :=
    Q43_nk_succ_sq_lt (k:=k) hk
  have hnpos : 0 < Q43_nk k := by
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    exact Nat.lt_of_lt_of_le hpos (Q43_nk_ge_pow k)
  have hlog := Q43_log2_grid_size_jump (n:=Q43_nk k) (k:=k) hnpos
    (by simpa [Q43_grid_size, Nat.pow_two] using hlow)
    (by simpa [Q43_grid_size, Nat.pow_two] using hhigh)
    (by simpa [Q43_grid_size, Nat.pow_two] using hlow')
    (by simpa [Q43_grid_size, Nat.pow_two] using hhigh')
  simpa [Q43_grid_size, Nat.pow_two] using hlog

-- Q43.S274-gap-drop-from-jump:
-- connect the canonical log2 jump point `n_k` with the existing gap-drop counterexamples (k=12..25).
theorem Q43_floorSqrt_eq_of_sq_bounds {n m : Nat}
    (hlow : m ^ 2 <= n) (hhigh : n < (m + 1) ^ 2) : Q43_floorSqrt n = m := by
  apply Nat.le_antisymm
  ·
    have hlt : Q43_floorSqrt n < m + 1 :=
      Q43_floorSqrt_lt_of_lt_sq (n:=n) (b:=m + 1) (by simpa using hhigh)
    exact (Nat.lt_succ_iff).1 hlt
  · exact Q43_le_floorSqrt_of_sq_le (n:=n) (m:=m) hlow

theorem Q43_nk_eq_gap_n12 : Q43_nk 12 = Q43_gap_n := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 12 + 1) - 1) (m:=Q43_gap_n) (by decide) (by decide)

-- Q43.S276-gap-drop-nk-uniform-kge12:
-- replace the k-list bridge with a uniform lemma: the ratio drops at the log2-jump point n_k.
theorem Q43_nk_lt_pow_succ (k : Nat) : Q43_nk k < 2 ^ (k + 1) := by
  unfold Q43_nk
  have hlt' : 2 ^ (2 * k + 1) - 1 < 2 ^ (2 * k + 2) := by
    have hpos : 0 < 2 ^ (2 * k + 1) := Nat.pow_pos (by decide)
    have hsub : 2 ^ (2 * k + 1) - 1 < 2 ^ (2 * k + 1) :=
      Nat.sub_lt_of_pos_le (a := 1) (b := 2 ^ (2 * k + 1)) (by decide) (Nat.succ_le_iff.2 hpos)
    have hle : 2 ^ (2 * k + 1) <= 2 ^ (2 * k + 2) :=
      Nat.pow_le_pow_of_le (a := 2) (h := by decide) (Nat.le_succ _)
    exact Nat.lt_of_lt_of_le hsub hle
  have hpow : (2 ^ (k + 1)) ^ 2 = 2 ^ (2 * k + 2) := by
    have hpow' : 2 ^ ((k + 1) * 2) = (2 ^ (k + 1)) ^ 2 := Nat.pow_mul 2 (k + 1) 2
    calc
      (2 ^ (k + 1)) ^ 2 = 2 ^ ((k + 1) * 2) := by
        symm
        exact hpow'
      _ = 2 ^ (2 * k + 2) := by
        simp [Nat.add_mul, Nat.mul_comm]
  have hlt : 2 ^ (2 * k + 1) - 1 < (2 ^ (k + 1)) ^ 2 := by
    simpa [hpow] using hlt'
  exact Q43_floorSqrt_lt_of_lt_sq (n := 2 ^ (2 * k + 1) - 1) (b := 2 ^ (k + 1)) hlt

theorem Q43_two_nk_add_one_le_pow (k : Nat) : 2 * Q43_nk k + 1 <= 2 ^ (k + 2) := by
  have hle_succ : Q43_nk k + 1 <= 2 ^ (k + 1) := (Nat.succ_le_iff).2 (Q43_nk_lt_pow_succ k)
  have hmul : 2 * (Q43_nk k + 1) <= 2 * (2 ^ (k + 1)) := Nat.mul_le_mul_left 2 hle_succ
  have hmul' : 2 * Q43_nk k + 2 <= 2 ^ (k + 2) := by
    simpa [Nat.mul_add, Nat.add_assoc, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact Nat.le_trans (Nat.le_succ _) hmul'

theorem Q43_nk_sq_ge_pow_sub (k : Nat) :
    2 ^ (2 * k + 1) - 2 ^ (k + 2) <= (Q43_nk k) ^ 2 := by
  have hlow : 2 ^ (2 * k + 1) <= (Q43_nk k + 1) ^ 2 := Q43_nk_succ_sq_ge k
  have hle : 2 ^ (2 * k + 1) <= (Q43_nk k) ^ 2 + 2 ^ (k + 2) := by
    have hsq : (Q43_nk k + 1) ^ 2 = (Q43_nk k) ^ 2 + (2 * Q43_nk k + 1) := by
      simp [Nat.pow_two, Nat.mul_add, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        Nat.two_mul]
    have h2 : (Q43_nk k) ^ 2 + (2 * Q43_nk k + 1) <= (Q43_nk k) ^ 2 + 2 ^ (k + 2) :=
      Nat.add_le_add_left (Q43_two_nk_add_one_le_pow k) _
    have hstep : (Q43_nk k + 1) ^ 2 <= (Q43_nk k) ^ 2 + 2 ^ (k + 2) := by
      simpa [hsq] using h2
    exact Nat.le_trans hlow hstep
  exact (Nat.sub_le_iff_le_add).2 hle

theorem Q43_pow6_succ_le_mul4 (k : Nat) (hk : 4 <= k) :
    (2 * (k + 1) + 1) ^ 6 <= 4 * (2 * k + 1) ^ 6 := by
  have h7 : 7 <= 2 * k := by
    have h8 : 8 <= 2 * k := by
      have h := Nat.mul_le_mul_left 2 hk
      simpa using h
    exact Nat.le_trans (by decide : 7 <= 8) h8
  have hmul4 : 4 * (2 * k + 3) <= 5 * (2 * k + 1) := by
    have h12 : 12 <= 2 * k + 5 := Nat.add_le_add_right h7 5
    have h' : 8 * k + 12 <= 8 * k + (2 * k + 5) := Nat.add_le_add_left h12 (8 * k)
    have h'' : 4 * (2 * k + 3) <= 8 * k + 12 := by
      simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm]
    have h''' : 8 * k + (2 * k + 5) = 5 * (2 * k + 1) := by
      omega
    exact Nat.le_trans h'' (by simpa [h'''] using h')
  have hpow :
      (4 * (2 * k + 3)) ^ 6 <= (5 * (2 * k + 1)) ^ 6 :=
    Q43_pow_le_pow_of_le hmul4
  have hpow' : 4096 * (2 * k + 3) ^ 6 <= 15625 * (2 * k + 1) ^ 6 := by
    simpa [Nat.mul_pow, Nat.pow_succ, Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpow
  have hcoeff : 15625 <= 16384 := by decide
  have hpow'' : 4096 * (2 * k + 3) ^ 6 <= 16384 * (2 * k + 1) ^ 6 :=
    Nat.le_trans hpow' (Nat.mul_le_mul_right _ hcoeff)
  have hpow4 : 16384 * (2 * k + 1) ^ 6 = 4096 * (4 * (2 * k + 1) ^ 6) := by
    have hconst : 16384 = 4096 * 4 := by decide
    calc
      16384 * (2 * k + 1) ^ 6 = (4096 * 4) * (2 * k + 1) ^ 6 := by
        simp [hconst]
      _ = 4096 * (4 * (2 * k + 1) ^ 6) := by
        ac_rfl
  have hfinal : 4096 * (2 * k + 3) ^ 6 <= 4096 * (4 * (2 * k + 1) ^ 6) := by
    simpa [hpow4] using hpow''
  have : (2 * k + 3) ^ 6 <= 4 * (2 * k + 1) ^ 6 :=
    Nat.le_of_mul_le_mul_left hfinal (by decide : 0 < 4096)
  have hrewrite : 2 * (k + 1) + 1 = 2 * k + 3 := by
    omega
  simpa [hrewrite] using this

theorem Q43_pow6_le_three_pow2_ge13 {k : Nat} (hk : 13 <= k) :
    (2 * k + 1) ^ 6 <= 3 * 2 ^ (2 * k + 1) := by
  let m : Nat := k - 13
  have hk' : k = 13 + m := by
    have : 13 + (k - 13) = k := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.sub_add_cancel hk)
    simpa [m] using this.symm
  -- prove the bound for all k = 13 + m by induction on m.
  have hmain : (2 * (13 + m) + 1) ^ 6 <= 3 * 2 ^ (2 * (13 + m) + 1) := by
    induction m with
    | zero =>
        decide
    | succ m ih =>
        have hk4 : 4 <= 13 + m := Nat.le_trans (by decide : 4 <= 13) (Nat.le_add_right 13 m)
        have hstep : (2 * ((13 + m) + 1) + 1) ^ 6 <= 4 * (2 * (13 + m) + 1) ^ 6 := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Q43_pow6_succ_le_mul4 (k := 13 + m) hk4)
        have ih4 : 4 * (2 * (13 + m) + 1) ^ 6 <= 4 * (3 * 2 ^ (2 * (13 + m) + 1)) :=
          Nat.mul_le_mul_left 4 ih
        have hpow :
            4 * (3 * 2 ^ (2 * (13 + m) + 1)) = 3 * 2 ^ (2 * ((13 + m) + 1) + 1) := by
          have hpow_add :
              2 ^ ((2 * (13 + m) + 1) + 2) = 2 ^ (2 * (13 + m) + 1) * 2 ^ 2 := by
            simpa [Nat.add_assoc] using (Nat.pow_add 2 (2 * (13 + m) + 1) 2)
          have hpow_mul : 2 ^ (2 * (13 + m) + 1) * 4 = 2 ^ ((2 * (13 + m) + 1) + 2) := by
            calc
              2 ^ (2 * (13 + m) + 1) * 4
                  = 2 ^ (2 * (13 + m) + 1) * 2 ^ 2 := by
                      simp [Nat.pow_two]
              _ = 2 ^ ((2 * (13 + m) + 1) + 2) := by
                      symm
                      exact hpow_add
          have hexp : (2 * (13 + m) + 1) + 2 = 2 * ((13 + m) + 1) + 1 := by
            omega
          calc
            4 * (3 * 2 ^ (2 * (13 + m) + 1))
                = 3 * (2 ^ (2 * (13 + m) + 1) * 4) := by
                    simp [Nat.mul_left_comm, Nat.mul_comm]
            _ = 3 * 2 ^ ((2 * (13 + m) + 1) + 2) := by
                    simp [hpow_mul]
            _ = 3 * 2 ^ (2 * ((13 + m) + 1) + 1) := by
                    simp [hexp]
        have hpow_le :
            4 * (3 * 2 ^ (2 * (13 + m) + 1)) <= 3 * 2 ^ (2 * ((13 + m) + 1) + 1) :=
          Nat.le_of_eq hpow
        exact Nat.le_trans hstep (Nat.le_trans ih4 hpow_le)
  simpa [hk'] using hmain

theorem Q43_pow2_ge_two_mul_add_ge13 {k : Nat} (hk : 13 <= k) : 2 * k + 5 <= 2 ^ k := by
  let m : Nat := k - 13
  have hk' : k = 13 + m := by
    have : 13 + (k - 13) = k := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.sub_add_cancel hk)
    simpa [m] using this.symm
  have hmain : 2 * (13 + m) + 5 <= 2 ^ (13 + m) := by
    induction m with
    | zero =>
        decide
    | succ m ih =>
        have hstep1 : 2 * (13 + m.succ) + 5 = (2 * (13 + m) + 5) + 2 := by
          omega
        have hstep2 : 2 ^ (13 + m.succ) = 2 * 2 ^ (13 + m) := by
          calc
            2 ^ (13 + m.succ) = 2 ^ ((13 + m) + 1) := by
              simp [Nat.succ_eq_add_one, Nat.add_assoc]
            _ = 2 ^ (13 + m) * 2 := by
              simpa using (Nat.pow_add_one 2 (13 + m))
            _ = 2 * 2 ^ (13 + m) := by
              simp [Nat.mul_comm]
        have hmul : (2 * (13 + m) + 5) + 2 <= 2 * 2 ^ (13 + m) := by
          have hpos : 2 <= 2 * (13 + m) + 5 := by
            exact Nat.le_trans (by decide : 2 <= 5) (Nat.le_add_left 5 (2 * (13 + m)))
          have hdouble :
              (2 * (13 + m) + 5) + 2 <= (2 * (13 + m) + 5) + (2 * (13 + m) + 5) :=
            Nat.add_le_add_left hpos _
          have hmul3 : 2 * (2 * (13 + m) + 5) <= 2 * 2 ^ (13 + m) :=
            Nat.mul_le_mul_left 2 ih
          have hmul3' :
              (2 * (13 + m) + 5) + (2 * (13 + m) + 5) <= 2 * 2 ^ (13 + m) := by
            simpa [Nat.two_mul] using hmul3
          exact Nat.le_trans hdouble hmul3'
        simpa [hstep1, hstep2, Nat.mul_add, Nat.add_assoc] using hmul
  simpa [hk'] using hmain

-- (a+1)^5 - a^5 >= 5·a^4, via a^(n+1) + (n+1)·a^n <= (a+1)^(n+1).
theorem Q43_pow_succ_add_mul_le_succ_pow (a n : Nat) :
    a ^ (n + 1) + (n + 1) * a ^ n <= (a + 1) ^ (n + 1) := by
  induction n with
  | zero =>
      simp [Nat.pow_succ, Nat.mul_add, Nat.mul_comm]
  | succ n ih =>
      have ih_mul :
          a * (a ^ (n + 1) + (n + 1) * a ^ n) <= a * (a + 1) ^ (n + 1) :=
        Nat.mul_le_mul_left a ih
      have hmono : a ^ (n + 1) <= (a + 1) ^ (n + 1) :=
        Q43_pow_le_pow_of_le (a := a) (b := a + 1) (n := n + 1) (Nat.le_succ _)
      have ih' : a ^ (n + 2) + (n + 2) * a ^ (n + 1) <= a * (a + 1) ^ (n + 1) + (a + 1) ^ (n + 1) := by
        have h1 : a ^ (n + 2) + (n + 1) * a ^ (n + 1) <= a * (a + 1) ^ (n + 1) := by
          simpa [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih_mul
        have h2 :
            a ^ (n + 2) + (n + 1) * a ^ (n + 1) + a ^ (n + 1) <=
              a * (a + 1) ^ (n + 1) + (a + 1) ^ (n + 1) :=
          Nat.add_le_add h1 hmono
        -- rewrite `(n+2)·a^(n+1)` as `(n+1)·a^(n+1) + a^(n+1)`
        have hmul_succ :
            (n + 2) * a ^ (n + 1) = (n + 1) * a ^ (n + 1) + a ^ (n + 1) := by
          calc
            (n + 2) * a ^ (n + 1) = (n + 1 + 1) * a ^ (n + 1) := by
              simp [Nat.add_assoc]
            _ = (n + 1) * a ^ (n + 1) + 1 * a ^ (n + 1) := by
              simpa [Nat.add_assoc] using (Nat.add_mul (n + 1) 1 (a ^ (n + 1)))
            _ = (n + 1) * a ^ (n + 1) + a ^ (n + 1) := by
              simp
        simpa [Nat.add_assoc, hmul_succ] using h2
      -- rewrite the RHS as `(a+1)^(n+2)`
      simpa [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih'

theorem Q43_pow5_sub_pow5_ge_five_pow4 (a : Nat) :
    5 * a ^ 4 <= (a + 1) ^ 5 - a ^ 5 := by
  have hmono : a ^ 5 <= (a + 1) ^ 5 :=
    Q43_pow_le_pow_of_le (a := a) (b := a + 1) (n := 5) (Nat.le_succ _)
  have hmain : a ^ 5 + 5 * a ^ 4 <= (a + 1) ^ 5 := by
    simpa using (Q43_pow_succ_add_mul_le_succ_pow a 4)
  refine (Nat.le_sub_iff_add_le hmono).2 ?_
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain

theorem Q43_key_ineq_ge13 {k : Nat} (hk : 13 <= k) :
    (2 * k) * (2 ^ (k + 2) + (2 * k + 1) ^ 5)
      <= 5 * (2 ^ (2 * k + 1) - 2 ^ (k + 2)) := by
  have hpow6 : (2 * k + 1) ^ 6 <= 3 * 2 ^ (2 * k + 1) := Q43_pow6_le_three_pow2_ge13 hk
  have hpoly_le : (2 * k) * (2 * k + 1) ^ 5 <= (2 * k + 1) ^ 6 := by
    have h := Nat.mul_le_mul_right ((2 * k + 1) ^ 5) (Nat.le_succ (2 * k))
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hpoly : (2 * k) * (2 * k + 1) ^ 5 <= 3 * 2 ^ (2 * k + 1) :=
    Nat.le_trans hpoly_le hpow6
  have hpow2 : 2 * k + 5 <= 2 ^ k := Q43_pow2_ge_two_mul_add_ge13 hk
  have hexp : (2 * k + 5) * 2 ^ (k + 2) <= 2 ^ (2 * k + 2) := by
    have hmul : (2 * k + 5) * 2 ^ (k + 2) <= (2 ^ k) * 2 ^ (k + 2) :=
      Nat.mul_le_mul_right _ hpow2
    have hpow : (2 ^ k) * 2 ^ (k + 2) = 2 ^ (2 * k + 2) := by
      calc
        (2 ^ k) * 2 ^ (k + 2) = 2 ^ (k + (k + 2)) := by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.pow_add 2 k (k + 2)).symm
        _ = 2 ^ (2 * k + 2) := by
          simp [Nat.add_assoc, Nat.two_mul]
    exact Nat.le_trans hmul (by simp [hpow])
  have h5B : 5 * 2 ^ (k + 2) <= 2 ^ (2 * k + 2) := by
    have h5 : 5 <= 2 * k + 5 := Nat.le_add_left 5 (2 * k)
    have h5mul : 5 * 2 ^ (k + 2) <= (2 * k + 5) * 2 ^ (k + 2) :=
      Nat.mul_le_mul_right _ h5
    exact Nat.le_trans h5mul hexp
  have hexp' : (2 * k) * 2 ^ (k + 2) <= 2 ^ (2 * k + 2) - 5 * 2 ^ (k + 2) := by
    have hsum :
        (2 * k) * 2 ^ (k + 2) + 5 * 2 ^ (k + 2) <= 2 ^ (2 * k + 2) := by
      have hsum' : ((2 * k) + 5) * 2 ^ (k + 2) <= 2 ^ (2 * k + 2) := by
        simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hexp
      simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum'
    exact (Nat.le_sub_iff_add_le (m := 2 ^ (2 * k + 2)) (k := 5 * 2 ^ (k + 2)) (n := (2 * k) * 2 ^ (k + 2))
      (Nat.le_trans (Nat.le_add_left _ _) hsum)).2 hsum
  have hsum :
      (2 * k) * (2 ^ (k + 2) + (2 * k + 1) ^ 5)
        <= (2 ^ (2 * k + 2) - 5 * 2 ^ (k + 2)) + 3 * 2 ^ (2 * k + 1) := by
    have : (2 * k) * (2 ^ (k + 2) + (2 * k + 1) ^ 5)
        = (2 * k) * 2 ^ (k + 2) + (2 * k) * (2 * k + 1) ^ 5 := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
    rw [this]
    exact Nat.add_le_add hexp' hpoly
  have hpow : (2 ^ (2 * k + 2) - 5 * 2 ^ (k + 2)) + 3 * 2 ^ (2 * k + 1) =
      5 * (2 ^ (2 * k + 1) - 2 ^ (k + 2)) := by
    let A : Nat := 2 ^ (2 * k + 1)
    let B : Nat := 2 ^ (k + 2)
    have hA : 2 ^ (2 * k + 2) = 2 * A := by
      simp [A, Nat.pow_succ, Nat.mul_comm]
    have h5B' : 5 * B <= 2 * A := by
      simpa [A, B, hA] using h5B
    calc
      (2 ^ (2 * k + 2) - 5 * B) + 3 * A = (2 * A - 5 * B) + 3 * A := by
        simp [A, B, hA]
      _ = 3 * A + (2 * A - 5 * B) := by
        simp [Nat.add_comm]
      _ = 3 * A + 2 * A - 5 * B := by
        simpa [Nat.add_assoc] using (Nat.add_sub_assoc h5B' (n := 3 * A)).symm
      _ = (3 + 2) * A - 5 * B := by
        have h : 3 * A + 2 * A = (3 + 2) * A := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.add_mul 3 2 A).symm
        simp [h]
      _ = 5 * A - 5 * B := by
        simp
      _ = 5 * (A - B) := by
        symm
        simp [Nat.mul_sub_left_distrib]
      _ = 5 * (2 ^ (2 * k + 1) - 2 ^ (k + 2)) := by
        simp [A, B]
  simpa [hpow] using hsum

theorem Q43_grid_ratio_drop_nk_of_ge {k : Nat} (hk : 12 <= k) :
    Q43_grid_ratio (Q43_nk k + 1) < Q43_grid_ratio (Q43_nk k) := by
  by_cases hk12 : k = 12
  · subst hk12
    simpa [Q43_nk_eq_gap_n12, Q43_gap_n, Q43_gap_n_succ] using Q43_grid_ratio_drop_gap
  ·
    have hk13 : 13 <= k := Nat.succ_le_iff.2 (Nat.lt_of_le_of_ne hk (Ne.symm hk12))
    have hk1 : 1 <= k := Nat.le_trans (by decide : 1 <= 13) hk13
    have hlog := Q43_log2_jump_nk (k := k) hk1
    let n : Nat := Q43_nk k
    have hlog_n : Nat.log2 (Q43_grid_size n) = 2 * k := by
      simpa [n, Q43_grid_size, Nat.pow_two] using hlog.1
    have hlog_succ : Nat.log2 (Q43_grid_size (n + 1)) = 2 * k + 1 := by
      simpa [n, Q43_grid_size, Nat.pow_two, Nat.add_assoc] using hlog.2
    have hn2 : 2 * n + 1 <= 2 ^ (k + 2) := by
      simpa [n] using Q43_two_nk_add_one_le_pow k
    have hn0 : 2 ^ (2 * k + 1) - 2 ^ (k + 2) <= Q43_grid_size n := by
      simpa [n, Q43_grid_size, Nat.pow_two] using Q43_nk_sq_ge_pow_sub k
    have hkey :
        (2 * k) * (2 ^ (k + 2) + (2 * k + 1) ^ 5) <= 5 * (2 ^ (2 * k + 1) - 2 ^ (k + 2)) :=
      Q43_key_ineq_ge13 hk13
    have hkey' :
        (2 * k) * (2 * n + 1 + (2 * k + 1) ^ 5) <= 5 * Q43_grid_size n := by
      have hn_le : 2 * n + 1 + (2 * k + 1) ^ 5 <= 2 ^ (k + 2) + (2 * k + 1) ^ 5 :=
        Nat.add_le_add_right hn2 _
      have hmul1 :
          (2 * k) * (2 * n + 1 + (2 * k + 1) ^ 5)
            <= (2 * k) * (2 ^ (k + 2) + (2 * k + 1) ^ 5) :=
        Nat.mul_le_mul_left _ hn_le
      have hmul2 :
          (2 * k) * (2 * n + 1 + (2 * k + 1) ^ 5)
            <= 5 * (2 ^ (2 * k + 1) - 2 ^ (k + 2)) :=
        Nat.le_trans hmul1 hkey
      have hmul3 : 5 * (2 ^ (2 * k + 1) - 2 ^ (k + 2)) <= 5 * Q43_grid_size n :=
        Nat.mul_le_mul_left 5 hn0
      exact Nat.le_trans hmul2 hmul3
    -- turn the k-bound into the cross-multiplication inequality needed for division comparison
    let d0 : Nat := (2 * k) ^ 5
    let d1 : Nat := (2 * k + 1) ^ 5
    have hd01 : d0 <= d1 :=
      Q43_pow_le_pow_of_le (a := 2 * k) (b := 2 * k + 1) (n := 5) (Nat.le_succ _)
    have hgap : 5 * (2 * k) ^ 4 <= d1 - d0 := by
      simpa [d0, d1, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Q43_pow5_sub_pow5_ge_five_pow4 (a := 2 * k))
    have hgap' : 5 * Q43_grid_size n * (2 * k) ^ 4 <= Q43_grid_size n * (d1 - d0) := by
      have := Nat.mul_le_mul_left (Q43_grid_size n) hgap
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
    have hkey_pow : d0 * (2 * n + 1 + d1) <= 5 * Q43_grid_size n * (2 * k) ^ 4 := by
      have hmul : (2 * k) ^ 4 * ((2 * k) * (2 * n + 1 + d1)) <= (2 * k) ^ 4 * (5 * Q43_grid_size n) :=
        Nat.mul_le_mul_left ((2 * k) ^ 4) hkey'
      have hmul' : d0 * (2 * n + 1 + d1) <= (2 * k) ^ 4 * (5 * Q43_grid_size n) := by
        simpa [d0, Nat.pow_succ, Nat.mul_assoc] using hmul
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul'
    have hdiff : d0 * (2 * n + 1 + d1) <= Q43_grid_size n * (d1 - d0) :=
      Nat.le_trans hkey_pow hgap'
    have hgrid_succ : Q43_grid_size (n + 1) = Q43_grid_size n + (2 * n + 1) := by
      simp [Q43_grid_size, Nat.two_mul, Nat.mul_add, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm]
    have hcross : d0 * (Q43_grid_size (n + 1) + d1) <= Q43_grid_size n * d1 := by
      have hplus :
          d0 * Q43_grid_size n + d0 * (2 * n + 1 + d1)
            <= d0 * Q43_grid_size n + Q43_grid_size n * (d1 - d0) :=
        Nat.add_le_add_left hdiff (d0 * Q43_grid_size n)
      have hleft :
          d0 * (Q43_grid_size (n + 1) + d1) =
            d0 * Q43_grid_size n + d0 * (2 * n + 1 + d1) := by
        calc
          d0 * (Q43_grid_size (n + 1) + d1)
              = d0 * (Q43_grid_size n + (2 * n + 1) + d1) := by
                  simp [hgrid_succ, Nat.add_assoc]
          _ = d0 * (Q43_grid_size n + (2 * n + 1 + d1)) := by
                  simp [Nat.add_assoc]
          _ = d0 * Q43_grid_size n + d0 * (2 * n + 1 + d1) := by
                  simp [Nat.mul_add, Nat.add_assoc]
      have hright :
          d0 * Q43_grid_size n + Q43_grid_size n * (d1 - d0) = Q43_grid_size n * d1 := by
        have hadd : d1 - d0 + d0 = d1 := Nat.sub_add_cancel hd01
        have hfirst : d0 * Q43_grid_size n = Q43_grid_size n * d0 := by
          simpa using (Nat.mul_comm d0 (Q43_grid_size n))
        calc
          d0 * Q43_grid_size n + Q43_grid_size n * (d1 - d0)
              = Q43_grid_size n * d0 + Q43_grid_size n * (d1 - d0) := by
                  simp [hfirst]
          _ = Q43_grid_size n * (d0 + (d1 - d0)) := by
                  symm
                  simp [Nat.mul_add]
          _ = Q43_grid_size n * (d1 - d0 + d0) := by
                  simp [Nat.add_comm]
          _ = Q43_grid_size n * d1 := by
                  simp [hadd]
      calc
        d0 * (Q43_grid_size (n + 1) + d1)
            = d0 * Q43_grid_size n + d0 * (2 * n + 1 + d1) := hleft
        _ <= d0 * Q43_grid_size n + Q43_grid_size n * (d1 - d0) := hplus
        _ = Q43_grid_size n * d1 := hright
    -- conclude via division comparison at fixed denominator d0·d1
    have hkpos : 0 < k := Nat.lt_of_lt_of_le (by decide : 0 < 13) hk13
    have h2kpos : 0 < 2 * k := Nat.mul_pos (by decide : 0 < 2) hkpos
    have hd0 : 0 < d0 := by
      simpa [d0] using (Nat.pow_pos h2kpos : 0 < (2 * k) ^ 5)
    have hd1 : 0 < d1 := by
      have : 0 < 2 * k + 1 := Nat.succ_pos _
      simpa [d1] using (Nat.pow_pos this : 0 < (2 * k + 1) ^ 5)
    have hdiv : (Q43_grid_size (n + 1) + d1) / d1 <= Q43_grid_size n / d0 := by
      let D : Nat := d0 * d1
      have hscaled := Nat.div_le_div_right (c := D) (by simpa [D] using hcross)
      have hleft : (d0 * (Q43_grid_size (n + 1) + d1)) / D = (Q43_grid_size (n + 1) + d1) / d1 := by
        simpa [D, Nat.mul_assoc] using
          (Nat.mul_div_mul_left (m := d0) (n := Q43_grid_size (n + 1) + d1) (k := d1) hd0)
      have hright : (Q43_grid_size n * d1) / D = Q43_grid_size n / d0 := by
        simpa [D, Nat.mul_assoc] using
          (Nat.mul_div_mul_right (m := d1) (n := Q43_grid_size n) (k := d0) hd1)
      simpa [hleft, hright] using hscaled
    have hq :
        Q43_grid_ratio (n + 1) + 1 <= Q43_grid_ratio n := by
      have hadd : (Q43_grid_size (n + 1) + d1) / d1 = Q43_grid_size (n + 1) / d1 + 1 := by
        simpa [Nat.add_comm] using Nat.add_div_right (Q43_grid_size (n + 1)) (z := d1) hd1
      -- rewrite Q43_grid_ratio using the log2-jump equalities
      have hr1 : Q43_grid_ratio (n + 1) = Q43_grid_size (n + 1) / d1 := by
        simp [Q43_grid_ratio, hlog_succ, d1]
      have hr0 : Q43_grid_ratio n = Q43_grid_size n / d0 := by
        simp [Q43_grid_ratio, hlog_n, d0]
      -- combine
      have : Q43_grid_size (n + 1) / d1 + 1 <= Q43_grid_size n / d0 := by
        simpa [hadd] using hdiv
      simpa [hr1, hr0] using this
    have : Q43_grid_ratio (n + 1) < Q43_grid_ratio n :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hq
    -- finish by rewriting n = Q43_nk k
    simpa [n, Nat.add_assoc] using this

theorem Q43_grid_ratio_drop_nk {k : Nat} (hk : 12 <= k) :
    Q43_grid_ratio (Q43_nk k + 1) < Q43_grid_ratio (Q43_nk k) := by
  simpa using (Q43_grid_ratio_drop_nk_of_ge (k := k) hk)

-- Q43.S278-simplify-gap-min-bridge:
-- bridge the gap-min ratio alias directly to the uniform n_k drop.
theorem Q43_gap_min_ratio_drop_nk {k : Nat} (hk : 12 <= k) :
    Q43_gap_min_ratio_k k (Q43_nk k + 1) < Q43_gap_min_ratio_k k (Q43_nk k) := by
  simpa [Q43_gap_min_ratio_k] using (Q43_grid_ratio_drop_nk (k := k) hk)

-- Q43.S279-gap-min-global-bridge-apply:
-- apply the uniform n_k bridge to the global gap-min ratio at k=12.
theorem Q43_gap_min_ratio_drop_global :
    Q43_gap_min_ratio < Q43_gap_min_ratio_k Q43_gap_k Q43_gap_n := by
  have hk : 12 <= Q43_gap_k := by
    simp [Q43_gap_k]
  have hdrop := Q43_gap_min_ratio_drop_nk (k := Q43_gap_k) hk
  simpa [Q43_gap_min_ratio, Q43_gap_k, Q43_nk_eq_gap_n12, Q43_gap_n_succ_eq] using hdrop

-- Q43.S285-gap-min-global-route:
-- route the global drop through the grid_ratio form without re-expanding the alias.
theorem Q43_gap_min_ratio_drop_global_grid_of_drop
    (h : Q43_gap_min_ratio < Q43_gap_min_ratio_k Q43_gap_k Q43_gap_n) :
    Q43_gap_min_ratio < Q43_grid_ratio Q43_gap_n := by
  simpa [Q43_gap_min_ratio_k] using h

-- Q43.S282-gap-min-global-use:
-- lift the global drop to a +1 bound in grid_ratio form.
theorem Q43_gap_min_ratio_drop_global_grid_succ_le :
    Q43_gap_min_ratio + 1 <= Q43_grid_ratio Q43_gap_n := by
  have h : Q43_gap_min_ratio < Q43_grid_ratio Q43_gap_n :=
    Q43_gap_min_ratio_drop_global_grid_of_drop Q43_gap_min_ratio_drop_global
  exact (Nat.succ_le_iff).2 h

-- Q43.S284-gap-min-global-le-bridge:
-- turn a succ-le bound into a strict inequality.
theorem Q43_lt_of_succ_le {a b : Nat} (h : a + 1 <= b) : a < b := by
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h

-- Q43.S283-gap-min-global-succ-use:
-- repackage the +1 bound as a strict inequality.
theorem Q43_gap_min_ratio_drop_global_grid_of_succ_le
    (h : Q43_gap_min_ratio + 1 <= Q43_grid_ratio Q43_gap_n) :
    Q43_gap_min_ratio < Q43_grid_ratio Q43_gap_n := by
  exact Q43_lt_of_succ_le h

-- Q43.S280-gap-min-global-cleanup:
-- expose the global drop as a grid_ratio inequality.
theorem Q43_gap_min_ratio_drop_global_grid :
    Q43_gap_min_ratio < Q43_grid_ratio Q43_gap_n := by
  exact Q43_gap_min_ratio_drop_global_grid_of_succ_le
    Q43_gap_min_ratio_drop_global_grid_succ_le

-- TODO(Q43.S137-logn-remaining-scan): add the formal flat local-EF(s) evaluation statement.

end PvNP
