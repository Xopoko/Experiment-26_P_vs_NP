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

-- Q43.S299-logn-remaining-scan:
-- isolate the remaining log2 N usage in the Thm. 4.1 threshold via log2 monotonicity.
theorem Q43_thm41_log2_threshold_c1_grid_param_of_log2 {n N : Nat}
    (hlog : Nat.log2 N <= Nat.log2 (Q43_grid_size n))
    (hth : Q43_thm41_log2_threshold_c1_grid n) :
    Q43_thm41_log2_threshold_c1_grid_param n N := by
  exact Nat.le_trans hlog hth

theorem Q43_thm41_log2_threshold_c1_grid_param_of_le {n N : Nat}
    (hN : N <= Q43_grid_size n)
    (hth : Q43_thm41_log2_threshold_c1_grid n) :
    Q43_thm41_log2_threshold_c1_grid_param n N := by
  have hlog : Nat.log2 N <= Nat.log2 (Q43_grid_size n) := Q43_log2_mono hN
  exact Q43_thm41_log2_threshold_c1_grid_param_of_log2 (n:=n) (N:=N) hlog hth

def Q43_thm41_regime_d_ok_param (n N : Nat) : Prop :=
  Q43_thm41_log2_threshold_c1_grid_param n N ∧ Q43_thm41_c1_chernoff_ln <= Q43_grid_size n

theorem Q43_thm41_regime_d_ok_param_of_log2 {n N : Nat}
    (hlog : Nat.log2 N <= Nat.log2 (Q43_grid_size n))
    (hok : Q43_thm41_regime_d_ok n) :
    Q43_thm41_regime_d_ok_param n N := by
  rcases hok with ⟨hth, hbound⟩
  refine ⟨?_, hbound⟩
  exact Q43_thm41_log2_threshold_c1_grid_param_of_log2 (n:=n) (N:=N) hlog hth

theorem Q43_thm41_regime_d_ok_param_of_le {n N : Nat}
    (hN : N <= Q43_grid_size n)
    (hok : Q43_thm41_regime_d_ok n) :
    Q43_thm41_regime_d_ok_param n N := by
  have hlog : Nat.log2 N <= Nat.log2 (Q43_grid_size n) := Q43_log2_mono hN
  exact Q43_thm41_regime_d_ok_param_of_log2 (n:=n) (N:=N) hlog hok

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

-- Q43.S301-flat-eval-evaluation-statement:
-- polynomial size bounds yield explicit log2 t-parameter bounds.
theorem Q43_log2_poly_bound {n k : Nat} (hn : 2 <= n) :
    Nat.log2 (n ^ k + 1) <= (Nat.log2 n + 1) * k + 1 := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 2) hn
  have hpow_pos : 0 < n ^ k := Nat.pow_pos hnpos
  have hpow_ge_one : 1 <= n ^ k := (Nat.succ_le_iff).2 hpow_pos
  have hle' : n ^ k + 1 <= n ^ k + n ^ k := Nat.add_le_add_left hpow_ge_one _
  have hle : n ^ k + 1 <= 2 * n ^ k := by
    simpa [Nat.two_mul] using hle'
  have hlog : Nat.log2 (n ^ k + 1) <= Nat.log2 (2 * n ^ k) := Q43_log2_mono hle
  have hne : n ^ k ≠ 0 := Nat.ne_of_gt hpow_pos
  have hlog2 : Nat.log2 (2 * n ^ k) = Nat.log2 (n ^ k) + 1 := by
    simpa using (Nat.log2_two_mul (n := n ^ k) hne)
  have hlog' : Nat.log2 (n ^ k + 1) <= Nat.log2 (n ^ k) + 1 := by
    simpa [hlog2] using hlog
  have hpow : Nat.log2 (n ^ k) <= (Nat.log2 n + 1) * k :=
    Q43_log2_pow_le_mul_succ (a := n) (C := k)
  exact Nat.le_trans hlog' (Nat.add_le_add_right hpow 1)

theorem Q43_tParam_le_log2_poly_bound {n k M : Nat} (hn : 2 <= n) (hM : M <= n ^ k + 1) :
    Q43_tParam M <= (Nat.log2 n + 1) * k + 1 := by
  have hlog : Nat.log2 M <= Nat.log2 (n ^ k + 1) := Q43_log2_mono hM
  have hpoly : Nat.log2 (n ^ k + 1) <= (Nat.log2 n + 1) * k + 1 :=
    Q43_log2_poly_bound (n := n) (k := k) hn
  simpa [Q43_tParam] using (Nat.le_trans hlog hpoly)

-- Q43.S302-flat-eval-proofsize-to-linemax:
-- specialize the polynomial log2 bound to lineMax via proofSize.
theorem Q43_tParam_lineMax_le_log2_poly_bound {α : Type} {proof : List (List α)} {n k : Nat}
    (hn : 2 <= n) (hsize : Q43_proofSize proof <= n ^ k + 1) :
    Q43_tParam (Q43_lineMax proof) <= (Nat.log2 n + 1) * k + 1 := by
  have hline : Q43_lineMax proof <= Q43_proofSize proof := Q43_lineMax_le_proofSize proof
  have hM : Q43_lineMax proof <= n ^ k + 1 := Nat.le_trans hline hsize
  exact Q43_tParam_le_log2_poly_bound (n := n) (k := k) (M := Q43_lineMax proof) hn hM

-- Q43.S303-flat-eval-quasipoly-linemax:
-- quasi-polynomial size bounds yield polylog t-parameter bounds.
theorem Q43_tParam_le_polylog_of_quasipoly {n c M : Nat}
    (hM : M <= 2 ^ ((Nat.log2 n) ^ (c + 1))) :
    Q43_tParam M <= (Nat.log2 n) ^ (c + 1) := by
  have hlog : Nat.log2 M <= Nat.log2 (2 ^ ((Nat.log2 n) ^ (c + 1))) := Q43_log2_mono hM
  have hfinal : Nat.log2 M <= (Nat.log2 n) ^ (c + 1) := by
    simpa [Nat.log2_two_pow] using hlog
  simpa [Q43_tParam] using hfinal

theorem Q43_tParam_lineMax_le_polylog_of_quasipoly {α : Type} {proof : List (List α)} {n c : Nat}
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 n) ^ (c + 1))) :
    Q43_tParam (Q43_lineMax proof) <= (Nat.log2 n) ^ (c + 1) := by
  have hline : Q43_lineMax proof <= Q43_proofSize proof := Q43_lineMax_le_proofSize proof
  have hM : Q43_lineMax proof <= 2 ^ ((Nat.log2 n) ^ (c + 1)) := Nat.le_trans hline hsize
  exact Q43_tParam_le_polylog_of_quasipoly (n := n) (c := c) (M := Q43_lineMax proof) hM

-- Q43.S304-flat-eval-quasipoly-bridge:
-- specialize the quasi-poly lineMax bound to grid size |F| = n^2.
@[simp] theorem Q43_tParam_lineMax_le_polylog_of_quasipoly_grid {α : Type}
    {proof : List (List α)} {n c : Nat}
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1))) :
    Q43_tParam (Q43_lineMax proof) <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) := by
  exact Q43_tParam_lineMax_le_polylog_of_quasipoly
    (n := Q43_grid_size n) (c := c) (proof := proof) hsize

-- Q43.S305-flat-eval-quasipoly-eval-apply:
-- apply grid-size quasi-poly bounds to N and lineMax for the evaluation regime.
theorem Q43_quasipoly_grid_eval_bounds {α : Type} {proof : List (List α)} {n N c : Nat}
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1))) :
    Nat.log2 N <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) ∧
      Q43_tParam (Q43_lineMax proof) <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) := by
  have hlog : Nat.log2 N <= Nat.log2 (2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1))) :=
    Q43_log2_mono hN
  have hlogN : Nat.log2 N <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) := by
    simpa [Nat.log2_two_pow] using hlog
  have hM : Q43_tParam (Q43_lineMax proof) <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) :=
    Q43_tParam_lineMax_le_polylog_of_quasipoly_grid (proof := proof) (n := n) (c := c) hsize
  exact ⟨hlogN, hM⟩

@[simp] theorem Q43_tParam_lineMax_le_polylog_of_quasipoly_grid_twice {α : Type}
    {proof : List (List α)} {n N c : Nat}
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1))) :
    Q43_tParam (Q43_lineMax proof) <= (2 * Nat.log2 (Q43_grid_size n)) ^ (c + 1) := by
  have h := (Q43_quasipoly_grid_eval_bounds (proof := proof) (n := n) (N := N) (c := c) hN hsize).2
  have hle :
      Nat.log2 (Q43_grid_size n) <= 2 * Nat.log2 (Q43_grid_size n) := by
    calc
      Nat.log2 (Q43_grid_size n)
          <= Nat.log2 (Q43_grid_size n) + Nat.log2 (Q43_grid_size n) := Nat.le_add_left _ _
      _ = 2 * Nat.log2 (Q43_grid_size n) := by
        simp [Nat.two_mul]
  have hpow :
      (Nat.log2 (Q43_grid_size n)) ^ (c + 1)
        <= (2 * Nat.log2 (Q43_grid_size n)) ^ (c + 1) :=
    Q43_pow_le_pow_of_le hle
  exact Nat.le_trans h hpow

theorem Q43_polyNM_log2_bounds {n N C M K : Nat} (hn : 2 <= n) (h : Q43_polyNM n N C M K) :
    Nat.log2 N <= Nat.log2 ((Q43_grid_size n) ^ C) ∧
    Q43_tParam M <= Nat.log2 ((Q43_grid_size n) ^ K) ∧
    Q43_tParam M <= (Nat.log2 (Q43_grid_size n) + 1) * K + 1 := by
  rcases h with ⟨hN, hM⟩
  have hn1 : 1 <= n := Nat.le_trans (by decide : 1 <= 2) hn
  have hmul : n <= Q43_grid_size n := by
    calc
      n = n * 1 := by simp
      _ <= n * n := by
        exact Nat.mul_le_mul_left n hn1
  have hgrid : 2 <= Q43_grid_size n := Nat.le_trans hn hmul
  have hM' : M <= (Q43_grid_size n) ^ K + 1 := Nat.le_trans hM (Nat.le_succ _)
  have hpoly :
      Q43_tParam M <= (Nat.log2 (Q43_grid_size n) + 1) * K + 1 :=
    Q43_tParam_le_log2_poly_bound (n := Q43_grid_size n) (k := K) (M := M) hgrid hM'
  exact ⟨Q43_log2_le_log2_grid_pow (n:=n) (N:=N) (C:=C) hN,
    Q43_tParam_le_log2_grid_pow (n:=n) (M:=M) (K:=K) hM, hpoly⟩

-- Q43.S231-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-threshold:
-- bundle the regime-d criterion with poly N/M log2 bounds.
theorem Q43_regime_d_ok_polyNM_bounds {n N C M K : Nat} (hn : 2 <= n)
    (hpow5 : Q43_thm41_log2_threshold_c1_grid_mul_pow5 n)
    (hpoly : Q43_polyNM n N C M K) :
    Q43_thm41_regime_d_ok n ∧
      Nat.log2 N <= Nat.log2 ((Q43_grid_size n) ^ C) ∧
      Q43_tParam M <= Nat.log2 ((Q43_grid_size n) ^ K) ∧
      Q43_tParam M <= (Nat.log2 (Q43_grid_size n) + 1) * K + 1 := by
  have hreg : Q43_thm41_regime_d_ok n :=
    Q43_thm41_regime_d_ok_of_pow5 (n:=n) hn hpow5
  have hbounds :
      Nat.log2 N <= Nat.log2 ((Q43_grid_size n) ^ C) ∧
      Q43_tParam M <= Nat.log2 ((Q43_grid_size n) ^ K) ∧
      Q43_tParam M <= (Nat.log2 (Q43_grid_size n) + 1) * K + 1 :=
    Q43_polyNM_log2_bounds (n:=n) (N:=N) (C:=C) (M:=M) (K:=K) hn hpoly
  exact ⟨hreg, hbounds⟩

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

-- Q43.S306-flat-eval-quasipoly-hr-threshold:
-- connect quasi-poly log2 bounds to the Thm. 4.1 regime-d parameter check.
theorem Q43_thm41_log2_threshold_c1_grid_param_of_scaled {n N C : Nat} (hn : 2 <= n)
    (hlog : Nat.log2 N <= C * Nat.log2 (Q43_grid_size n))
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C) :
    Q43_thm41_log2_threshold_c1_grid_param n N := by
  let L := Nat.log2 (Q43_grid_size n)
  have hlog' : Nat.log2 N <= C * L := by
    simpa [L] using hlog
  have hposlog : 0 < L := by
    have hlog1 : 1 <= L := by
      simpa [L] using (Q43_log2_grid_ge_one (n:=n) hn)
    exact (Nat.succ_le_iff).1 hlog1
  have hc1 : 0 < Q43_thm41_c1_chernoff_ln := by decide
  have hpos : 0 < Q43_thm41_c1_chernoff_ln * L ^ 4 := by
    exact Nat.mul_pos hc1 (Nat.pow_pos hposlog)
  have hscale' :
      (2 * C * Q43_thm41_c1_chernoff_ln) * L ^ 5 <= Q43_grid_size n := by
    simpa [Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple, L] using hscale
  have hle : C * Q43_thm41_c1_chernoff_ln <= 2 * C * Q43_thm41_c1_chernoff_ln := by
    calc
      C * Q43_thm41_c1_chernoff_ln
          <= C * Q43_thm41_c1_chernoff_ln + C * Q43_thm41_c1_chernoff_ln := by
            exact Nat.le_add_left _ _
      _ = 2 * (C * Q43_thm41_c1_chernoff_ln) := by
            simp [Nat.two_mul]
      _ = 2 * C * Q43_thm41_c1_chernoff_ln := by
            simp [Nat.mul_assoc]
  have hmul' :
      (C * Q43_thm41_c1_chernoff_ln) * L ^ 5
        <= (2 * C * Q43_thm41_c1_chernoff_ln) * L ^ 5 := by
    exact Nat.mul_le_mul_right _ hle
  have hmul :
      (C * Q43_thm41_c1_chernoff_ln) * L ^ 5 <= Q43_grid_size n := by
    exact Nat.le_trans hmul' hscale'
  have hmul'': (C * L) * (Q43_thm41_c1_chernoff_ln * L ^ 4) <= Q43_grid_size n := by
    have hmul_eq :
        (C * L) * (Q43_thm41_c1_chernoff_ln * L ^ 4)
          = (C * Q43_thm41_c1_chernoff_ln) * L ^ 5 := by
      calc
        (C * L) * (Q43_thm41_c1_chernoff_ln * L ^ 4)
            = (C * Q43_thm41_c1_chernoff_ln) * (L * L ^ 4) := by
              ac_rfl
        _ = (C * Q43_thm41_c1_chernoff_ln) * L ^ 5 := by
              simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc]
    simpa [hmul_eq] using hmul
  have hCL :
      C * L <= Q43_grid_size n / (Q43_thm41_c1_chernoff_ln * L ^ 4) := by
    exact (Nat.le_div_iff_mul_le hpos).2 hmul''
  have hfinal :
      Nat.log2 N <= Q43_grid_size n / (Q43_thm41_c1_chernoff_ln * L ^ 4) :=
    Nat.le_trans hlog' hCL
  simpa [Q43_thm41_log2_threshold_c1_grid_param, L] using hfinal

-- Q43.S307-flat-eval-quasipoly-regime-d-bundle:
-- bundle the regime-d threshold, |F| >= c1, and quasi-poly t-parameter bounds.
theorem Q43_thm41_c1_le_grid_of_scaled {n C : Nat} (hn : 2 <= n) (hC : 1 <= C)
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C) :
    Q43_thm41_c1_chernoff_ln <= Q43_grid_size n := by
  let L := Nat.log2 (Q43_grid_size n)
  have hlog : 1 <= L := by
    simpa [L] using (Q43_log2_grid_ge_one (n:=n) hn)
  have hpow_pos : 0 < L ^ 5 := Nat.pow_pos (Nat.succ_le_iff.mp hlog)
  have hpow_ge_one : 1 <= L ^ 5 := (Nat.succ_le_iff).2 hpow_pos
  have hC2 : 1 <= 2 * C := by
    have h2le : 2 <= 2 * C := by
      simpa using (Nat.mul_le_mul_left 2 hC)
    exact Nat.le_trans (by decide : 1 <= 2) h2le
  have hc1 : Q43_thm41_c1_chernoff_ln <= 2 * C * Q43_thm41_c1_chernoff_ln := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.mul_le_mul_right Q43_thm41_c1_chernoff_ln hC2)
  have hmul :
      2 * C * Q43_thm41_c1_chernoff_ln
        <= (2 * C * Q43_thm41_c1_chernoff_ln) * L ^ 5 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.mul_le_mul_left (2 * C * Q43_thm41_c1_chernoff_ln) hpow_ge_one)
  have hc1' :
      Q43_thm41_c1_chernoff_ln
        <= (2 * C * Q43_thm41_c1_chernoff_ln) * L ^ 5 := by
    exact Nat.le_trans hc1 hmul
  have hscale' :
      (2 * C * Q43_thm41_c1_chernoff_ln) * L ^ 5 <= Q43_grid_size n := by
    simpa [Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple, L] using hscale
  exact Nat.le_trans hc1' hscale'

theorem Q43_thm41_regime_d_ok_param_of_scaled {n N C : Nat} (hn : 2 <= n) (hC : 1 <= C)
    (hlog : Nat.log2 N <= C * Nat.log2 (Q43_grid_size n))
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C) :
    Q43_thm41_regime_d_ok_param n N := by
  refine ⟨?_, ?_⟩
  · exact Q43_thm41_log2_threshold_c1_grid_param_of_scaled (n:=n) (N:=N) (C:=C) hn hlog hscale
  · exact Q43_thm41_c1_le_grid_of_scaled (n:=n) (C:=C) hn hC hscale

-- Q43.S308-flat-eval-quasipoly-regime-d-linemax-apply:
-- apply the regime-d bundle to lineMax via proofSize in the quasi-poly regime.
theorem Q43_quasipoly_regime_d_ok_param_lineMax {α : Type} {proof : List (List α)} {n N c : Nat}
    (hn : 2 <= n)
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n
      ((Nat.log2 (Q43_grid_size n)) ^ c)) :
    Q43_thm41_regime_d_ok_param n N ∧
      Q43_tParam (Q43_lineMax proof) <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) := by
  let L := Nat.log2 (Q43_grid_size n)
  have hlog : Nat.log2 N <= L ^ (c + 1) := by
    have hlog' : Nat.log2 N <= Nat.log2 (2 ^ (L ^ (c + 1))) := Q43_log2_mono hN
    simpa [Nat.log2_two_pow, L] using hlog'
  have hlog_mul : Nat.log2 N <= L ^ c * L := by
    simpa [Nat.pow_succ, L] using hlog
  have hC : 1 <= L ^ c := by
    have hlog1 : 1 <= L := by
      simpa [L] using (Q43_log2_grid_ge_one (n:=n) hn)
    have hpos : 0 < L := (Nat.succ_le_iff).1 hlog1
    have hpow_pos : 0 < L ^ c := Nat.pow_pos hpos
    exact (Nat.succ_le_iff).2 hpow_pos
  have hscale' :
      Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n (L ^ c) := by
    simpa [L] using hscale
  have hreg :
      Q43_thm41_regime_d_ok_param n N :=
    Q43_thm41_regime_d_ok_param_of_scaled
      (n:=n) (N:=N) (C:=L ^ c) hn hC hlog_mul hscale'
  have hM' :
      Q43_tParam (Q43_lineMax proof) <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) :=
    Q43_tParam_lineMax_le_polylog_of_quasipoly_grid (proof := proof) (n := n) (c := c) hsize
  exact ⟨hreg, hM'⟩

-- Q43.S309-flat-eval-quasipoly-eval-linemax-bridge:
-- package the regime-d bundle into the flat evaluation statement (lineMax + proofSize).
def Q43_flat_eval_statement {α : Type} (n N c : Nat) (proof : List (List α)) : Prop :=
  Q43_thm41_regime_d_ok_param n N ∧
    Q43_tParam (Q43_lineMax proof) <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1)

theorem Q43_flat_eval_statement_of_quasipoly {α : Type} {proof : List (List α)} {n N c : Nat}
    (hn : 2 <= n)
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n
      ((Nat.log2 (Q43_grid_size n)) ^ c)) :
    Q43_flat_eval_statement n N c proof := by
  have hbundle :=
    Q43_quasipoly_regime_d_ok_param_lineMax
      (proof:=proof) (n:=n) (N:=N) (c:=c) hn hN hsize hscale
  simpa [Q43_flat_eval_statement] using hbundle

-- Q43.S311-flat-eval-quasipoly-hr-threshold-asymptotic:
-- asymptotic log2^c bound needed for the HR threshold on the grid regime.
def Q43_hrThreshold_log2_bound (n c : Nat) : Prop :=
  (Nat.log2 (Q43_grid_size n)) ^ (c + 1) <= n / 16

-- Q43.S315-flat-eval-quasipoly-hr-threshold-formal-c-bound:
-- rewrite the HR log2 bound as a square inequality on |F|.
theorem Q43_hrThreshold_log2_bound_iff_pow {n c : Nat} :
    Q43_hrThreshold_log2_bound n c ↔
      256 * (Nat.log2 (Q43_grid_size n)) ^ (2 * (c + 1)) <= Q43_grid_size n := by
  let L := Nat.log2 (Q43_grid_size n)
  have hpowmul : (L ^ (c + 1)) ^ 2 = L ^ (2 * (c + 1)) := by
    symm
    simpa [Nat.mul_comm] using (Nat.pow_mul L (c + 1) 2)
  have h16 : (16 : Nat) ^ 2 = 256 := by decide
  have hpow : (L ^ (c + 1) * 16) ^ 2 = 256 * L ^ (2 * (c + 1)) := by
    calc
      (L ^ (c + 1) * 16) ^ 2
          = (L ^ (c + 1)) ^ 2 * 16 ^ 2 := by
              simpa using (Nat.mul_pow (L ^ (c + 1)) 16 2)
      _ = 16 ^ 2 * (L ^ (c + 1)) ^ 2 := by
              simp [Nat.mul_comm]
      _ = 256 * L ^ (2 * (c + 1)) := by
              simp [h16, hpowmul, Nat.mul_comm]
  constructor
  · intro h
    have hmul : L ^ (c + 1) * 16 <= n :=
      (Nat.le_div_iff_mul_le (by decide : 0 < (16 : Nat))).1
        (by simpa [Q43_hrThreshold_log2_bound, L] using h)
    have hsq : (L ^ (c + 1) * 16) ^ 2 <= n ^ 2 :=
      (Nat.pow_le_pow_iff_left (n := 2) (a := L ^ (c + 1) * 16) (b := n) (by decide)).2 hmul
    have hsq' : 256 * L ^ (2 * (c + 1)) <= n ^ 2 := by
      simpa [hpow] using hsq
    simpa [Q43_grid_size, Nat.pow_two, L] using hsq'
  · intro h
    have hsq : (L ^ (c + 1) * 16) ^ 2 <= n ^ 2 := by
      have : 256 * L ^ (2 * (c + 1)) <= n ^ 2 := by
        simpa [Q43_grid_size, Nat.pow_two, L] using h
      simpa [hpow] using this
    have hmul : L ^ (c + 1) * 16 <= n :=
      (Nat.pow_le_pow_iff_left (n := 2) (a := L ^ (c + 1) * 16) (b := n) (by decide)).1 hsq
    have hdiv : L ^ (c + 1) <= n / 16 :=
      (Nat.le_div_iff_mul_le (by decide : 0 < (16 : Nat))).2 hmul
    simpa [Q43_hrThreshold_log2_bound, L] using hdiv

-- Q43.S316-flat-eval-quasipoly-hr-threshold-c-bound-proof:
-- exponent comparison for c <= 3.
theorem Q43_log2_pow_le_pow_of_c_le_3 {L c : Nat} (hL : 0 < L) (hc : c <= 3) :
    L ^ (2 * (c + 1)) <= L ^ (c + 5) := by
  have hC : c + 2 <= 5 := by
    simpa using (Nat.add_le_add_right hc 2)
  have h2exp : 2 * (c + 1) <= c + 5 := by
    calc
      2 * (c + 1) = 2 * c + 2 := by
        simp [Nat.mul_add, Nat.mul_one]
      _ = c + c + 2 := by
        simp [Nat.two_mul, Nat.add_assoc]
      _ = c + (c + 2) := by
        simp [Nat.add_assoc]
      _ <= c + 5 := by
        exact Nat.add_le_add_left hC c
  exact Nat.pow_le_pow_right hL h2exp

-- Q43.S312-flat-eval-quasipoly-hr-threshold-derive-log2-bound:
-- scaled log2^5 threshold implies the HR log2 bound when c <= 3.
theorem Q43_hrThreshold_log2_bound_of_scaled {n c : Nat} (hn : 2 <= n) (hc : c <= 3)
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n
      ((Nat.log2 (Q43_grid_size n)) ^ c)) :
    Q43_hrThreshold_log2_bound n c := by
  let L := Nat.log2 (Q43_grid_size n)
  have hscale' :
      (2 * (L ^ c) * Q43_thm41_c1_chernoff_ln) * L ^ 5 <= n ^ 2 := by
    simpa [Q43_grid_size, Nat.pow_two, L] using hscale
  have hscale'' : 2 * Q43_thm41_c1_chernoff_ln * L ^ (c + 5) <= n ^ 2 := by
    simpa [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, L] using hscale'
  have hlog : 1 <= L := Q43_log2_grid_ge_one (n := n) hn
  have hpos : 0 < L := (Nat.succ_le_iff).1 hlog
  have hpowexp : L ^ (2 * (c + 1)) <= L ^ (c + 5) :=
    Q43_log2_pow_le_pow_of_c_le_3 (L := L) (c := c) hpos hc
  have hbig :
      (2 * Q43_thm41_c1_chernoff_ln) * L ^ (2 * (c + 1)) <= n ^ 2 := by
    have hmul :
        (2 * Q43_thm41_c1_chernoff_ln) * L ^ (2 * (c + 1))
          <= (2 * Q43_thm41_c1_chernoff_ln) * L ^ (c + 5) :=
      Nat.mul_le_mul_left _ hpowexp
    exact Nat.le_trans hmul hscale''
  have hc1 : 256 <= 2 * Q43_thm41_c1_chernoff_ln := by
    simp [Q43_thm41_c1_chernoff_ln_eval]
  have hconst :
      256 * L ^ (2 * (c + 1))
        <= (2 * Q43_thm41_c1_chernoff_ln) * L ^ (2 * (c + 1)) :=
    Nat.mul_le_mul_right _ hc1
  have h256 : 256 * L ^ (2 * (c + 1)) <= n ^ 2 :=
    Nat.le_trans hconst hbig
  have hpow :
      256 * (Nat.log2 (Q43_grid_size n)) ^ (2 * (c + 1)) <= Q43_grid_size n := by
    simpa [Q43_grid_size, Nat.pow_two, L] using h256
  exact (Q43_hrThreshold_log2_bound_iff_pow (n := n) (c := c)).2 hpow

-- Q43.S310-flat-eval-quasipoly-hr-eval-apply:
-- apply the flat evaluation statement to the HR threshold bounds via scaled log2^5.
theorem Q43_hrThreshold_of_flat_eval {α : Type} {proof : List (List α)} {n N c s : Nat}
    (hn : 2 <= n) (hc : c <= 3)
    (hflat : Q43_flat_eval_statement n N c proof)
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n
      ((Nat.log2 (Q43_grid_size n)) ^ c))
    (hs : s <= n / 32) :
    Q43_hrThreshold n (Q43_tParam (Q43_lineMax proof)) s := by
  have hlog : Q43_hrThreshold_log2_bound n c :=
    Q43_hrThreshold_log2_bound_of_scaled (n := n) (c := c) hn hc hscale
  have ht' : Q43_tParam (Q43_lineMax proof) <= n / 16 :=
    Nat.le_trans hflat.2 (by simpa [Q43_hrThreshold_log2_bound] using hlog)
  exact Q43_hrThreshold_of_le ht' hs

-- Q43.S313-flat-eval-quasipoly-hr-threshold-remove-c-bound:
-- counterexample: scaled log2^5 does not imply the HR log2 bound for c=9.
def Q43_hrThreshold_counterexample_n : Nat := 13356869453140769898496
def Q43_hrThreshold_counterexample_c : Nat := 9

theorem Q43_hrThreshold_counterexample_scaled :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple Q43_hrThreshold_counterexample_n
      ((Nat.log2 (Q43_grid_size Q43_hrThreshold_counterexample_n)) ^
        Q43_hrThreshold_counterexample_c) := by
  decide

theorem Q43_hrThreshold_counterexample_fail :
    Not (Q43_hrThreshold_log2_bound Q43_hrThreshold_counterexample_n
      Q43_hrThreshold_counterexample_c) := by
  dsimp [Q43_hrThreshold_log2_bound]
  decide

theorem Q43_hrThreshold_log2_bound_scaled_not_forall :
    Not (forall n c,
      Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n
        ((Nat.log2 (Q43_grid_size n)) ^ c) ->
        Q43_hrThreshold_log2_bound n c) := by
  intro h
  exact Q43_hrThreshold_counterexample_fail
    (h _ _ Q43_hrThreshold_counterexample_scaled)

theorem Q43_quasipoly_regime_d_ok_param_tParam {n N M c : Nat} (hn : 2 <= n)
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hM : M <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n
      ((Nat.log2 (Q43_grid_size n)) ^ c)) :
    Q43_thm41_regime_d_ok_param n N ∧
      Q43_tParam M <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) := by
  let proof : List (List Unit) := [List.replicate M ()]
  have hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)) := by
    have hsize_eq : Q43_proofSize proof = M := by
      simp [proof, Q43_proofSize, Q43_lineSize]
    simpa [hsize_eq] using hM
  have hline : Q43_lineMax proof = M := by
    simp [proof, Q43_lineMax, Q43_lineSize]
  have hbundle :=
    Q43_flat_eval_statement_of_quasipoly
      (proof:=proof) (n:=n) (N:=N) (c:=c) hn hN hsize hscale
  have hM' : Q43_tParam M <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) := by
    simpa [Q43_flat_eval_statement, hline] using hbundle.2
  exact ⟨hbundle.1, hM'⟩

theorem Q43_thm41_log2_threshold_c1_grid_param_of_quasipoly {n N c : Nat} (hn : 2 <= n)
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hscale : Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n
      ((Nat.log2 (Q43_grid_size n)) ^ c)) :
    Q43_thm41_log2_threshold_c1_grid_param n N := by
  have hbundle :=
    Q43_quasipoly_regime_d_ok_param_tParam
      (n:=n) (N:=N) (M:=N) (c:=c) hn hN hN hscale
  exact hbundle.1.1

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

-- Q43.S235-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0:
-- Q43.S317-flat-eval-quasipoly-hr-threshold-n0-bridge:
-- lift a ratio bound to the scaled log2^5 threshold (n >= 2).
theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio {n C : Nat}
    (hn : 2 <= n)
    (h : 2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio n) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C := by
  have hlog : 1 <= Nat.log2 (Q43_grid_size n) := Q43_log2_grid_ge_one (n:=n) hn
  have hpos : 0 < (Nat.log2 (Q43_grid_size n)) ^ 5 :=
    Nat.pow_pos (Nat.succ_le_iff.mp hlog)
  exact (Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_iff_ratio (n:=n) (C:=C) hpos).2 h

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

-- Q43.S318-flat-eval-quasipoly-hr-threshold-plateau-lift:
-- lift a ratio bound from 2^k across the lower plateau.
theorem Q43_pow_le_five_mul_pow_sub_two {k : Nat} (hk : 2 <= k) :
    2 ^ k <= 5 * 2 ^ (k - 2) := by
  have hk' : k - 2 + 2 = k := Nat.sub_add_cancel hk
  have hpow : 2 ^ k = 4 * 2 ^ (k - 2) := by
    calc
      2 ^ k = 2 ^ ((k - 2) + 2) := by simp [hk']
      _ = 2 ^ (k - 2) * 2 ^ 2 := by simp [Nat.pow_add]
      _ = 4 * 2 ^ (k - 2) := by
        simp [Nat.mul_comm]
  have h4le5 : 4 <= 5 := by decide
  have hmul : 4 * 2 ^ (k - 2) <= 5 * 2 ^ (k - 2) :=
    Nat.mul_le_mul_right _ h4le5
  simpa [hpow, Nat.mul_comm] using hmul

theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_plateau {k n C : Nat}
    (hk : 2 <= k) (hlo : 2 ^ k <= n) (hhi : n <= 5 * 2 ^ (k - 2))
    (hbase : 2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio (2 ^ k)) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C := by
  have hmono : Q43_grid_ratio (2 ^ k) <= Q43_grid_ratio n :=
    Q43_grid_ratio_mono_on_plateau (k:=k) (n:=2 ^ k) (m:=n) hk
      (by exact Nat.le_refl _) hlo (Q43_pow_le_five_mul_pow_sub_two hk) hhi hlo
  have hratio : 2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio n :=
    Nat.le_trans hbase hmono
  have hpowpos : 0 < 2 ^ (k - 2) := Nat.pow_pos (by decide)
  have hpowge : 1 <= 2 ^ (k - 2) := (Nat.succ_le_iff).2 hpowpos
  have h4le : 4 <= 4 * 2 ^ (k - 2) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mul_le_mul_left 4 hpowge)
  have h2le : 2 <= 4 := by decide
  have h2k : 2 <= 2 ^ k := by
    have hpow : 2 ^ k = 4 * 2 ^ (k - 2) := by
      have hk' : k - 2 + 2 = k := Nat.sub_add_cancel hk
      calc
        2 ^ k = 2 ^ ((k - 2) + 2) := by simp [hk']
        _ = 2 ^ (k - 2) * 2 ^ 2 := by simp [Nat.pow_add]
        _ = 4 * 2 ^ (k - 2) := by
          simp [Nat.mul_comm]
    have h2le' : 2 <= 4 * 2 ^ (k - 2) := Nat.le_trans h2le h4le
    simpa [hpow] using h2le'
  have hn : 2 <= n := Nat.le_trans h2k hlo
  exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio (n:=n) (C:=C) hn hratio

-- Q43.S235-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0:
-- toy explicit threshold for C=1.
def Q43_toy_n0_C1 : Nat := 2 ^ 40

theorem Q43_toy_n0_C1_ok :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple Q43_toy_n0_C1 1 := by
  have hratio :
      2 * 1 * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio (2 ^ 40) := by
    decide
  have hk : 2 <= (40 : Nat) := by decide
  have hlo : 2 ^ 40 <= Q43_toy_n0_C1 := by
    simp [Q43_toy_n0_C1]
  have hhi : Q43_toy_n0_C1 <= 5 * 2 ^ (40 - 2) := by
    dsimp [Q43_toy_n0_C1]
    exact Q43_pow_le_five_mul_pow_sub_two (k:=40) hk
  exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_plateau
    (k:=40) (n:=Q43_toy_n0_C1) (C:=1) hk hlo hhi hratio

-- Q43.S237-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-apply-params-poly-n0-formula:
-- constant-range explicit threshold for C <= 6.
def Q43_toy_Cmax : Nat := 6

theorem Q43_toy_n0_Cmax_ok :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple Q43_toy_n0_C1 Q43_toy_Cmax := by
  decide

theorem Q43_toy_n0_C_le_Cmax {C : Nat} (hC : C <= Q43_toy_Cmax) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple Q43_toy_n0_C1 C := by
  exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_mono_C hC Q43_toy_n0_Cmax_ok

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

-- Q43.S319-flat-eval-quasipoly-hr-threshold-upper-plateau-lift:
-- lift a ratio bound across the upper plateau.
theorem Q43_three_mul_pow_lt_pow_succ {k : Nat} (hk : 2 <= k) :
    3 * 2 ^ (k - 1) < 2 ^ (k + 1) := by
  have hk1 : 1 <= k := Nat.le_trans (by decide : 1 <= 2) hk
  have hpos : 0 < 2 ^ (k - 1) := Nat.pow_pos (by decide)
  have hmul : 3 * 2 ^ (k - 1) < 4 * 2 ^ (k - 1) :=
    (Nat.mul_lt_mul_right (a0 := hpos)).2 (by decide : 3 < 4)
  have hpow : 2 ^ (k + 1) = 4 * 2 ^ (k - 1) := by
    have hk1' : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    have hkp : k + 1 = (k - 1) + 2 := by
      calc
        k + 1 = (k - 1 + 1) + 1 := by
          simp [hk1']
        _ = (k - 1) + 2 := by simp [Nat.add_assoc]
    calc
      2 ^ (k + 1) = 2 ^ ((k - 1) + 2) := by simp [hkp]
      _ = 2 ^ (k - 1) * 2 ^ 2 := by simp [Nat.pow_add]
      _ = 4 * 2 ^ (k - 1) := by
        simp [Nat.mul_comm]
  simpa [hpow, Nat.mul_comm] using hmul

theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_plateau_upper
    {k n C : Nat} (hk : 2 <= k)
    (hlo : 3 * 2 ^ (k - 1) <= n) (hhi : n < 2 ^ (k + 1))
    (hbase : 2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio (3 * 2 ^ (k - 1))) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C := by
  have hmono : Q43_grid_ratio (3 * 2 ^ (k - 1)) <= Q43_grid_ratio n :=
    Q43_grid_ratio_mono_on_plateau_upper (k:=k) (n:=3 * 2 ^ (k - 1)) (m:=n) hk
      (by exact Nat.le_refl _) hlo (Q43_three_mul_pow_lt_pow_succ hk) hhi hlo
  have hratio : 2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio n :=
    Nat.le_trans hbase hmono
  have hpowpos : 0 < 2 ^ (k - 1) := Nat.pow_pos (by decide)
  have hpowge : 1 <= 2 ^ (k - 1) := (Nat.succ_le_iff).2 hpowpos
  have h3le : 3 <= 3 * 2 ^ (k - 1) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mul_le_mul_left 3 hpowge)
  have h2le : 2 <= 3 := by decide
  have h2k : 2 <= 3 * 2 ^ (k - 1) := Nat.le_trans h2le h3le
  have hn : 2 <= n := Nat.le_trans h2k hlo
  exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio (n:=n) (C:=C) hn hratio

-- Q43.S249-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-bridge:
-- counterexample inside the gap [5*2^(k-2), 3*2^(k-1)) for k=12.
def Q43_gap_k : Nat := 12
def Q43_gap_n : Nat := 5792
def Q43_gap_n_succ : Nat := 5793
theorem Q43_gap_n_succ_eq : Q43_gap_n + 1 = Q43_gap_n_succ := by
  decide

theorem Q43_grid_ratio_drop_gap :
    Q43_grid_ratio Q43_gap_n_succ < Q43_grid_ratio Q43_gap_n := by
  decide

def Q43_gap_min_ratio : Nat := Q43_grid_ratio Q43_gap_n_succ

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

theorem Q43_nk_succ_le_three_pow {k : Nat} (hk : 1 <= k) :
    Q43_nk k + 1 <= 3 * 2 ^ (k - 1) := by
  let t : Nat := 2 ^ (k - 1)
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
  simpa [t] using hnk_succ_le

theorem Q43_nk_succ_sq_lt {k : Nat} (hk : 1 <= k) :
    (Q43_nk k + 1) ^ 2 < 2 ^ (2 * k + 2) := by
  let t : Nat := 2 ^ (k - 1)
  have htpos : 0 < t := by
    simpa [t] using (Nat.pow_pos (by decide) : 0 < 2 ^ (k - 1))
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hpowt : 2 ^ (2 * (k - 1)) = t * t := by
    have hpow' : 2 ^ ((k - 1) * 2) = (2 ^ (k - 1)) ^ 2 := Nat.pow_mul 2 (k - 1) 2
    simpa [t, Nat.mul_comm, Nat.pow_two] using hpow'
  have hnk_succ_le : Q43_nk k + 1 <= 3 * t := by
    simpa [t] using (Q43_nk_succ_le_three_pow (k:=k) hk)
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
  have hpow3 : (3 * t) ^ 2 = 9 * t * t := by
    simp [Nat.pow_two, Nat.mul_comm, Nat.mul_left_comm]
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

-- Q43.S322-flat-eval-quasipoly-hr-threshold-nk-base-bound:
-- explicit ratio lower bound at the log2-jump point n_k+1.
theorem Q43_grid_ratio_nk_succ_lower {k : Nat} (hk : 1 <= k) :
    2 ^ (2 * k + 1) / (2 * k + 1) ^ 5 <= Q43_grid_ratio (Q43_nk k + 1) := by
  have hlog := Q43_log2_jump_nk (k := k) hk
  have hlog_succ : Nat.log2 (Q43_grid_size (Q43_nk k + 1)) = 2 * k + 1 := by
    simpa [Q43_grid_size, Nat.pow_two] using hlog.2
  have hgrid : 2 ^ (2 * k + 1) <= Q43_grid_size (Q43_nk k + 1) := by
    have hsq : 2 ^ (2 * k + 1) <= (Q43_nk k + 1) ^ 2 := Q43_nk_succ_sq_ge k
    simpa [Q43_grid_size, Nat.pow_two] using hsq
  have hdiv :
      2 ^ (2 * k + 1) / (2 * k + 1) ^ 5
        <= Q43_grid_size (Q43_nk k + 1) / (2 * k + 1) ^ 5 := by
    exact Nat.div_le_div_right (c := (2 * k + 1) ^ 5) hgrid
  simpa [Q43_grid_ratio, hlog_succ] using hdiv

-- Q43.S320-flat-eval-quasipoly-hr-threshold-gap-lift:
-- log2 |F| stays at 2k+1 on [n_k+1, 2^(k+1)); lift ratio from n_k+1 across the gap.
theorem Q43_log2_grid_size_eq_succ_of_bounds_self {n k : Nat}
    (hlow : 2 ^ (2 * k + 1) <= Q43_grid_size n)
    (hhigh : Q43_grid_size n < 2 ^ (2 * k + 2)) :
    Nat.log2 (Q43_grid_size n) = 2 * k + 1 := by
  have hpos : 0 < 2 ^ (2 * k + 1) := Nat.pow_pos (by decide)
  have hne : Q43_grid_size n ≠ 0 := by
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hpos hlow)
  exact (Nat.log2_eq_iff hne).2 ⟨hlow, hhigh⟩

theorem Q43_log2_grid_size_eq_succ_of_ge_nk {k n : Nat}
    (hlo : Q43_nk k + 1 <= n) (hhi : n < 2 ^ (k + 1)) :
    Nat.log2 (Q43_grid_size n) = 2 * k + 1 := by
  have hlow' : 2 ^ (2 * k + 1) <= Q43_grid_size n := by
    have hnk : 2 ^ (2 * k + 1) <= (Q43_nk k + 1) ^ 2 := Q43_nk_succ_sq_ge k
    have hpow : (Q43_nk k + 1) ^ 2 <= n ^ 2 := Q43_pow_le_pow_of_le hlo
    have hle : 2 ^ (2 * k + 1) <= n ^ 2 := Nat.le_trans hnk hpow
    simpa [Q43_grid_size, Nat.pow_two] using hle
  have hhigh' : Q43_grid_size n < 2 ^ (2 * k + 2) := by
    have hposn : 0 < n := Nat.lt_of_lt_of_le (Nat.succ_pos (Q43_nk k)) hlo
    have hmul1 : n * n < 2 ^ (k + 1) * n :=
      (Nat.mul_lt_mul_right (a0 := hposn)).2 hhi
    have hposp : 0 < 2 ^ (k + 1) := Nat.pow_pos (by decide)
    have hmul2 : 2 ^ (k + 1) * n < 2 ^ (k + 1) * 2 ^ (k + 1) :=
      (Nat.mul_lt_mul_left (a0 := hposp)).2 hhi
    have hmul : n * n < 2 ^ (k + 1) * 2 ^ (k + 1) := Nat.lt_trans hmul1 hmul2
    have hexp : (k + 1) * 2 = 2 * k + 2 := by
      calc
        (k + 1) * 2 = k * 2 + 1 * 2 := by simp [Nat.add_mul]
        _ = 2 * k + 2 := by simp [Nat.mul_comm]
    have hpow' : (2 ^ (k + 1)) ^ 2 = 2 ^ (2 * k + 2) := by
      calc
        (2 ^ (k + 1)) ^ 2 = 2 ^ ((k + 1) * 2) := by
          symm
          exact (Nat.pow_mul 2 (k + 1) 2)
        _ = 2 ^ (2 * k + 2) := by
          simp [hexp]
    have hpow : n ^ 2 < 2 ^ (2 * k + 2) := by
      have hmul' : n * n < (2 ^ (k + 1)) ^ 2 := by
        simpa [Nat.pow_two] using hmul
      simpa [Nat.pow_two, hpow'] using hmul'
    simpa [Q43_grid_size, Nat.pow_two] using hpow
  exact Q43_log2_grid_size_eq_succ_of_bounds_self (n:=n) (k:=k) hlow' hhigh'

-- log2 |F| stays at 2k on [2^k, n_k]; lift ratio from 2^k across the gap-left.
theorem Q43_log2_grid_size_eq_double_of_le_nk {k n : Nat}
    (hlo : 2 ^ k <= n) (hhi : n <= Q43_nk k) :
    Nat.log2 (Q43_grid_size n) = 2 * k := by
  have hpos2k : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hnpos : 0 < n := Nat.lt_of_lt_of_le hpos2k hlo
  have hpow2 : 2 ^ (2 * k) = (2 ^ k) ^ 2 := by
    simpa [Nat.mul_comm] using (Nat.pow_mul 2 k 2)
  have hlow : 2 ^ (2 * k) <= Q43_grid_size n := by
    have hpow : (2 ^ k) ^ 2 <= n ^ 2 :=
      Q43_pow_le_pow_of_le (a := 2 ^ k) (b := n) (n := 2) hlo
    simpa [Q43_grid_size, Nat.pow_two, hpow2] using hpow
  have hhigh : Q43_grid_size n < 2 ^ (2 * k + 1) := by
    have hpow : n ^ 2 <= (Q43_nk k) ^ 2 :=
      Q43_pow_le_pow_of_le (a := n) (b := Q43_nk k) (n := 2) hhi
    have hnk : (Q43_nk k) ^ 2 < 2 ^ (2 * k + 1) := Q43_nk_sq_lt k
    have hpow' : n ^ 2 < 2 ^ (2 * k + 1) := Nat.lt_of_le_of_lt hpow hnk
    simpa [Q43_grid_size, Nat.pow_two] using hpow'
  exact Q43_log2_grid_size_eq_of_bounds (n:=n) (k:=k) hnpos hlow hhigh

theorem Q43_grid_ratio_mono_on_gap_left {k n m : Nat}
    (hn : 2 ^ k <= n) (hm : 2 ^ k <= m)
    (hn_hi : n <= Q43_nk k) (hm_hi : m <= Q43_nk k)
    (h : n <= m) :
    Q43_grid_ratio n <= Q43_grid_ratio m := by
  have hlogn : Nat.log2 (Q43_grid_size n) = 2 * k :=
    Q43_log2_grid_size_eq_double_of_le_nk (k:=k) (n:=n) hn hn_hi
  have hlogm : Nat.log2 (Q43_grid_size m) = 2 * k :=
    Q43_log2_grid_size_eq_double_of_le_nk (k:=k) (n:=m) hm hm_hi
  have hlog : Nat.log2 (Q43_grid_size n) = Nat.log2 (Q43_grid_size m) := by
    simp [hlogn, hlogm]
  exact Q43_grid_ratio_mono_of_log2_eq (n:=n) (m:=m) h hlog

theorem Q43_grid_ratio_mono_on_gap_right {k n m : Nat}
    (hn : Q43_nk k + 1 <= n) (hm : Q43_nk k + 1 <= m)
    (hn_hi : n < 2 ^ (k + 1)) (hm_hi : m < 2 ^ (k + 1))
    (h : n <= m) :
    Q43_grid_ratio n <= Q43_grid_ratio m := by
  have hlogn : Nat.log2 (Q43_grid_size n) = 2 * k + 1 :=
    Q43_log2_grid_size_eq_succ_of_ge_nk (k:=k) (n:=n) hn hn_hi
  have hlogm : Nat.log2 (Q43_grid_size m) = 2 * k + 1 :=
    Q43_log2_grid_size_eq_succ_of_ge_nk (k:=k) (n:=m) hm hm_hi
  have hlog : Nat.log2 (Q43_grid_size n) = Nat.log2 (Q43_grid_size m) := by
    simp [hlogn, hlogm]
  exact Q43_grid_ratio_mono_of_log2_eq (n:=n) (m:=m) h hlog

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

theorem Q43_pow5_even_le_two_pow5_odd {k : Nat} (hk : 4 <= k) :
    (2 * k) ^ 5 <= 2 * (2 * k - 1) ^ 5 := by
  have hmul : 7 * (2 * k) <= 8 * (2 * k - 1) := by
    omega
  have hpow : (7 * (2 * k)) ^ 5 <= (8 * (2 * k - 1)) ^ 5 :=
    Q43_pow_le_pow_of_le hmul
  have hpow' : 7 ^ 5 * (2 * k) ^ 5 <= 8 ^ 5 * (2 * k - 1) ^ 5 := by
    simpa [Nat.mul_pow, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hpow
  have hcoeff : 8 ^ 5 <= 2 * 7 ^ 5 := by decide
  have hpow'' : 7 ^ 5 * (2 * k) ^ 5 <= 2 * 7 ^ 5 * (2 * k - 1) ^ 5 := by
    exact Nat.le_trans hpow' (Nat.mul_le_mul_right _ hcoeff)
  have hpow''' : 7 ^ 5 * (2 * k) ^ 5 <= 7 ^ 5 * (2 * (2 * k - 1) ^ 5) := by
    calc
      7 ^ 5 * (2 * k) ^ 5 <= 2 * 7 ^ 5 * (2 * k - 1) ^ 5 := hpow''
      _ = 7 ^ 5 * (2 * (2 * k - 1) ^ 5) := by
        ac_rfl
  have hpos : 0 < 7 ^ 5 := Nat.pow_pos (by decide)
  have hfinal := Nat.le_of_mul_le_mul_left hpow''' hpos
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfinal

-- compare the explicit base bound against a C-dependent threshold (k>=13).
theorem Q43_gap_right_base_bound_of_c {k C : Nat} (hk : 13 <= k)
    (hC : 3 * (2 * C * Q43_thm41_c1_chernoff_ln) <= 2 * k + 1) :
    2 * C * Q43_thm41_c1_chernoff_ln <= 2 ^ (2 * k + 1) / (2 * k + 1) ^ 5 := by
  let X : Nat := 2 * C * Q43_thm41_c1_chernoff_ln
  let B : Nat := (2 * k + 1) ^ 5
  have hpos : 0 < B := by
    have hbase : 0 < 2 * k + 1 := Nat.succ_pos _
    exact Nat.pow_pos hbase
  have hmul1 : 3 * X * B <= (2 * k + 1) * B := by
    have hmul := Nat.mul_le_mul_right B hC
    simpa [X, B, Nat.mul_assoc] using hmul
  have hpow6 : (2 * k + 1) ^ 6 <= 3 * 2 ^ (2 * k + 1) := Q43_pow6_le_three_pow2_ge13 hk
  have hmul1' : 3 * X * B <= (2 * k + 1) ^ 6 := by
    have hpow : (2 * k + 1) * B = (2 * k + 1) ^ 6 := by
      simp [B, Nat.pow_succ, Nat.mul_comm]
    simpa [hpow] using hmul1
  have hmul2 : 3 * X * B <= 3 * 2 ^ (2 * k + 1) :=
    Nat.le_trans hmul1' hpow6
  have hmul2' : 3 * (X * B) <= 3 * 2 ^ (2 * k + 1) := by
    simpa [Nat.mul_assoc] using hmul2
  have hmul3 : X * B <= 2 ^ (2 * k + 1) :=
    Nat.le_of_mul_le_mul_left hmul2' (by decide : 0 < (3 : Nat))
  have hdiv : X <= 2 ^ (2 * k + 1) / B :=
    (Nat.le_div_iff_mul_le hpos).2 hmul3
  simpa [X, B] using hdiv

-- explicit k0(C) to satisfy the gap-right base bound.
def Q43_gap_right_k0 (C : Nat) : Nat :=
  Nat.max 13 (2 * (2 * C * Q43_thm41_c1_chernoff_ln))

theorem Q43_three_mul_le_two_k_succ {k X : Nat} (h : 2 * X <= k) :
    3 * X <= 2 * k + 1 := by
  have h4 : 4 * X <= 2 * k := by
    have h2 : 2 * (2 * X) <= 2 * k := Nat.mul_le_mul_left 2 h
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2
  have h3 : 3 * X <= 4 * X := by
    exact Nat.mul_le_mul_right X (by decide : 3 <= 4)
  have h4' : 4 * X <= 2 * k + 1 := Nat.le_trans h4 (Nat.le_succ _)
  exact Nat.le_trans h3 h4'

theorem Q43_gap_right_base_bound_of_k0 {C k : Nat} (hk : Q43_gap_right_k0 C <= k) :
    2 * C * Q43_thm41_c1_chernoff_ln <= 2 ^ (2 * k + 1) / (2 * k + 1) ^ 5 := by
  have hk13 : 13 <= k := by
    have hk0 : 13 <= Q43_gap_right_k0 C := by
      unfold Q43_gap_right_k0
      exact Nat.le_max_left _ _
    exact Nat.le_trans hk0 hk
  have hk2 : 2 * (2 * C * Q43_thm41_c1_chernoff_ln) <= k := by
    have hk0 : 2 * (2 * C * Q43_thm41_c1_chernoff_ln) <= Q43_gap_right_k0 C := by
      unfold Q43_gap_right_k0
      exact Nat.le_max_right _ _
    exact Nat.le_trans hk0 hk
  have hC : 3 * (2 * C * Q43_thm41_c1_chernoff_ln) <= 2 * k + 1 :=
    Q43_three_mul_le_two_k_succ hk2
  exact Q43_gap_right_base_bound_of_c (k:=k) (C:=C) hk13 hC

theorem Q43_gap_left_base_bound_of_k0 {k C : Nat}
    (hk0 : Q43_gap_right_k0 C + 1 <= k) :
    2 * C * Q43_thm41_c1_chernoff_ln <= 2 ^ (2 * k) / (2 * k) ^ 5 := by
  let X : Nat := 2 * C * Q43_thm41_c1_chernoff_ln
  have hk13 : 13 <= Q43_gap_right_k0 C := by
    unfold Q43_gap_right_k0
    exact Nat.le_max_left _ _
  have hk14 : 14 <= k := Nat.le_trans (Nat.succ_le_succ hk13) hk0
  have hk4 : 4 <= k := Nat.le_trans (by decide : 4 <= 14) hk14
  have hk0' : Q43_gap_right_k0 C <= k - 1 := by
    omega
  have hbase :
      X <= 2 ^ (2 * (k - 1) + 1) / (2 * (k - 1) + 1) ^ 5 := by
    simpa [X] using (Q43_gap_right_base_bound_of_k0 (C:=C) (k:=k-1) hk0')
  have hpos : 0 < (2 * (k - 1) + 1) ^ 5 := by
    have : 0 < 2 * (k - 1) + 1 := by
      omega
    exact Nat.pow_pos this
  have hbase_mul :
      X * (2 * (k - 1) + 1) ^ 5 <= 2 ^ (2 * (k - 1) + 1) := by
    exact (Nat.le_div_iff_mul_le hpos).1 hbase
  have hshift : 2 * (k - 1) + 1 = 2 * k - 1 := by
    omega
  have hbase_mul' : X * (2 * k - 1) ^ 5 <= 2 ^ (2 * k - 1) := by
    simpa [hshift] using hbase_mul
  have hpow5 : (2 * k) ^ 5 <= 2 * (2 * k - 1) ^ 5 :=
    Q43_pow5_even_le_two_pow5_odd hk4
  have hmul1 : X * (2 * k) ^ 5 <= X * (2 * (2 * k - 1) ^ 5) := by
    exact Nat.mul_le_mul_left X hpow5
  have hmul2 : X * (2 * (2 * k - 1) ^ 5) <= 2 * 2 ^ (2 * k - 1) := by
    have h := Nat.mul_le_mul_left 2 hbase_mul'
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hmul3 : X * (2 * k) ^ 5 <= 2 ^ (2 * k) := by
    have h := Nat.le_trans hmul1 hmul2
    have hpow : 2 * 2 ^ (2 * k - 1) = 2 ^ (2 * k) := by
      have hsub : 2 * k - 1 + 1 = 2 * k := by
        omega
      calc
        2 * 2 ^ (2 * k - 1) = 2 ^ (2 * k - 1) * 2 := by
          simp [Nat.mul_comm]
        _ = 2 ^ ((2 * k - 1) + 1) := by
          simpa using (Nat.pow_succ 2 (2 * k - 1))
        _ = 2 ^ (2 * k) := by
          simp [hsub]
    simpa [hpow] using h
  have hpos2 : 0 < (2 * k) ^ 5 := by
    have : 0 < 2 * k := by
      omega
    exact Nat.pow_pos this
  exact (Nat.le_div_iff_mul_le hpos2).2 (by simpa [X] using hmul3)

theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_right
    {k n C : Nat} (hk : 1 <= k)
    (hk0 : Q43_gap_right_k0 C <= k)
    (hlo : 3 * 2 ^ (k - 1) <= n) (hhi : n < 2 ^ (k + 1)) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C := by
  have hbase :
      2 * C * Q43_thm41_c1_chernoff_ln <= 2 ^ (2 * k + 1) / (2 * k + 1) ^ 5 :=
    Q43_gap_right_base_bound_of_k0 (C:=C) (k:=k) hk0
  have hn_base : Q43_nk k + 1 < 2 ^ (k + 1) := by
    have hsq : (Q43_nk k + 1) ^ 2 < 2 ^ (2 * k + 2) :=
      Q43_nk_succ_sq_lt (k:=k) hk
    have hexp : (k + 1) * 2 = 2 * k + 2 := by
      calc
        (k + 1) * 2 = k * 2 + 1 * 2 := by simp [Nat.add_mul]
        _ = 2 * k + 2 := by simp [Nat.mul_comm]
    have hpow' : (2 ^ (k + 1)) ^ 2 = 2 ^ (2 * k + 2) := by
      calc
        (2 ^ (k + 1)) ^ 2 = 2 ^ ((k + 1) * 2) := by
          symm
          exact (Nat.pow_mul 2 (k + 1) 2)
        _ = 2 ^ (2 * k + 2) := by
          simp [hexp]
    have hsq' : (Q43_nk k + 1) ^ 2 < (2 ^ (k + 1)) ^ 2 := by
      simpa [hpow'] using hsq
    by_cases hge : 2 ^ (k + 1) <= Q43_nk k + 1
    ·
      have hpow : (2 ^ (k + 1)) ^ 2 <= (Q43_nk k + 1) ^ 2 :=
        Q43_pow_le_pow_of_le hge
      exact (False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hpow hsq')))
    · exact Nat.lt_of_not_ge hge
  have hlo' : Q43_nk k + 1 <= n := by
    have hnk : Q43_nk k + 1 <= 3 * 2 ^ (k - 1) :=
      Q43_nk_succ_le_three_pow (k:=k) hk
    exact Nat.le_trans hnk hlo
  have hbase' :
      2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio (Q43_nk k + 1) := by
    exact Nat.le_trans hbase (Q43_grid_ratio_nk_succ_lower (k := k) hk)
  have hmono : Q43_grid_ratio (Q43_nk k + 1) <= Q43_grid_ratio n :=
    Q43_grid_ratio_mono_on_gap_right (k:=k) (n:=Q43_nk k + 1) (m:=n)
      (by exact Nat.le_refl _) hlo' hn_base hhi hlo'
  have hratio : 2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio n :=
    Nat.le_trans hbase' hmono
  have hnk : 2 ^ k <= Q43_nk k := Q43_nk_ge_pow k
  have h2k : 2 <= 2 ^ k := by
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hpos : 0 < 2 ^ (k - 1) := Nat.pow_pos (by decide)
    have hle : 1 <= 2 ^ (k - 1) := (Nat.succ_le_iff).2 hpos
    have hmul : 2 <= 2 ^ (k - 1) * 2 := by
      simpa [Nat.mul_comm] using (Nat.mul_le_mul_right 2 hle)
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by simp [hk1]
        _ = 2 ^ (k - 1) * 2 := by
          simpa [Nat.mul_comm] using (Nat.pow_succ 2 (k - 1))
    simpa [hpow] using hmul
  have h2nk : 2 <= Q43_nk k := Nat.le_trans h2k hnk
  have h2nk1 : 2 <= Q43_nk k + 1 := Nat.le_trans h2nk (Nat.le_succ _)
  have hn : 2 <= n := Nat.le_trans h2nk1 hlo'
  exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio (n:=n) (C:=C) hn hratio

-- cover the gap-left band [2^k, 3*2^(k-1)] using the n_k split.
theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_left
    {k n C : Nat} (hk0 : Q43_gap_right_k0 C + 1 <= k)
    (hlo : 2 ^ k <= n) (hhi : n <= 3 * 2 ^ (k - 1)) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C := by
  have hk13 : 13 <= Q43_gap_right_k0 C := by
    unfold Q43_gap_right_k0
    exact Nat.le_max_left _ _
  have hk14 : 14 <= k := Nat.le_trans (Nat.succ_le_succ hk13) hk0
  have hk4 : 4 <= k := Nat.le_trans (by decide : 4 <= 14) hk14
  have hk1 : 1 <= k := Nat.le_trans (by decide : 1 <= 4) hk4
  have hk2 : 2 <= k := Nat.le_trans (by decide : 2 <= 4) hk4
  have hbase :
      2 * C * Q43_thm41_c1_chernoff_ln <= 2 ^ (2 * k) / (2 * k) ^ 5 :=
    Q43_gap_left_base_bound_of_k0 (k:=k) (C:=C) hk0
  have hlog_base : Nat.log2 (Q43_grid_size (2 ^ k)) = 2 * k :=
    Q43_log2_grid_size_eq_double_of_le_nk (k:=k) (n:=2 ^ k)
      (by exact Nat.le_refl _) (Q43_nk_ge_pow k)
  have hgrid_base : Q43_grid_size (2 ^ k) = 2 ^ (2 * k) := by
    calc
      Q43_grid_size (2 ^ k) = (2 ^ k) ^ 2 := by
        simp [Q43_grid_size, Nat.pow_two]
      _ = 2 ^ (2 * k) := by
        symm
        simpa [Nat.mul_comm] using (Nat.pow_mul 2 k 2)
  have hbase_ratio :
      2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio (2 ^ k) := by
    simpa [Q43_grid_ratio, hlog_base, hgrid_base] using hbase
  have hk0' : Q43_gap_right_k0 C <= k := by
    exact Nat.le_trans (Nat.le_succ _) hk0
  have hbase_right :
      2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio (Q43_nk k + 1) := by
    have hbase' :
        2 * C * Q43_thm41_c1_chernoff_ln <= 2 ^ (2 * k + 1) / (2 * k + 1) ^ 5 :=
      Q43_gap_right_base_bound_of_k0 (C:=C) (k:=k) hk0'
    have hratio' :
        2 ^ (2 * k + 1) / (2 * k + 1) ^ 5 <= Q43_grid_ratio (Q43_nk k + 1) :=
      Q43_grid_ratio_nk_succ_lower (k:=k) hk1
    exact Nat.le_trans hbase' hratio'
  have h2k : 2 <= 2 ^ k := by
    have hk1' : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    have hpos : 0 < 2 ^ (k - 1) := Nat.pow_pos (by decide)
    have hle : 1 <= 2 ^ (k - 1) := (Nat.succ_le_iff).2 hpos
    have hmul : 2 <= 2 ^ (k - 1) * 2 := by
      simpa [Nat.mul_comm] using (Nat.mul_le_mul_right 2 hle)
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by simp [hk1']
        _ = 2 ^ (k - 1) * 2 := by
          simpa [Nat.mul_comm] using (Nat.pow_succ 2 (k - 1))
    simpa [hpow] using hmul
  have hn2 : 2 <= n := Nat.le_trans h2k hlo
  by_cases hnk : n <= Q43_nk k
  ·
    have hmono : Q43_grid_ratio (2 ^ k) <= Q43_grid_ratio n :=
      Q43_grid_ratio_mono_on_gap_left (k:=k) (n:=2 ^ k) (m:=n)
        (by exact Nat.le_refl _) hlo (Q43_nk_ge_pow k) hnk hlo
    have hratio : 2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio n :=
      Nat.le_trans hbase_ratio hmono
    exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio (n:=n) (C:=C) hn2 hratio
  ·
    have hnk_lt : Q43_nk k < n := Nat.lt_of_not_ge hnk
    have hnk_succ : Q43_nk k + 1 <= n := (Nat.succ_le_iff).2 hnk_lt
    have h3lt : 3 * 2 ^ (k - 1) < 2 ^ (k + 1) :=
      Q43_three_mul_pow_lt_pow_succ (k:=k) hk2
    have hhi' : n < 2 ^ (k + 1) := Nat.lt_of_le_of_lt hhi h3lt
    have hnk_hi : Q43_nk k + 1 < 2 ^ (k + 1) := by
      have hnk_le : Q43_nk k + 1 <= 3 * 2 ^ (k - 1) :=
        Q43_nk_succ_le_three_pow (k:=k) hk1
      exact Nat.lt_of_le_of_lt hnk_le h3lt
    have hmono : Q43_grid_ratio (Q43_nk k + 1) <= Q43_grid_ratio n :=
      Q43_grid_ratio_mono_on_gap_right (k:=k) (n:=Q43_nk k + 1) (m:=n)
        (by exact Nat.le_refl _) hnk_succ hnk_hi hhi' hnk_succ
    have hratio : 2 * C * Q43_thm41_c1_chernoff_ln <= Q43_grid_ratio n :=
      Nat.le_trans hbase_right hmono
    exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio (n:=n) (C:=C) hn2 hratio

theorem Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_band
    {k n C : Nat} (hk0 : Q43_gap_right_k0 C + 1 <= k)
    (hlo : 2 ^ k <= n) (hhi : n < 2 ^ (k + 1)) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C := by
  by_cases hgap : n <= 3 * 2 ^ (k - 1)
  ·
    exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_left
      (k:=k) (n:=n) (C:=C) hk0 hlo hgap
  ·
    have hgap' : 3 * 2 ^ (k - 1) <= n := by
      exact Nat.le_of_lt (Nat.lt_of_not_ge hgap)
    have hk13 : 13 <= Q43_gap_right_k0 C := by
      unfold Q43_gap_right_k0
      exact Nat.le_max_left _ _
    have hk14 : 14 <= k := Nat.le_trans (Nat.succ_le_succ hk13) hk0
    have hk1 : 1 <= k := Nat.le_trans (by decide : 1 <= 14) hk14
    have hk0' : Q43_gap_right_k0 C <= k := by
      exact Nat.le_trans (Nat.le_succ _) hk0
    exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_right
      (k:=k) (n:=n) (C:=C) hk1 hk0' hgap' hhi

def Q43_gap_right_n0 (C : Nat) : Nat :=
  3 * 2 ^ (Q43_gap_right_k0 C - 1)

theorem Q43_gap_right_k0_ge_one (C : Nat) : 1 <= Q43_gap_right_k0 C := by
  have hk13 : 13 <= Q43_gap_right_k0 C := by
    unfold Q43_gap_right_k0
    exact Nat.le_max_left _ _
  exact Nat.le_trans (by decide : 1 <= 13) hk13

theorem Q43_gap_right_n0_ge_two (C : Nat) : 2 <= Q43_gap_right_n0 C := by
  have hpow : 1 <= 2 ^ (Q43_gap_right_k0 C - 1) := by
    have hpos : 0 < 2 ^ (Q43_gap_right_k0 C - 1) := Nat.pow_pos (by decide)
    exact (Nat.succ_le_iff).2 hpos
  have h3 : 3 <= 3 * 2 ^ (Q43_gap_right_k0 C - 1) := by
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_left 3 hpow)
  have h2 : 2 <= 3 := by decide
  have hle : 2 <= 3 * 2 ^ (Q43_gap_right_k0 C - 1) := Nat.le_trans h2 h3
  simpa [Q43_gap_right_n0] using hle

theorem Q43_gap_right_apply_n0 {n C : Nat}
    (hlo : Q43_gap_right_n0 C <= n)
    (hhi : n < 2 ^ (Q43_gap_right_k0 C + 1)) :
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C := by
  have hk : 1 <= Q43_gap_right_k0 C := Q43_gap_right_k0_ge_one C
  have hk0 : Q43_gap_right_k0 C <= Q43_gap_right_k0 C := Nat.le_refl _
  have hlo' : 3 * 2 ^ (Q43_gap_right_k0 C - 1) <= n := by
    simpa [Q43_gap_right_n0] using hlo
  exact Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_right
    (k:=Q43_gap_right_k0 C) (n:=n) (C:=C) hk hk0 hlo' hhi

-- Q43.S327-flat-eval-quasipoly-hr-threshold-regime-d-thread:
-- thread the gap-right n0 threshold into the regime-d bundle.
theorem Q43_thm41_regime_d_ok_param_of_gap_right_n0 {n N C : Nat}
    (hC : 1 <= C)
    (hlog : Nat.log2 N <= C * Nat.log2 (Q43_grid_size n))
    (hlo : Q43_gap_right_n0 C <= n)
    (hhi : n < 2 ^ (Q43_gap_right_k0 C + 1)) :
    Q43_thm41_regime_d_ok_param n N := by
  have hn : 2 <= n := Nat.le_trans (Q43_gap_right_n0_ge_two C) hlo
  have hscale :
      Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n C :=
    Q43_gap_right_apply_n0 (n:=n) (C:=C) hlo hhi
  exact Q43_thm41_regime_d_ok_param_of_scaled (n:=n) (N:=N) (C:=C) hn hC hlog hscale

-- Q43.S329-flat-eval-quasipoly-hr-threshold-flat-eval-apply-gap-right:
-- apply the gap-right regime-d wrapper to the quasi-poly flat-eval chain.
theorem Q43_quasipoly_regime_d_ok_param_lineMax_of_gap_right {α : Type}
    {proof : List (List α)} {n N c : Nat}
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hlo : Q43_gap_right_n0 ((Nat.log2 (Q43_grid_size n)) ^ c) <= n)
    (hhi : n < 2 ^ (Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) + 1)) :
    Q43_thm41_regime_d_ok_param n N ∧
      Q43_tParam (Q43_lineMax proof) <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) := by
  let L := Nat.log2 (Q43_grid_size n)
  have hbounds :=
    Q43_quasipoly_grid_eval_bounds (proof:=proof) (n:=n) (N:=N) (c:=c) hN hsize
  have hlog : Nat.log2 N <= L ^ (c + 1) := by
    simpa [L] using hbounds.1
  have hlog_mul : Nat.log2 N <= L ^ c * L := by
    simpa [Nat.pow_succ, L] using hlog
  have hlo' : Q43_gap_right_n0 (L ^ c) <= n := by
    simpa [L] using hlo
  have hn : 2 <= n := Nat.le_trans (Q43_gap_right_n0_ge_two (C:=L ^ c)) hlo'
  have hlog1 : 1 <= L := by
    simpa [L] using (Q43_log2_grid_ge_one (n:=n) hn)
  have hpos : 0 < L := (Nat.succ_le_iff).1 hlog1
  have hpow_pos : 0 < L ^ c := Nat.pow_pos hpos
  have hC : 1 <= L ^ c := (Nat.succ_le_iff).2 hpow_pos
  have hreg : Q43_thm41_regime_d_ok_param n N :=
    Q43_thm41_regime_d_ok_param_of_gap_right_n0
      (n:=n) (N:=N) (C:=L ^ c) hC hlog_mul hlo' (by simpa [L] using hhi)
  have hM :
      Q43_tParam (Q43_lineMax proof) <= (Nat.log2 (Q43_grid_size n)) ^ (c + 1) := by
    simpa [L] using hbounds.2
  exact ⟨hreg, hM⟩

@[simp] theorem Q43_flat_eval_statement_of_quasipoly_gap_right {α : Type}
    {proof : List (List α)} {n N c : Nat}
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hlo : Q43_gap_right_n0 ((Nat.log2 (Q43_grid_size n)) ^ c) <= n)
    (hhi : n < 2 ^ (Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) + 1)) :
    Q43_flat_eval_statement n N c proof := by
  have hbundle :=
    Q43_quasipoly_regime_d_ok_param_lineMax_of_gap_right
      (proof:=proof) (n:=n) (N:=N) (c:=c) hN hsize hlo hhi
  simpa [Q43_flat_eval_statement] using hbundle

-- Q43.S332-flat-eval-quasipoly-hr-threshold-gap-bridge:
-- package the k-parameter gap-right HR threshold under an existential k.
theorem Q43_hrThreshold_of_quasipoly_gap_right_exists {α : Type}
    {proof : List (List α)} {n N c s : Nat}
    (hk :
      ∃ k, 1 <= k ∧
        Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) <= k ∧
        3 * 2 ^ (k - 1) <= n ∧ n < 2 ^ (k + 1))
    (hc : c <= 3)
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hs : s <= n / 32) :
    Q43_hrThreshold n (Q43_tParam (Q43_lineMax proof)) s := by
  rcases hk with ⟨k, hk1, hk0, hlo, hhi⟩
  let L := Nat.log2 (Q43_grid_size n)
  have hpow : 1 <= 2 ^ (k - 1) := by
    have hpos : 0 < 2 ^ (k - 1) := Nat.pow_pos (by decide)
    exact (Nat.succ_le_iff).2 hpos
  have h3 : 3 <= 3 * 2 ^ (k - 1) := by
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_left 3 hpow)
  have h2 : 2 <= 3 := by decide
  have hn : 2 <= n := Nat.le_trans (Nat.le_trans h2 h3) hlo
  have hscale :
      Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n (L ^ c) :=
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_right
      (k:=k) (n:=n) (C:=L ^ c) hk1 hk0 hlo hhi
  have hbundle :=
    Q43_quasipoly_regime_d_ok_param_lineMax
      (proof:=proof) (n:=n) (N:=N) (c:=c)
      hn hN hsize (by simpa [L] using hscale)
  have hflat : Q43_flat_eval_statement n N c proof := by
    simpa [Q43_flat_eval_statement] using hbundle
  exact Q43_hrThreshold_of_flat_eval
    (proof:=proof) (n:=n) (N:=N) (c:=c) (s:=s) hn hc hflat
    (by simpa [L] using hscale) hs

-- Q43.S333-flat-eval-quasipoly-hr-threshold-gap-choose-k:
-- choose k = log2 n for the upper plateau band.
theorem Q43_lt_pow_succ_log2 (n : Nat) : n < 2 ^ (Nat.log2 n + 1) := by
  cases n with
  | zero =>
      decide
  | succ n =>
      by_cases hle : 2 ^ (Nat.log2 (Nat.succ n) + 1) <= Nat.succ n
      ·
        have hlog : Nat.log2 (Nat.succ n) + 1 <= Nat.log2 (Nat.succ n) :=
          (Nat.le_log2 (Nat.succ_ne_zero _)).2 hle
        exact (False.elim ((Nat.not_lt_of_ge hlog) (Nat.lt_succ_self _)))
      ·
        exact Nat.lt_of_not_ge hle

theorem Q43_gap_right_choose_k_of_log2 {n C : Nat}
    (hk0 : Q43_gap_right_k0 C <= Nat.log2 n)
    (hlo : 3 * 2 ^ (Nat.log2 n - 1) <= n) :
    ∃ k, 1 <= k ∧
      Q43_gap_right_k0 C <= k ∧
      3 * 2 ^ (k - 1) <= n ∧ n < 2 ^ (k + 1) := by
  refine ⟨Nat.log2 n, ?_, hk0, hlo, ?_⟩
  · exact Nat.le_trans (Q43_gap_right_k0_ge_one C) hk0
  · simpa using (Q43_lt_pow_succ_log2 n)

theorem Q43_hrThreshold_of_quasipoly_gap_right_log2 {α : Type}
    {proof : List (List α)} {n N c s : Nat}
    (hk0 : Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) <= Nat.log2 n)
    (hlo : 3 * 2 ^ (Nat.log2 n - 1) <= n)
    (hc : c <= 3)
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hs : s <= n / 32) :
    Q43_hrThreshold n (Q43_tParam (Q43_lineMax proof)) s := by
  have hk :
      ∃ k, 1 <= k ∧
        Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) <= k ∧
        3 * 2 ^ (k - 1) <= n ∧ n < 2 ^ (k + 1) :=
    Q43_gap_right_choose_k_of_log2
      (n:=n) (C:=((Nat.log2 (Q43_grid_size n)) ^ c)) hk0 hlo
  exact Q43_hrThreshold_of_quasipoly_gap_right_exists
    (proof:=proof) (n:=n) (N:=N) (c:=c) (s:=s)
    hk hc hN hsize hs

-- Q43.S330-flat-eval-quasipoly-hr-threshold-hr-apply-gap-right:
-- use the gap-right flat-eval statement to obtain the HR threshold.
theorem Q43_hrThreshold_of_quasipoly_gap_right {α : Type}
    {proof : List (List α)} {n N c s : Nat}
    (hc : c <= 3)
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hlo : Q43_gap_right_n0 ((Nat.log2 (Q43_grid_size n)) ^ c) <= n)
    (hhi : n < 2 ^ (Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) + 1))
    (hs : s <= n / 32) :
    Q43_hrThreshold n (Q43_tParam (Q43_lineMax proof)) s := by
  let L := Nat.log2 (Q43_grid_size n)
  have hlo' : 3 * 2 ^ (Q43_gap_right_k0 (L ^ c) - 1) <= n := by
    simpa [Q43_gap_right_n0, L] using hlo
  have hhi' : n < 2 ^ (Q43_gap_right_k0 (L ^ c) + 1) := by
    simpa [L] using hhi
  have hk :
      ∃ k, 1 <= k ∧
        Q43_gap_right_k0 (L ^ c) <= k ∧
        3 * 2 ^ (k - 1) <= n ∧ n < 2 ^ (k + 1) := by
    refine ⟨Q43_gap_right_k0 (L ^ c), Q43_gap_right_k0_ge_one (L ^ c), Nat.le_refl _, hlo', ?_⟩
    simpa using hhi'
  exact Q43_hrThreshold_of_quasipoly_gap_right_exists
    (proof:=proof) (n:=n) (N:=N) (c:=c) (s:=s)
    (by simpa [L] using hk) hc hN hsize hs

-- gap-right lower bounds imply n >= 2.
theorem Q43_gap_right_lower_bound_ge_two {k n : Nat}
    (hlo : 3 * 2 ^ (k - 1) <= n) : 2 <= n := by
  have hpow : 1 <= 2 ^ (k - 1) := by
    have hpos : 0 < 2 ^ (k - 1) := Nat.pow_pos (by decide)
    exact (Nat.succ_le_iff).2 hpos
  have h3 : 3 <= 3 * 2 ^ (k - 1) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.mul_le_mul_left 3 hpow)
  have h2 : 2 <= 3 := by decide
  exact Nat.le_trans (Nat.le_trans h2 h3) hlo

-- Q43.S335-flat-eval-quasipoly-hr-threshold-gap-left-hr-apply:
-- apply the gap-left cover by lifting the scaled threshold across the full band.
theorem Q43_flat_eval_statement_of_quasipoly_gap_band_k {α : Type}
    {proof : List (List α)} {n N c k : Nat}
    (hk0 : Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) + 1 <= k)
    (hlo : 2 ^ k <= n)
    (hhi : n < 2 ^ (k + 1))
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1))) :
    Q43_flat_eval_statement n N c proof := by
  let L := Nat.log2 (Q43_grid_size n)
  have hk0' : Q43_gap_right_k0 (L ^ c) + 1 <= k := by
    simpa [L] using hk0
  have hk1 : 1 <= k := by
    have hk0_ge_one : 1 <= Q43_gap_right_k0 (L ^ c) :=
      Q43_gap_right_k0_ge_one (L ^ c)
    have hk0_le : Q43_gap_right_k0 (L ^ c) <= k :=
      Nat.le_trans (Nat.le_succ _) hk0'
    exact Nat.le_trans hk0_ge_one hk0_le
  have h2k : 2 <= 2 ^ k := by
    have hk1' : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    have hpos : 0 < 2 ^ (k - 1) := Nat.pow_pos (by decide)
    have hle : 1 <= 2 ^ (k - 1) := (Nat.succ_le_iff).2 hpos
    have hmul : 2 <= 2 ^ (k - 1) * 2 := by
      simpa [Nat.mul_comm] using (Nat.mul_le_mul_right 2 hle)
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by simp [hk1']
        _ = 2 ^ (k - 1) * 2 := by
          simpa [Nat.mul_comm] using (Nat.pow_succ 2 (k - 1))
    simpa [hpow] using hmul
  have hn : 2 <= n := Nat.le_trans h2k hlo
  have hscale :
      Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n (L ^ c) :=
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_band
      (k:=k) (n:=n) (C:=L ^ c) hk0' hlo hhi
  have hbundle :=
    Q43_quasipoly_regime_d_ok_param_lineMax
      (proof:=proof) (n:=n) (N:=N) (c:=c) hn hN hsize (by simpa [L] using hscale)
  simpa [Q43_flat_eval_statement] using hbundle

-- Q43.S331-flat-eval-quasipoly-hr-threshold-extend-upper:
-- extend gap-right application by allowing any k >= k0(C).
theorem Q43_flat_eval_statement_of_quasipoly_gap_right_k {α : Type}
    {proof : List (List α)} {n N c k : Nat}
    (hk0 : Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) + 1 <= k)
    (hlo : 3 * 2 ^ (k - 1) <= n)
    (hhi : n < 2 ^ (k + 1))
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1))) :
    Q43_flat_eval_statement n N c proof := by
  let L := Nat.log2 (Q43_grid_size n)
  have hk13 : 13 <= Q43_gap_right_k0 (L ^ c) := by
    unfold Q43_gap_right_k0
    exact Nat.le_max_left _ _
  have hk14 : 14 <= k := Nat.le_trans (Nat.succ_le_succ hk13) hk0
  have hk1 : 1 <= k := Nat.le_trans (by decide : 1 <= 14) hk14
  have hlo2 : 2 ^ k <= n := by
    have hk1' : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    have hmul : 2 ^ (k - 1) * 2 <= 3 * 2 ^ (k - 1) := by
      have h2le3 : 2 <= 3 := by decide
      have hmul' : 2 * 2 ^ (k - 1) <= 3 * 2 ^ (k - 1) :=
        Nat.mul_le_mul_right _ h2le3
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul'
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by simp [hk1']
        _ = 2 ^ (k - 1) * 2 := by
          simpa [Nat.mul_comm] using (Nat.pow_succ 2 (k - 1))
    have hpow' : 2 ^ k <= 3 * 2 ^ (k - 1) := by
      simpa [hpow] using hmul
    exact Nat.le_trans hpow' hlo
  exact Q43_flat_eval_statement_of_quasipoly_gap_band_k
    (proof:=proof) (n:=n) (N:=N) (c:=c) (k:=k)
    hk0 hlo2 hhi hN hsize

theorem Q43_hrThreshold_of_quasipoly_gap_band_k {α : Type}
    {proof : List (List α)} {n N c k s : Nat}
    (hk0 : Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) + 1 <= k)
    (hc : c <= 3)
    (hlo : 2 ^ k <= n)
    (hhi : n < 2 ^ (k + 1))
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hs : s <= n / 32) :
    Q43_hrThreshold n (Q43_tParam (Q43_lineMax proof)) s := by
  let L := Nat.log2 (Q43_grid_size n)
  have hk0' : Q43_gap_right_k0 (L ^ c) + 1 <= k := by
    simpa [L] using hk0
  have hk1 : 1 <= k := by
    have hk0_ge_one : 1 <= Q43_gap_right_k0 (L ^ c) :=
      Q43_gap_right_k0_ge_one (L ^ c)
    have hk0_le : Q43_gap_right_k0 (L ^ c) <= k :=
      Nat.le_trans (Nat.le_succ _) hk0'
    exact Nat.le_trans hk0_ge_one hk0_le
  have h2k : 2 <= 2 ^ k := by
    have hk1' : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    have hpos : 0 < 2 ^ (k - 1) := Nat.pow_pos (by decide)
    have hle : 1 <= 2 ^ (k - 1) := (Nat.succ_le_iff).2 hpos
    have hmul : 2 <= 2 ^ (k - 1) * 2 := by
      simpa [Nat.mul_comm] using (Nat.mul_le_mul_right 2 hle)
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by simp [hk1']
        _ = 2 ^ (k - 1) * 2 := by
          simpa [Nat.mul_comm] using (Nat.pow_succ 2 (k - 1))
    simpa [hpow] using hmul
  have hn : 2 <= n := Nat.le_trans h2k hlo
  have hflat :
      Q43_flat_eval_statement n N c proof :=
    Q43_flat_eval_statement_of_quasipoly_gap_band_k
      (proof:=proof) (n:=n) (N:=N) (c:=c) (k:=k)
      hk0 hlo hhi hN hsize
  have hscale :
      Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple n (L ^ c) :=
    Q43_thm41_log2_threshold_c1_grid_pow5_scaled_simple_of_ratio_gap_band
      (k:=k) (n:=n) (C:=L ^ c) hk0' hlo hhi
  exact Q43_hrThreshold_of_flat_eval
    (proof:=proof) (n:=n) (N:=N) (c:=c) (s:=s) hn hc hflat
    (by simpa [L] using hscale) hs

theorem Q43_hrThreshold_of_quasipoly_gap_right_k {α : Type}
    {proof : List (List α)} {n N c k s : Nat}
    (hk0 : Q43_gap_right_k0 ((Nat.log2 (Q43_grid_size n)) ^ c) + 1 <= k)
    (hc : c <= 3)
    (hlo : 3 * 2 ^ (k - 1) <= n)
    (hhi : n < 2 ^ (k + 1))
    (hN : N <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hsize : Q43_proofSize proof <= 2 ^ ((Nat.log2 (Q43_grid_size n)) ^ (c + 1)))
    (hs : s <= n / 32) :
    Q43_hrThreshold n (Q43_tParam (Q43_lineMax proof)) s := by
  let L := Nat.log2 (Q43_grid_size n)
  have hk13 : 13 <= Q43_gap_right_k0 (L ^ c) := by
    unfold Q43_gap_right_k0
    exact Nat.le_max_left _ _
  have hk14 : 14 <= k := Nat.le_trans (Nat.succ_le_succ hk13) hk0
  have hk1 : 1 <= k := Nat.le_trans (by decide : 1 <= 14) hk14
  have hlo2 : 2 ^ k <= n := by
    have hk1' : k - 1 + 1 = k := Nat.sub_add_cancel hk1
    have hmul : 2 ^ (k - 1) * 2 <= 3 * 2 ^ (k - 1) := by
      have h2le3 : 2 <= 3 := by decide
      have hmul' : 2 * 2 ^ (k - 1) <= 3 * 2 ^ (k - 1) :=
        Nat.mul_le_mul_right _ h2le3
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul'
    have hpow : 2 ^ k = 2 ^ (k - 1) * 2 := by
      calc
        2 ^ k = 2 ^ (k - 1 + 1) := by simp [hk1']
        _ = 2 ^ (k - 1) * 2 := by
          simpa [Nat.mul_comm] using (Nat.pow_succ 2 (k - 1))
    have hpow' : 2 ^ k <= 3 * 2 ^ (k - 1) := by
      simpa [hpow] using hmul
    exact Nat.le_trans hpow' hlo
  exact Q43_hrThreshold_of_quasipoly_gap_band_k
    (proof:=proof) (n:=n) (N:=N) (c:=c) (k:=k) (s:=s)
    hk0 hc hlo2 hhi hN hsize hs

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

-- Q43.S279-gap-min-global-bridge-apply:
-- apply the uniform n_k bridge to the global gap-min ratio at k=12.
theorem Q43_gap_min_ratio_drop_global :
    Q43_gap_min_ratio < Q43_grid_ratio Q43_gap_n := by
  have hk : 12 <= Q43_gap_k := by
    simp [Q43_gap_k]
  have hdrop := Q43_grid_ratio_drop_nk (k := Q43_gap_k) hk
  simpa [Q43_gap_min_ratio, Q43_gap_k, Q43_nk_eq_gap_n12, Q43_gap_n_succ_eq] using hdrop

end PvNP
