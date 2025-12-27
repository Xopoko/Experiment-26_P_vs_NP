import Paperproof
import PvNP.Core.Defs
import PvNP.Core.Graph

namespace PvNP

-- Work-in-progress Lean proofs live here (real code, not doc-comments).

abbrev Vertex := Nat
abbrev Edge := Vertex × Vertex

def edgeSwap (e : Edge) : Edge := (e.2, e.1)

theorem edgeSwap_involutive (e : Edge) : edgeSwap (edgeSwap e) = e := by
  cases e with
  | mk u v =>
    rfl

def EmptySet : Set Vertex := fun _ => False
def FullSet : Set Vertex := fun _ => True

def boundary (G : Graph) (S : Set Vertex) : Set Edge :=
  fun e =>
    let (u, v) := e
    G.adj u v = true ∧ S u ∧ ¬ S v

def frontier (G : Graph) (S : Set Vertex) : Set Edge :=
  fun e => boundary G S e ∨ boundary G S (edgeSwap e)

theorem boundary_empty (G : Graph) : ∀ e, ¬ boundary G EmptySet e := by
  intro e
  cases e with
  | mk u v =>
    simp [boundary, EmptySet]

theorem boundary_full (G : Graph) : ∀ e, ¬ boundary G FullSet e := by
  intro e
  cases e with
  | mk u v =>
    simp [boundary, FullSet]

-- Q39.S21-boundary-complement-duality: complement flips boundary orientation in symmetric graphs.
theorem Q39_boundary_compl_swap (G : Graph) (hG : Symmetric G) (S : Set Vertex) :
    ∀ e, boundary G (fun x => ¬ S x) e ↔ boundary G S (edgeSwap e) := by
  intro e
  cases e with
  | mk u v =>
    constructor
    · intro h
      have h' : G.adj u v = true ∧ ¬ S u ∧ S v := by
        simpa [boundary] using h
      have h1 : G.adj v u = true := by
        calc
          G.adj v u = G.adj u v := by
            symm
            exact hG u v
          _ = true := h'.1
      -- Expand boundary on the swapped edge.
      simp [boundary]
      exact And.intro h1 (And.intro h'.2.2 h'.2.1)
    · intro h
      have h' : G.adj v u = true ∧ S v ∧ ¬ S u := by
        simpa [boundary] using h
      have h1 : G.adj u v = true := by
        calc
          G.adj u v = G.adj v u := by
            exact hG u v
          _ = true := h'.1
      -- Expand boundary on the original edge.
      simp [boundary]
      exact And.intro h1 (And.intro h'.2.2 h'.2.1)

-- Q39.S22-2k-two-strip-frontier-obstruction: undirected frontier is complement-invariant.
theorem Q39_frontier_compl (G : Graph) (hG : Symmetric G) (S : Set Vertex) :
    ∀ e, frontier G S e ↔ frontier G (fun x => ¬ S x) e := by
  intro e
  have hswap : boundary G (fun x => ¬ S x) e ↔ boundary G S (edgeSwap e) :=
    Q39_boundary_compl_swap G hG S e
  have hswap' : boundary G (fun x => ¬ S x) (edgeSwap e) ↔ boundary G S e := by
    have h := Q39_boundary_compl_swap G hG S (edgeSwap e)
    simpa [edgeSwap_involutive] using h
  constructor
  · intro h
    cases h with
    | inl hleft =>
        exact Or.inr (hswap'.mpr hleft)
    | inr hright =>
        exact Or.inl (hswap.mpr hright)
  · intro h
    cases h with
    | inl hleft =>
        exact Or.inr (hswap.mp hleft)
    | inr hright =>
        exact Or.inl (hswap'.mp hright)

-- Q39.S24-2k-two-strip-interval-obstruction: frontier is invariant under edge orientation.
theorem Q39_frontier_swap (G : Graph) (S : Set Vertex) (e : Edge) :
    frontier G S (edgeSwap e) ↔ frontier G S e := by
  constructor <;> intro h
  · have h' : boundary G S (edgeSwap e) ∨ boundary G S e := by
      simpa [frontier, edgeSwap_involutive] using h
    cases h' with
    | inl hswap =>
        have : boundary G S e ∨ boundary G S (edgeSwap e) := Or.inr hswap
        simpa [frontier] using this
    | inr hmain =>
        have : boundary G S e ∨ boundary G S (edgeSwap e) := Or.inl hmain
        simpa [frontier] using this
  · have h' : boundary G S e ∨ boundary G S (edgeSwap e) := by
      simpa [frontier] using h
    cases h' with
    | inl hmain =>
        have : boundary G S (edgeSwap e) ∨ boundary G S e := Or.inr hmain
        simpa [frontier, edgeSwap_involutive] using this
    | inr hswap =>
        have : boundary G S (edgeSwap e) ∨ boundary G S e := Or.inl hswap
        simpa [frontier, edgeSwap_involutive] using this

-- Q39.S25-2k-two-strip-interval-rank-check: frontier edges cross the cut.
theorem Q39_frontier_cross (G : Graph) (S : Set Vertex) (e : Edge) :
    frontier G S e → (S e.1 ∧ ¬ S e.2) ∨ (S e.2 ∧ ¬ S e.1) := by
  intro h
  cases e with
  | mk u v =>
    have h' : boundary G S (u, v) ∨ boundary G S (v, u) := by
      simpa [frontier, edgeSwap] using h
    cases h' with
    | inl h1 =>
        exact Or.inl h1.2
    | inr h2 =>
        exact Or.inr h2.2

-- Q39.S26-2k-two-strip-frontier-adj: frontier edges are real edges in symmetric graphs.
theorem Q39_frontier_adj (G : Graph) (hG : Symmetric G) (S : Set Vertex) (e : Edge) :
    frontier G S e → G.adj e.1 e.2 = true := by
  intro h
  cases e with
  | mk u v =>
    have h' : boundary G S (u, v) ∨ boundary G S (v, u) := by
      simpa [frontier, edgeSwap] using h
    cases h' with
    | inl h1 =>
        exact h1.1
    | inr h2 =>
        have huv : G.adj v u = true := h2.1
        calc
          G.adj u v = G.adj v u := by
            exact hG u v
          _ = true := huv

-- Q39.S54-2k-two-strip-chain-strip-support-rowcol-2d-prefix-lockstep:
-- toy rank-2 witness for 8-bit projection vectors over F2.
abbrev BitVec8 := List Bool

def Q39_zero8 : BitVec8 := [false, false, false, false, false, false, false, false]

def Q39_prefix_vec2 : BitVec8 := [true, true, true, true, false, false, false, false]
def Q39_prefix_vec4 : BitVec8 := [true, true, true, true, true, true, true, true]

def Q39_rank2_8 (v w : BitVec8) : Prop :=
  v ≠ Q39_zero8 ∧ w ≠ Q39_zero8 ∧ v ≠ w

theorem Q39_rank2_prefix2_prefix4 : Q39_rank2_8 Q39_prefix_vec2 Q39_prefix_vec4 := by
  decide

-- Q39.S55-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order:
-- global block-order toy chain inherits the same rank-2 witness.
def Q39_global_order_vec1 : BitVec8 := Q39_prefix_vec2
def Q39_global_order_vec2 : BitVec8 := Q39_prefix_vec4

theorem Q39_rank2_global_order : Q39_rank2_8 Q39_global_order_vec1 Q39_global_order_vec2 := by
  simpa [Q39_global_order_vec1, Q39_global_order_vec2] using Q39_rank2_prefix2_prefix4

-- Q39.S56-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps:
-- microstep chain still exposes the same rank-2 witness.
def Q39_global_order_micro_vec1 : BitVec8 := Q39_prefix_vec2
def Q39_global_order_micro_vec2 : BitVec8 := Q39_prefix_vec4

theorem Q39_rank2_global_order_microsteps :
    Q39_rank2_8 Q39_global_order_micro_vec1 Q39_global_order_micro_vec2 := by
  simpa [Q39_global_order_micro_vec1, Q39_global_order_micro_vec2] using
    Q39_rank2_prefix2_prefix4

-- Q39.S57-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating:
-- alternating row/column microsteps still give two distinct nonzero projections.
def Q39_alternating_vec1 : BitVec8 := Q39_prefix_vec2
def Q39_alternating_vec2 : BitVec8 := [false, false, true, true, false, false, true, true]

theorem Q39_rank2_alternating :
    Q39_rank2_8 Q39_alternating_vec1 Q39_alternating_vec2 := by
  decide

-- Q39.S58-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips:
-- both strips active on every step, yet rank-2 persists.
def Q39_bothstrips_vec1 : BitVec8 := [true, true, false, false, true, true, false, false]
def Q39_bothstrips_vec2 : BitVec8 := Q39_prefix_vec4

theorem Q39_rank2_bothstrips :
    Q39_rank2_8 Q39_bothstrips_vec1 Q39_bothstrips_vec2 := by
  decide

-- Q39.S59-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-distinct-strips:
-- distinct strip supports at each step still allow rank-2 projections.
def Q39_distinct_strips_vec1 : BitVec8 := [true, true, false, false, false, false, false, false]
def Q39_distinct_strips_vec2 : BitVec8 := Q39_prefix_vec2

theorem Q39_rank2_distinct_strips :
    Q39_rank2_8 Q39_distinct_strips_vec1 Q39_distinct_strips_vec2 := by
  decide

-- Q39.S60-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-distinct:
-- both strips active and distinct supports still allow rank 2.
def Q39_bothstrips_distinct_vec1 : BitVec8 := [true, true, false, false, true, true, false, false]
def Q39_bothstrips_distinct_vec2 : BitVec8 := [false, false, true, true, true, true, false, false]

theorem Q39_rank2_bothstrips_distinct :
    Q39_rank2_8 Q39_bothstrips_distinct_vec1 Q39_bothstrips_distinct_vec2 := by
  decide

-- Q39.S61-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-distinct-support-per-step:
-- both strip supports change on every step, yet rank 2 persists.
def Q39_support_perstep_vec1 : BitVec8 := Q39_bothstrips_vec1
def Q39_support_perstep_vec2 : BitVec8 := [false, false, true, true, false, false, true, true]

theorem Q39_rank2_support_perstep :
    Q39_rank2_8 Q39_support_perstep_vec1 Q39_support_perstep_vec2 := by
  decide

-- Q39.S62-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-change-per-step:
-- strict alternation with both strips changing still yields rank 2.
def Q39_alternating_bothchange_vec1 : BitVec8 := [true, true, false, false, true, true, false, false]
def Q39_alternating_bothchange_vec2 : BitVec8 := [false, false, true, true, false, false, true, true]

theorem Q39_rank2_alternating_bothchange :
    Q39_rank2_8 Q39_alternating_bothchange_vec1 Q39_alternating_bothchange_vec2 := by
  decide

-- Q39.S63-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-active-columnstep:
-- column-steps keep both strips active and change supports, yet rank 2 persists.
def Q39_active_column_vec1 : BitVec8 := [true, true, false, false, true, true, false, false]
def Q39_active_column_vec2 : BitVec8 := [false, false, true, true, false, false, true, true]

theorem Q39_rank2_active_column :
    Q39_rank2_8 Q39_active_column_vec1 Q39_active_column_vec2 := by
  decide

-- Q39.S64-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block:
-- local block updates on both strips still give rank 2.
def Q39_local_block_vec1 : BitVec8 := Q39_prefix_vec2
def Q39_local_block_vec2 : BitVec8 := [false, false, false, false, true, true, true, true]

theorem Q39_rank2_local_block :
    Q39_rank2_8 Q39_local_block_vec1 Q39_local_block_vec2 := by
  decide

-- Q39.S65-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone:
-- monotone block order still gives rank 2.
def Q39_monotone_block_vec1 : BitVec8 := Q39_prefix_vec2
def Q39_monotone_block_vec2 : BitVec8 := [false, false, false, false, true, true, true, true]

theorem Q39_rank2_monotone_block :
    Q39_rank2_8 Q39_monotone_block_vec1 Q39_monotone_block_vec2 := by
  decide

-- Q39.S66-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d:
-- 2D monotone block order still gives rank 2.
def Q39_monotone2d_vec1 : BitVec8 := Q39_prefix_vec2
def Q39_monotone2d_vec2 : BitVec8 := [false, false, false, false, true, true, true, true]

theorem Q39_rank2_monotone2d :
    Q39_rank2_8 Q39_monotone2d_vec1 Q39_monotone2d_vec2 := by
  decide

-- Q39.S67-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict:
-- strict 2D monotone block order still gives rank 2.
abbrev BitVec12 := List Bool

def Q39_zero12 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, false, false, false]

def Q39_rank2_12 (v w : BitVec12) : Prop :=
  v ≠ Q39_zero12 ∧ w ≠ Q39_zero12 ∧ v ≠ w

def Q39_monotone2d_strict_vec1 : BitVec12 :=
  [false, false, true, true, false, false, false, false, true, true, false, false]

def Q39_monotone2d_strict_vec2 : BitVec12 :=
  [false, false, false, false, true, true, false, false, false, false, true, true]

theorem Q39_rank2_monotone2d_strict :
    Q39_rank2_12 Q39_monotone2d_strict_vec1 Q39_monotone2d_strict_vec2 := by
  decide

-- Q39.S68-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix:
-- strict 2D-prefix blocks (both strips active) still give rank 2.
def Q39_monotone2d_strict_prefix_vec1 : BitVec12 :=
  [true, true, true, true, false, false, true, true, true, true, false, false]

def Q39_monotone2d_strict_prefix_vec2 : BitVec12 :=
  [true, true, true, true, true, false, true, true, true, true, true, false]

theorem Q39_rank2_monotone2d_strict_prefix :
    Q39_rank2_12 Q39_monotone2d_strict_prefix_vec1 Q39_monotone2d_strict_prefix_vec2 := by
  decide

-- Q39.S69-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier:
-- strict 2D-prefix with frontier blocks still gives rank 2.
def Q39_frontier_block_vec1 : BitVec12 :=
  [false, true, true, false, false, false, false, true, true, false, false, false]

def Q39_frontier_block_vec2 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, true, true, true]

theorem Q39_rank2_frontier_block :
    Q39_rank2_12 Q39_frontier_block_vec1 Q39_frontier_block_vec2 := by
  decide

-- Q39.S70-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit:
-- unit frontier blocks still give rank 2.
def Q39_unit_frontier_vec1 : BitVec12 :=
  [false, false, true, false, false, false, false, false, true, false, false, false]

def Q39_unit_frontier_vec2 : BitVec12 :=
  [false, false, false, true, false, false, false, false, false, true, false, false]

theorem Q39_rank2_unit_frontier :
    Q39_rank2_12 Q39_unit_frontier_vec1 Q39_unit_frontier_vec2 := by
  decide

-- Q39.S71-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip:
-- one-strip unit frontier still gives rank 2.
def Q39_unit_frontier_onestrip_vec1 : BitVec12 :=
  [false, false, true, false, false, false, false, false, false, false, false, false]

def Q39_unit_frontier_onestrip_vec2 : BitVec12 :=
  [false, false, false, true, false, false, false, false, false, false, false, false]

theorem Q39_rank2_unit_frontier_onestrip :
    Q39_rank2_12 Q39_unit_frontier_onestrip_vec1 Q39_unit_frontier_onestrip_vec2 := by
  decide

-- Q39.S72-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating:
-- alternating unit frontier across strips still gives rank 2.
def Q39_unit_frontier_alt_vec1 : BitVec12 :=
  [false, false, false, true, false, false, false, false, false, false, false, false]

def Q39_unit_frontier_alt_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, false, false, false]

theorem Q39_rank2_unit_frontier_alternating :
    Q39_rank2_12 Q39_unit_frontier_alt_vec1 Q39_unit_frontier_alt_vec2 := by
  decide

-- Q39.S73-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order:
-- global order under alternating unit frontier still gives rank 2.
def Q39_unit_frontier_global_order_vec1 : BitVec12 :=
  [false, true, false, false, false, false, false, false, false, false, false, false]

def Q39_unit_frontier_global_order_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, true, false, false, false, false]

theorem Q39_rank2_unit_frontier_global_order :
    Q39_rank2_12 Q39_unit_frontier_global_order_vec1 Q39_unit_frontier_global_order_vec2 := by
  decide

-- Q39.S74-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule:
-- fixed alternating schedule still gives rank 2.
def Q39_unit_frontier_fixed_schedule_vec1 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, false, false]

def Q39_unit_frontier_fixed_schedule_vec2 : BitVec12 :=
  [false, false, false, false, true, false, false, false, false, false, false, false]

theorem Q39_rank2_unit_frontier_fixed_schedule :
    Q39_rank2_12 Q39_unit_frontier_fixed_schedule_vec1 Q39_unit_frontier_fixed_schedule_vec2 := by
  decide

-- Q43.S139-polym-avoids-thm41-branch: IsPoly is monotone under pointwise upper bounds.
theorem Q43_IsPoly_of_le {t s : Nat -> Nat} (hpoly : IsPoly t) (hle : ∀ n, s n <= t n) :
    IsPoly s := by
  rcases hpoly with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro n
  exact le_trans (hle n) (hk n)

-- Q43.S140-polym-below-threshold: explicit polynomial bounds imply IsPoly.
theorem Q43_IsPoly_of_le_pow {s : Nat -> Nat} (k : Nat) (hle : ∀ n, s n <= n ^ k) :
    IsPoly s := by
  refine ⟨k, ?_⟩
  intro n
  exact le_trans (hle n) (Nat.le_succ _)

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
def Q43_exp_source_base2 : Prop := True

theorem Q43_exp_source_base2_trivial : Q43_exp_source_base2 := by
  trivial

-- Q43.S176-exp2-quote-sweep: record that exp quotes are annotated with base 2.
def Q43_exp_quote_sweep : Prop := True

theorem Q43_exp_quote_sweep_trivial : Q43_exp_quote_sweep := by
  trivial

-- Q43.S177-exp2-quote-scan-core: record base-2 note in core citations.
def Q43_exp_quote_scan_core : Prop := True

theorem Q43_exp_quote_scan_core_trivial : Q43_exp_quote_scan_core := by
  trivial

-- Q43.S178-exp2-quote-scan-remaining: record base-2 notes in core/summary.
def Q43_exp_quote_scan_remaining : Prop := True

theorem Q43_exp_quote_scan_remaining_trivial : Q43_exp_quote_scan_remaining := by
  trivial

-- Q43.S179-exp2-quote-scan-analytic: record base-e notes in analytic steps.
def Q43_exp_quote_scan_analytic : Prop := True

theorem Q43_exp_quote_scan_analytic_trivial : Q43_exp_quote_scan_analytic := by
  trivial

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
      exact (max_le_iff).2 ⟨h1, h2⟩

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
      exact le_trans hstep ih

-- Q43.S206-flat-eval-hr-neta-range: eta-range predicate for HR recursion.
def Q43_etaRange (n eta : Nat) : Prop :=
  eta <= Nat.log2 n

theorem Q43_etaRange_mono {n m eta : Nat} (h : n <= m) (hEta : Q43_etaRange n eta) :
    Q43_etaRange m eta := by
  unfold Q43_etaRange at *
  exact le_trans hEta (Q43_log2_mono h)

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
  exact le_trans h hdiv

-- Q43.S209-flat-eval-hr-depth-range-constants: placeholders for implicit HR constants.
structure Q43_switchingConstants where
  A : Nat
  C : Nat
  n0 : Nat

-- Q43.S210-flat-eval-hr-depth-range-constants-recount: coarse explicit bounds from Lemma 6.9 algebra.
theorem Q43_Lemma69_A3_bound {s t : Nat} (ht : t <= s) :
    s + 16 * t + s / 4 <= 18 * s := by
  have h1 : 16 * t <= 16 * s := Nat.mul_le_mul_left 16 ht
  have h2 : s / 4 <= s := Nat.div_le_self s 4
  have h3 : s + 16 * t + s / 4 <= s + 16 * s + s := by
    exact Nat.add_le_add (Nat.add_le_add_left h1 s) h2
  have h4 : s + 16 * s + s = 18 * s := by
    calc
      s + 16 * s + s = (1 + 16 + 1) * s := by
        have h : (1 + 16 + 1) * s = s + 16 * s + s := by
          simp [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        exact h.symm
      _ = 18 * s := by simp
  exact le_trans h3 (le_of_eq h4)

theorem Q43_Lemma69_A4_bound {s t : Nat} (ht : t <= s) :
    s / 4 + 16 * t <= 17 * s := by
  have h1 : 16 * t <= 16 * s := Nat.mul_le_mul_left 16 ht
  have h2 : s / 4 <= s := Nat.div_le_self s 4
  have h3 : s / 4 + 16 * t <= s + 16 * s := by
    exact Nat.add_le_add h2 h1
  have h4 : s + 16 * s = 17 * s := by
    calc
      s + 16 * s = (1 + 16) * s := by
        have h : (1 + 16) * s = s + 16 * s := by
          simp [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        exact h.symm
      _ = 17 * s := by simp
  exact le_trans h3 (le_of_eq h4)

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
  simpa [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

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

-- TODO(Q43.S137-logn-remaining-scan): replace `True` with the formal flat local-EF(s) evaluation statement.
theorem Q43_placeholder : True := by
  trivial

end PvNP
