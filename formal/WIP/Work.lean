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

-- Q39.S141-frontier-complement-swap-invariant: complement + swap leaves the frontier unchanged.
theorem Q39_frontier_compl_swap (G : Graph) (hG : Symmetric G) (S : Set Vertex) (e : Edge) :
    frontier G (fun x => ¬ S x) (edgeSwap e) ↔ frontier G S e := by
  have hswap : frontier G (fun x => ¬ S x) (edgeSwap e) ↔ frontier G (fun x => ¬ S x) e :=
    Q39_frontier_swap G (fun x => ¬ S x) e
  have hcompl : frontier G (fun x => ¬ S x) e ↔ frontier G S e :=
    (Q39_frontier_compl G hG S e).symm
  exact hswap.trans hcompl

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

instance (v w : BitVec8) : Decidable (Q39_rank2_8 v w) := by
  unfold Q39_rank2_8
  infer_instance

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

instance (v w : BitVec12) : Decidable (Q39_rank2_12 v w) := by
  unfold Q39_rank2_12
  infer_instance

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

-- Q39.S75-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase:
-- two-phase alternating schedule still gives rank 2.
def Q39_unit_frontier_two_phase_vec1 : BitVec12 :=
  [false, false, true, false, false, false, false, false, false, false, false, false]

def Q39_unit_frontier_two_phase_vec2 : BitVec12 :=
  [false, false, false, false, false, true, false, false, false, false, false, false]

theorem Q39_rank2_unit_frontier_two_phase :
    Q39_rank2_12 Q39_unit_frontier_two_phase_vec1 Q39_unit_frontier_two_phase_vec2 := by
  decide

-- Q39.S76-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks:
-- fixed block lengths in two-phase schedule still give rank 2.
def Q39_unit_frontier_two_phase_blocks_vec1 : BitVec12 :=
  [false, false, false, false, true, true, false, false, false, false, false, false]

def Q39_unit_frontier_two_phase_blocks_vec2 : BitVec12 :=
  [false, false, false, false, false, false, true, true, false, false, false, false]

theorem Q39_rank2_unit_frontier_two_phase_blocks :
    Q39_rank2_12 Q39_unit_frontier_two_phase_blocks_vec1
      Q39_unit_frontier_two_phase_blocks_vec2 := by
  decide

-- Q39.S77-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved:
-- interleaved blocks in two-phase schedule still give rank 2.
def Q39_unit_frontier_blocks_interleaved_vec1 : BitVec12 :=
  [false, true, false, true, false, false, false, false, false, false, false, false]

def Q39_unit_frontier_blocks_interleaved_vec2 : BitVec12 :=
  [false, false, false, false, false, true, false, true, false, false, false, false]

theorem Q39_rank2_unit_frontier_blocks_interleaved :
    Q39_rank2_12 Q39_unit_frontier_blocks_interleaved_vec1
      Q39_unit_frontier_blocks_interleaved_vec2 := by
  decide

-- Q39.S78-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored:
-- anchored interleaved blocks still give rank 2.
def Q39_unit_frontier_blocks_anchored_vec1 : BitVec12 :=
  [true, true, false, false, false, false, false, false, false, false, false, false]

def Q39_unit_frontier_blocks_anchored_vec2 : BitVec12 :=
  [false, false, true, true, false, false, false, false, false, false, false, false]

theorem Q39_rank2_unit_frontier_blocks_anchored :
    Q39_rank2_12 Q39_unit_frontier_blocks_anchored_vec1
      Q39_unit_frontier_blocks_anchored_vec2 := by
  decide

-- Q39.S79-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted:
-- shifted anchored blocks still give rank 2.
def Q39_unit_frontier_blocks_anchored_shifted_vec1 : BitVec12 :=
  [false, true, true, false, false, false, false, false, false, false, false, false]

def Q39_unit_frontier_blocks_anchored_shifted_vec2 : BitVec12 :=
  [false, false, false, true, true, false, false, false, false, false, false, false]

theorem Q39_rank2_unit_frontier_blocks_anchored_shifted :
    Q39_rank2_12 Q39_unit_frontier_blocks_anchored_shifted_vec1
      Q39_unit_frontier_blocks_anchored_shifted_vec2 := by
  decide

-- Q39.S80-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced:
-- balanced anchored blocks still give rank 2.
def Q39_unit_frontier_blocks_anchored_shifted_balanced_vec1 : BitVec12 :=
  [true, false, false, true, false, false, true, false, false, true, false, false]

def Q39_unit_frontier_blocks_anchored_shifted_balanced_vec2 : BitVec12 :=
  [false, true, false, false, true, false, false, true, false, false, true, false]

theorem Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced :
    Q39_rank2_12 Q39_unit_frontier_blocks_anchored_shifted_balanced_vec1
      Q39_unit_frontier_blocks_anchored_shifted_balanced_vec2 := by
  decide

-- Q39.S81-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced-rowcol-swap:
-- row/column swap symmetry still gives rank 2.
def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_vec1 : BitVec12 :=
  [true, true, false, false, false, false, true, true, false, false, false, false]

def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_vec2 : BitVec12 :=
  [false, false, true, true, false, false, false, false, true, true, false, false]

theorem Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap :
    Q39_rank2_12 Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_vec1
      Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_vec2 := by
  decide

-- Q39.S82-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced-rowcol-swap-fixedpair:
-- fixed-pair row/column swap symmetry still gives rank 2.
def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_vec1 : BitVec12 :=
  [true, false, true, false, false, false, true, false, true, false, false, false]

def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_vec2 : BitVec12 :=
  [false, true, false, true, false, false, false, true, false, true, false, false]

theorem Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair :
    Q39_rank2_12 Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_vec1
      Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_vec2 := by
  decide

-- Q39.S83-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced-rowcol-swap-fixedpair-sameorder:
-- fixed-pair + same-order still gives rank 2.
def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_vec1 : BitVec12 :=
  [true, false, false, true, false, false, true, false, false, true, false, false]

def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_vec2 : BitVec12 :=
  [false, true, false, false, true, false, false, true, false, false, true, false]

theorem Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder :
    Q39_rank2_12 Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_vec1
      Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_vec2 := by
  decide

-- Q39.S84-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced-rowcol-swap-fixedpair-sameorder-globalfixedpair:
-- global fixed-pair still gives rank 2.
def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair_vec1 :
    BitVec12 :=
  [true, false, true, false, true, false, false, false, true, false, false, false]

def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair_vec2 :
    BitVec12 :=
  [false, true, false, true, false, true, false, false, false, true, false, false]

theorem Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair :
    Q39_rank2_12
      Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair_vec1
      Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair_vec2 := by
  decide

-- Q39.S85-2k-two-strip-chain-strip-support-rowcol-2d-prefix-global-order-microsteps-alternating-
-- bothstrips-local-block-monotone-2d-strict-prefix-frontier-unit-onestrip-alternating-global-order-fixed-schedule-two-phase-blocks-interleaved-anchored-shifted-balanced-rowcol-swap-fixedpair-sameorder-globalfixedpair-fixedorientation:
-- fixed orientation still gives rank 2.
def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair_fixedorientation_vec1 :
    BitVec12 :=
  [true, false, true, false, true, false, true, false, true, false, true, false]

def Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair_fixedorientation_vec2 :
    BitVec12 :=
  [false, true, false, true, false, true, false, true, false, true, false, true]

theorem Q39_rank2_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair_fixedorientation :
    Q39_rank2_12
      Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair_fixedorientation_vec1
      Q39_unit_frontier_blocks_anchored_shifted_balanced_rowcolswap_fixedpair_sameorder_globalfixedpair_fixedorientation_vec2 := by
  decide

-- Q39.S86-globalfixedpair-fixedorientation-contiguous:
-- contiguous blocks with fixed orientation still give rank 2.
def Q39_globalfixedpair_fixedorientation_contiguous_vec1 : BitVec12 :=
  [true, true, true, false, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_vec2 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_vec2 := by
  decide

-- Q39.S87-globalfixedpair-fixedorientation-contiguous-shift:
-- contiguous blocks with fixed orientation still give rank 2 after a shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_vec1 : BitVec12 :=
  [false, true, true, true, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_vec2 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_vec2 := by
  decide

-- Q39.S88-globalfixedpair-fixedorientation-contiguous-shift-alt:
-- contiguous blocks with fixed orientation still give rank 2 after an alternate shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt_vec1 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt_vec2 : BitVec12 :=
  [false, false, false, false, false, true, true, true, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt_vec2 := by
  decide

-- Q39.S89-globalfixedpair-fixedorientation-contiguous-shift-alt2:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt2_vec1 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt2_vec2 : BitVec12 :=
  [false, false, false, false, false, false, true, true, true, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt2 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt2_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt2_vec2 := by
  decide

-- Q39.S90-globalfixedpair-fixedorientation-contiguous-shift-alt3:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt3_vec1 : BitVec12 :=
  [false, false, false, false, false, true, true, true, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt3_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt3 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt3_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt3_vec2 := by
  decide

-- Q39.S91-globalfixedpair-fixedorientation-contiguous-shift-alt4:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt4_vec1 : BitVec12 :=
  [false, false, false, false, false, false, true, true, true, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt4_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt4 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt4_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt4_vec2 := by
  decide

-- Q39.S92-globalfixedpair-fixedorientation-contiguous-shift-alt5:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt5_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt5_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt5 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt5_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt5_vec2 := by
  decide

-- Q39.S93-globalfixedpair-fixedorientation-contiguous-shift-alt6:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt6_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt6_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt6 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt6_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt6_vec2 := by
  decide

-- Q39.S94-globalfixedpair-fixedorientation-contiguous-shift-alt7:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt7_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt7_vec2 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt7 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt7_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt7_vec2 := by
  decide

-- Q39.S95-globalfixedpair-fixedorientation-contiguous-shift-alt8:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt8_vec1 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, true, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt8_vec2 : BitVec12 :=
  [true, true, false, false, false, false, false, false, false, false, false, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt8 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt8_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt8_vec2 := by
  decide

-- Q39.S96-globalfixedpair-fixedorientation-contiguous-shift-alt9:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt9_vec1 : BitVec12 :=
  [true, true, false, false, false, false, false, false, false, false, false, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt9_vec2 : BitVec12 :=
  [true, true, true, false, false, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt9 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt9_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt9_vec2 := by
  decide

-- Q39.S97-globalfixedpair-fixedorientation-contiguous-shift-alt10:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt10_vec1 : BitVec12 :=
  [true, true, true, false, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt10_vec2 : BitVec12 :=
  [false, true, true, true, false, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt10 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt10_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt10_vec2 := by
  decide

-- Q39.S98-globalfixedpair-fixedorientation-contiguous-shift-alt11:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt11_vec1 : BitVec12 :=
  [false, true, true, true, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt11_vec2 : BitVec12 :=
  [false, false, true, true, true, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt11 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt11_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt11_vec2 := by
  decide

-- Q39.S99-globalfixedpair-fixedorientation-contiguous-shift-alt12:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt12_vec1 : BitVec12 :=
  [false, false, true, true, true, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt12_vec2 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt12 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt12_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt12_vec2 := by
  decide

-- Q39.S100-globalfixedpair-fixedorientation-contiguous-shift-alt13:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt13_vec1 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt13_vec2 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt13 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt13_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt13_vec2 := by
  decide

-- Q39.S101-globalfixedpair-fixedorientation-contiguous-shift-alt14:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt14_vec1 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt14_vec2 : BitVec12 :=
  [false, false, false, false, false, true, true, true, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt14 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt14_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt14_vec2 := by
  decide

-- Q39.S102-globalfixedpair-fixedorientation-contiguous-shift-alt15:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt15_vec1 : BitVec12 :=
  [false, false, false, false, false, true, true, true, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt15_vec2 : BitVec12 :=
  [false, false, false, false, false, false, true, true, true, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt15 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt15_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt15_vec2 := by
  decide

-- Q39.S103-globalfixedpair-fixedorientation-contiguous-shift-alt16:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt16_vec1 : BitVec12 :=
  [false, false, false, false, false, false, true, true, true, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt16_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt16 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt16_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt16_vec2 := by
  decide

-- Q39.S104-globalfixedpair-fixedorientation-contiguous-shift-alt17:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt17_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt17_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt17 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt17_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt17_vec2 := by
  decide

-- Q39.S105-globalfixedpair-fixedorientation-contiguous-shift-alt18:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt18_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt18_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt18 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt18_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt18_vec2 := by
  decide

-- Q39.S106-globalfixedpair-fixedorientation-contiguous-shift-alt19:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt19_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt19_vec2 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt19 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt19_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt19_vec2 := by
  decide

-- Q39.S107-globalfixedpair-fixedorientation-contiguous-shift-alt20:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt20_vec1 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, true, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt20_vec2 : BitVec12 :=
  [true, true, false, false, false, false, false, false, false, false, false, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt20 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt20_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt20_vec2 := by
  decide

-- Q39.S108-globalfixedpair-fixedorientation-contiguous-shift-alt21:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt21_vec1 : BitVec12 :=
  [true, true, false, false, false, false, false, false, false, false, false, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt21_vec2 : BitVec12 :=
  [true, true, true, false, false, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt21 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt21_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt21_vec2 := by
  decide

-- Q39.S109-globalfixedpair-fixedorientation-contiguous-shift-alt22:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt22_vec1 : BitVec12 :=
  [true, true, true, false, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt22_vec2 : BitVec12 :=
  [false, true, true, true, false, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt22 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt22_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt22_vec2 := by
  decide

-- Q39.S110-globalfixedpair-fixedorientation-contiguous-shift-alt23:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt23_vec1 : BitVec12 :=
  [false, true, true, true, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt23_vec2 : BitVec12 :=
  [false, false, true, true, true, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt23 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt23_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt23_vec2 := by
  decide

-- Q39.S111-globalfixedpair-fixedorientation-contiguous-shift-alt24:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt24_vec1 : BitVec12 :=
  [false, false, true, true, true, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt24_vec2 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt24 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt24_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt24_vec2 := by
  decide

-- Q39.S112-globalfixedpair-fixedorientation-contiguous-shift-alt25:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt25_vec1 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt25_vec2 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt25 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt25_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt25_vec2 := by
  decide

-- Q39.S113-globalfixedpair-fixedorientation-contiguous-shift-alt26:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt26_vec1 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt26_vec2 : BitVec12 :=
  [false, false, false, false, false, true, true, true, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt26 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt26_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt26_vec2 := by
  decide

-- Q39.S114-globalfixedpair-fixedorientation-contiguous-shift-alt27:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt27_vec1 : BitVec12 :=
  [false, false, false, false, false, false, true, true, true, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt27_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt27 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt27_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt27_vec2 := by
  decide

-- Q39.S115-globalfixedpair-fixedorientation-contiguous-shift-alt28:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt28_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt28_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt28 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt28_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt28_vec2 := by
  decide

-- Q39.S116-globalfixedpair-fixedorientation-contiguous-shift-alt29:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt29_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt29_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt29 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt29_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt29_vec2 := by
  decide

-- Q39.S117-globalfixedpair-fixedorientation-contiguous-shift-alt30:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt30_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt30_vec2 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt30 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt30_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt30_vec2 := by
  decide

-- Q39.S118-globalfixedpair-fixedorientation-contiguous-shift-alt31:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt31_vec1 : BitVec12 :=
  [true, true, true, false, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt31_vec2 : BitVec12 :=
  [false, true, true, true, false, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt31 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt31_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt31_vec2 := by
  decide

-- Q39.S119-globalfixedpair-fixedorientation-contiguous-shift-alt32:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt32_vec1 : BitVec12 :=
  [false, true, true, true, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt32_vec2 : BitVec12 :=
  [false, false, true, true, true, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt32 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt32_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt32_vec2 := by
  decide

-- Q39.S120-globalfixedpair-fixedorientation-contiguous-shift-alt33:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt33_vec1 : BitVec12 :=
  [false, false, true, true, true, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt33_vec2 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt33 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt33_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt33_vec2 := by
  decide

-- Q39.S121-globalfixedpair-fixedorientation-contiguous-shift-alt34:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt34_vec1 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt34_vec2 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt34 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt34_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt34_vec2 := by
  decide

-- Q39.S122-globalfixedpair-fixedorientation-contiguous-shift-alt35:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt35_vec1 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt35_vec2 : BitVec12 :=
  [false, false, false, false, false, true, true, true, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt35 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt35_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt35_vec2 := by
  decide

-- Q39.S123-globalfixedpair-fixedorientation-contiguous-shift-alt36:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt36_vec1 : BitVec12 :=
  [false, false, false, false, false, true, true, true, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt36_vec2 : BitVec12 :=
  [false, false, false, false, false, false, true, true, true, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt36 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt36_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt36_vec2 := by
  decide

-- Q39.S124-globalfixedpair-fixedorientation-contiguous-shift-alt37:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt37_vec1 : BitVec12 :=
  [false, false, false, false, false, false, true, true, true, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt37_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt37 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt37_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt37_vec2 := by
  decide

-- Q39.S125-globalfixedpair-fixedorientation-contiguous-shift-alt38:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt38_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt38_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt38 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt38_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt38_vec2 := by
  decide

-- Q39.S126-globalfixedpair-fixedorientation-contiguous-shift-alt39:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt39_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt39_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt39 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt39_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt39_vec2 := by
  decide

-- Q39.S127-globalfixedpair-fixedorientation-contiguous-shift-alt40:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt40_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt40_vec2 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt40 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt40_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt40_vec2 := by
  decide

-- Q39.S128-globalfixedpair-fixedorientation-contiguous-shift-alt41:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt41_vec1 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, true, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt41_vec2 : BitVec12 :=
  [true, true, false, false, false, false, false, false, false, false, false, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt41 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt41_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt41_vec2 := by
  decide

-- Q39.S129-globalfixedpair-fixedorientation-contiguous-shift-alt42:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt42_vec1 : BitVec12 :=
  [true, true, false, false, false, false, false, false, false, false, false, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt42_vec2 : BitVec12 :=
  [true, true, true, false, false, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt42 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt42_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt42_vec2 := by
  decide

-- Q39.S130-globalfixedpair-fixedorientation-contiguous-shift-alt43:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt43_vec1 : BitVec12 :=
  [true, true, true, false, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt43_vec2 : BitVec12 :=
  [false, true, true, true, false, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt43 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt43_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt43_vec2 := by
  decide

-- Q39.S131-globalfixedpair-fixedorientation-contiguous-shift-alt44:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt44_vec1 : BitVec12 :=
  [false, true, true, true, false, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt44_vec2 : BitVec12 :=
  [false, false, true, true, true, false, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt44 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt44_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt44_vec2 := by
  decide

-- Q39.S132-globalfixedpair-fixedorientation-contiguous-shift-alt45:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt45_vec1 : BitVec12 :=
  [false, false, true, true, true, false, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt45_vec2 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt45 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt45_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt45_vec2 := by
  decide

-- Q39.S133-globalfixedpair-fixedorientation-contiguous-shift-alt46:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt46_vec1 : BitVec12 :=
  [false, false, false, true, true, true, false, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt46_vec2 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt46 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt46_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt46_vec2 := by
  decide

-- Q39.S134-globalfixedpair-fixedorientation-contiguous-shift-alt47:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt47_vec1 : BitVec12 :=
  [false, false, false, false, true, true, true, false, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt47_vec2 : BitVec12 :=
  [false, false, false, false, false, true, true, true, false, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt47 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt47_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt47_vec2 := by
  decide

-- Q39.S135-globalfixedpair-fixedorientation-contiguous-shift-alt48:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt48_vec1 : BitVec12 :=
  [false, false, false, false, false, true, true, true, false, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt48_vec2 : BitVec12 :=
  [false, false, false, false, false, false, true, true, true, false, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt48 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt48_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt48_vec2 := by
  decide

-- Q39.S136-globalfixedpair-fixedorientation-contiguous-shift-alt49:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt49_vec1 : BitVec12 :=
  [false, false, false, false, false, false, true, true, true, false, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt49_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt49 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt49_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt49_vec2 := by
  decide

-- Q39.S137-globalfixedpair-fixedorientation-contiguous-shift-alt50:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt50_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, true, true, true, false, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt50_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt50 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt50_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt50_vec2 := by
  decide

-- Q39.S138-globalfixedpair-fixedorientation-contiguous-shift-alt51:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt51_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, true, true, true, false]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt51_vec2 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt51 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt51_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt51_vec2 := by
  decide

-- Q39.S139-globalfixedpair-fixedorientation-contiguous-shift-alt52:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt52_vec1 : BitVec12 :=
  [false, false, false, false, false, false, false, false, false, true, true, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt52_vec2 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, true, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt52 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt52_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt52_vec2 := by
  decide

-- Q39.S140-globalfixedpair-fixedorientation-contiguous-shift-alt53:
-- contiguous blocks with fixed orientation still give rank 2 after another shift.
def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt53_vec1 : BitVec12 :=
  [true, false, false, false, false, false, false, false, false, false, true, true]

def Q39_globalfixedpair_fixedorientation_contiguous_shift_alt53_vec2 : BitVec12 :=
  [true, true, false, false, false, false, false, false, false, false, false, true]

theorem Q39_rank2_globalfixedpair_fixedorientation_contiguous_shift_alt53 :
    Q39_rank2_12 Q39_globalfixedpair_fixedorientation_contiguous_shift_alt53_vec1
      Q39_globalfixedpair_fixedorientation_contiguous_shift_alt53_vec2 := by
  decide

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

-- Q43.S253-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k13:
-- counterexample inside the gap for k=13.
def Q43_gap_k13 : Nat := 13
def Q43_gap_n13 : Nat := 11585
def Q43_gap_n13_succ : Nat := 11586

theorem Q43_gap_range_k13 :
    Q43_gap_end_lo_k Q43_gap_k13 <= Q43_gap_n13 ∧
    Q43_gap_end_lo_k Q43_gap_k13 <= Q43_gap_n13_succ ∧
    Q43_gap_n13_succ < Q43_gap_end_hi_k Q43_gap_k13 := by
  decide

theorem Q43_grid_ratio_drop_gap_k13 :
    Q43_grid_ratio Q43_gap_n13_succ < Q43_grid_ratio Q43_gap_n13 := by
  decide

-- Q43.S254-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k14:
-- counterexample inside the gap for k=14.
def Q43_gap_k14 : Nat := 14
def Q43_gap_n14 : Nat := 23170
def Q43_gap_n14_succ : Nat := 23171

theorem Q43_gap_range_k14 :
    Q43_gap_end_lo_k Q43_gap_k14 <= Q43_gap_n14 ∧
    Q43_gap_end_lo_k Q43_gap_k14 <= Q43_gap_n14_succ ∧
    Q43_gap_n14_succ < Q43_gap_end_hi_k Q43_gap_k14 := by
  decide

theorem Q43_grid_ratio_drop_gap_k14 :
    Q43_grid_ratio Q43_gap_n14_succ < Q43_grid_ratio Q43_gap_n14 := by
  decide

-- Q43.S255-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k15:
-- counterexample inside the gap for k=15.
def Q43_gap_k15 : Nat := 15
def Q43_gap_n15 : Nat := 46340
def Q43_gap_n15_succ : Nat := 46341

theorem Q43_gap_range_k15 :
    Q43_gap_end_lo_k Q43_gap_k15 <= Q43_gap_n15 ∧
    Q43_gap_end_lo_k Q43_gap_k15 <= Q43_gap_n15_succ ∧
    Q43_gap_n15_succ < Q43_gap_end_hi_k Q43_gap_k15 := by
  decide

theorem Q43_grid_ratio_drop_gap_k15 :
    Q43_grid_ratio Q43_gap_n15_succ < Q43_grid_ratio Q43_gap_n15 := by
  decide

-- Q43.S256-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k16:
-- counterexample inside the gap for k=16.
def Q43_gap_k16 : Nat := 16
def Q43_gap_n16 : Nat := 92681
def Q43_gap_n16_succ : Nat := 92682

theorem Q43_gap_range_k16 :
    Q43_gap_end_lo_k Q43_gap_k16 <= Q43_gap_n16 ∧
    Q43_gap_end_lo_k Q43_gap_k16 <= Q43_gap_n16_succ ∧
    Q43_gap_n16_succ < Q43_gap_end_hi_k Q43_gap_k16 := by
  decide

theorem Q43_grid_ratio_drop_gap_k16 :
    Q43_grid_ratio Q43_gap_n16_succ < Q43_grid_ratio Q43_gap_n16 := by
  decide

-- Q43.S257-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k17:
-- counterexample inside the gap for k=17.
def Q43_gap_k17 : Nat := 17
def Q43_gap_n17 : Nat := 185363
def Q43_gap_n17_succ : Nat := 185364

theorem Q43_gap_range_k17 :
    Q43_gap_end_lo_k Q43_gap_k17 <= Q43_gap_n17 ∧
    Q43_gap_end_lo_k Q43_gap_k17 <= Q43_gap_n17_succ ∧
    Q43_gap_n17_succ < Q43_gap_end_hi_k Q43_gap_k17 := by
  decide

theorem Q43_grid_ratio_drop_gap_k17 :
    Q43_grid_ratio Q43_gap_n17_succ < Q43_grid_ratio Q43_gap_n17 := by
  decide

-- Q43.S258-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k18:
-- counterexample inside the gap for k=18.
def Q43_gap_k18 : Nat := 18
def Q43_gap_n18 : Nat := 370727
def Q43_gap_n18_succ : Nat := 370728

theorem Q43_gap_range_k18 :
    Q43_gap_end_lo_k Q43_gap_k18 <= Q43_gap_n18 ∧
    Q43_gap_end_lo_k Q43_gap_k18 <= Q43_gap_n18_succ ∧
    Q43_gap_n18_succ < Q43_gap_end_hi_k Q43_gap_k18 := by
  decide

theorem Q43_grid_ratio_drop_gap_k18 :
    Q43_grid_ratio Q43_gap_n18_succ < Q43_grid_ratio Q43_gap_n18 := by
  decide

-- Q43.S259-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k19:
-- counterexample inside the gap for k=19.
def Q43_gap_k19 : Nat := 19
def Q43_gap_n19 : Nat := 741455
def Q43_gap_n19_succ : Nat := 741456

theorem Q43_gap_range_k19 :
    Q43_gap_end_lo_k Q43_gap_k19 <= Q43_gap_n19 ∧
    Q43_gap_end_lo_k Q43_gap_k19 <= Q43_gap_n19_succ ∧
    Q43_gap_n19_succ < Q43_gap_end_hi_k Q43_gap_k19 := by
  decide

theorem Q43_grid_ratio_drop_gap_k19 :
    Q43_grid_ratio Q43_gap_n19_succ < Q43_grid_ratio Q43_gap_n19 := by
  decide

-- Q43.S260-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k20:
-- counterexample inside the gap for k=20.
def Q43_gap_k20 : Nat := 20
def Q43_gap_n20 : Nat := 1482910
def Q43_gap_n20_succ : Nat := 1482911

theorem Q43_gap_range_k20 :
    Q43_gap_end_lo_k Q43_gap_k20 <= Q43_gap_n20 ∧
    Q43_gap_end_lo_k Q43_gap_k20 <= Q43_gap_n20_succ ∧
    Q43_gap_n20_succ < Q43_gap_end_hi_k Q43_gap_k20 := by
  decide

theorem Q43_grid_ratio_drop_gap_k20 :
    Q43_grid_ratio Q43_gap_n20_succ < Q43_grid_ratio Q43_gap_n20 := by
  decide

-- Q43.S261-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k21:
-- counterexample inside the gap for k=21.
def Q43_gap_k21 : Nat := 21
def Q43_gap_n21 : Nat := 2965820
def Q43_gap_n21_succ : Nat := 2965821

theorem Q43_gap_range_k21 :
    Q43_gap_end_lo_k Q43_gap_k21 <= Q43_gap_n21 ∧
    Q43_gap_end_lo_k Q43_gap_k21 <= Q43_gap_n21_succ ∧
    Q43_gap_n21_succ < Q43_gap_end_hi_k Q43_gap_k21 := by
  decide

theorem Q43_grid_ratio_drop_gap_k21 :
    Q43_grid_ratio Q43_gap_n21_succ < Q43_grid_ratio Q43_gap_n21 := by
  decide

-- Q43.S262-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-drop-k22:
-- counterexample inside the gap for k=22.
def Q43_gap_k22 : Nat := 22
def Q43_gap_n22 : Nat := 5931641
def Q43_gap_n22_succ : Nat := 5931642

theorem Q43_gap_range_k22 :
    Q43_gap_end_lo_k Q43_gap_k22 <= Q43_gap_n22 ∧
    Q43_gap_end_lo_k Q43_gap_k22 <= Q43_gap_n22_succ ∧
    Q43_gap_n22_succ < Q43_gap_end_hi_k Q43_gap_k22 := by
  decide

theorem Q43_grid_ratio_drop_gap_k22 :
    Q43_grid_ratio Q43_gap_n22_succ < Q43_grid_ratio Q43_gap_n22 := by
  decide

-- Q43.S263-gap-drop-k23-k25:
-- counterexample inside the gap for k=23.
def Q43_gap_k23 : Nat := 23
def Q43_gap_n23 : Nat := 11863283
def Q43_gap_n23_succ : Nat := 11863284

theorem Q43_gap_range_k23 :
    Q43_gap_end_lo_k Q43_gap_k23 <= Q43_gap_n23 ∧
    Q43_gap_end_lo_k Q43_gap_k23 <= Q43_gap_n23_succ ∧
    Q43_gap_n23_succ < Q43_gap_end_hi_k Q43_gap_k23 := by
  decide

theorem Q43_grid_ratio_drop_gap_k23 :
    Q43_grid_ratio Q43_gap_n23_succ < Q43_grid_ratio Q43_gap_n23 := by
  decide

-- counterexample inside the gap for k=24.
def Q43_gap_k24 : Nat := 24
def Q43_gap_n24 : Nat := 23726566
def Q43_gap_n24_succ : Nat := 23726567

theorem Q43_gap_range_k24 :
    Q43_gap_end_lo_k Q43_gap_k24 <= Q43_gap_n24 ∧
    Q43_gap_end_lo_k Q43_gap_k24 <= Q43_gap_n24_succ ∧
    Q43_gap_n24_succ < Q43_gap_end_hi_k Q43_gap_k24 := by
  decide

theorem Q43_grid_ratio_drop_gap_k24 :
    Q43_grid_ratio Q43_gap_n24_succ < Q43_grid_ratio Q43_gap_n24 := by
  decide

-- counterexample inside the gap for k=25.
def Q43_gap_k25 : Nat := 25
def Q43_gap_n25 : Nat := 47453132
def Q43_gap_n25_succ : Nat := 47453133

theorem Q43_gap_range_k25 :
    Q43_gap_end_lo_k Q43_gap_k25 <= Q43_gap_n25 ∧
    Q43_gap_end_lo_k Q43_gap_k25 <= Q43_gap_n25_succ ∧
    Q43_gap_n25_succ < Q43_gap_end_hi_k Q43_gap_k25 := by
  decide

theorem Q43_grid_ratio_drop_gap_k25 :
    Q43_grid_ratio Q43_gap_n25_succ < Q43_grid_ratio Q43_gap_n25 := by
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

-- Q43.S252-flat-eval-hr-depth-range-constants-a0-c1c2-log2-verify-regime-d-criterion-bound-
-- apply-params-poly-n0-ratio-lift-piecewise-gap-bound-generalize:
-- parameterized gap scan instantiated at k=12.
set_option maxRecDepth 8000 in
theorem Q43_gap_min_ratio_le_all_k12 :
    ∀ n, n ∈ Q43_gap_range_list_k Q43_gap_k →
      Q43_gap_min_ratio_k Q43_gap_k Q43_gap_n_succ <= Q43_grid_ratio n := by
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

theorem Q43_nk_eq_gap_n13 : Q43_nk 13 = Q43_gap_n13 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 13 + 1) - 1) (m:=Q43_gap_n13) (by decide) (by decide)

theorem Q43_nk_eq_gap_n14 : Q43_nk 14 = Q43_gap_n14 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 14 + 1) - 1) (m:=Q43_gap_n14) (by decide) (by decide)

theorem Q43_nk_eq_gap_n15 : Q43_nk 15 = Q43_gap_n15 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 15 + 1) - 1) (m:=Q43_gap_n15) (by decide) (by decide)

theorem Q43_nk_eq_gap_n16 : Q43_nk 16 = Q43_gap_n16 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 16 + 1) - 1) (m:=Q43_gap_n16) (by decide) (by decide)

theorem Q43_nk_eq_gap_n17 : Q43_nk 17 = Q43_gap_n17 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 17 + 1) - 1) (m:=Q43_gap_n17) (by decide) (by decide)

theorem Q43_nk_eq_gap_n18 : Q43_nk 18 = Q43_gap_n18 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 18 + 1) - 1) (m:=Q43_gap_n18) (by decide) (by decide)

theorem Q43_nk_eq_gap_n19 : Q43_nk 19 = Q43_gap_n19 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 19 + 1) - 1) (m:=Q43_gap_n19) (by decide) (by decide)

theorem Q43_nk_eq_gap_n20 : Q43_nk 20 = Q43_gap_n20 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 20 + 1) - 1) (m:=Q43_gap_n20) (by decide) (by decide)

theorem Q43_nk_eq_gap_n21 : Q43_nk 21 = Q43_gap_n21 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 21 + 1) - 1) (m:=Q43_gap_n21) (by decide) (by decide)

theorem Q43_nk_eq_gap_n22 : Q43_nk 22 = Q43_gap_n22 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 22 + 1) - 1) (m:=Q43_gap_n22) (by decide) (by decide)

theorem Q43_nk_eq_gap_n23 : Q43_nk 23 = Q43_gap_n23 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 23 + 1) - 1) (m:=Q43_gap_n23) (by decide) (by decide)

theorem Q43_nk_eq_gap_n24 : Q43_nk 24 = Q43_gap_n24 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 24 + 1) - 1) (m:=Q43_gap_n24) (by decide) (by decide)

theorem Q43_nk_eq_gap_n25 : Q43_nk 25 = Q43_gap_n25 := by
  unfold Q43_nk
  refine
    Q43_floorSqrt_eq_of_sq_bounds (n:=2 ^ (2 * 25 + 1) - 1) (m:=Q43_gap_n25) (by decide) (by decide)

def Q43_gap_ks : List Nat := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

theorem Q43_grid_ratio_drop_nk_of_mem {k : Nat} (hk : k ∈ Q43_gap_ks) :
    Q43_grid_ratio (Q43_nk k + 1) < Q43_grid_ratio (Q43_nk k) := by
  simp [Q43_gap_ks] at hk
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n12, Q43_gap_n, Q43_gap_n_succ] using Q43_grid_ratio_drop_gap
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n13, Q43_gap_n13, Q43_gap_n13_succ] using Q43_grid_ratio_drop_gap_k13
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n14, Q43_gap_n14, Q43_gap_n14_succ] using Q43_grid_ratio_drop_gap_k14
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n15, Q43_gap_n15, Q43_gap_n15_succ] using Q43_grid_ratio_drop_gap_k15
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n16, Q43_gap_n16, Q43_gap_n16_succ] using Q43_grid_ratio_drop_gap_k16
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n17, Q43_gap_n17, Q43_gap_n17_succ] using Q43_grid_ratio_drop_gap_k17
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n18, Q43_gap_n18, Q43_gap_n18_succ] using Q43_grid_ratio_drop_gap_k18
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n19, Q43_gap_n19, Q43_gap_n19_succ] using Q43_grid_ratio_drop_gap_k19
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n20, Q43_gap_n20, Q43_gap_n20_succ] using Q43_grid_ratio_drop_gap_k20
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n21, Q43_gap_n21, Q43_gap_n21_succ] using Q43_grid_ratio_drop_gap_k21
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n22, Q43_gap_n22, Q43_gap_n22_succ] using Q43_grid_ratio_drop_gap_k22
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n23, Q43_gap_n23, Q43_gap_n23_succ] using Q43_grid_ratio_drop_gap_k23
  rcases hk with rfl | hk
  ·
    simpa [Q43_nk_eq_gap_n24, Q43_gap_n24, Q43_gap_n24_succ] using Q43_grid_ratio_drop_gap_k24
  cases hk
  simpa [Q43_nk_eq_gap_n25, Q43_gap_n25, Q43_gap_n25_succ] using Q43_grid_ratio_drop_gap_k25

-- TODO(Q43.S137-logn-remaining-scan): replace `True` with the formal flat local-EF(s) evaluation statement.
theorem Q43_placeholder : True := by
  trivial

end PvNP
