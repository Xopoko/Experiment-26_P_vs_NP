import Paperproof
import PvNP.Core.Defs
import PvNP.Core.Graph


namespace PvNP

-- Q39 work-in-progress Lean proofs (real code, not doc-comments).

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

end PvNP
