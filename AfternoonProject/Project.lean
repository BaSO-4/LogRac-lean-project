import Mathlib
open List
open BigOperators
open Finset
open Finset.antidiagonal

/- Small tasks -/

/- 1 -/
def catalan_number: (n : ℕ) → ℕ
| 0 => 1
| n+1 => ∑ i : Fin (n+1), (catalan_number i) * (catalan_number (n-i))

/- 2 -/
inductive plane_tree: Type
| node : (List plane_tree) → plane_tree

/- 3 -/
inductive full_binary_tree: Type
| leaf : full_binary_tree
| node₂: (T1 T2 : full_binary_tree) → full_binary_tree

/- 4 -/
inductive full_binary_tree_with_nodes : (n : ℕ) → Type
| leaf : full_binary_tree_with_nodes 0
| node₂ : {m n : ℕ} → full_binary_tree_with_nodes m → full_binary_tree_with_nodes n → full_binary_tree_with_nodes (m + n + 1)

/- 5 -/
inductive ballot : ℕ → ℕ → Type
| nil : ballot 0 0
| next_1 : {sum n : ℕ} → ballot sum n → ballot (sum + 1) (n + 1)
| next_minus1 : {sum n : ℕ} → ballot (sum + 1) n → ballot sum (n + 1)


/- Larger tasks -/

/- 4 -/
def plane_tree.to_List_plane_tree : plane_tree -> List plane_tree
| .node l => l

def list_to_plane_tree : List plane_tree -> plane_tree
| l => plane_tree.node l

theorem list_of_plane_tree_of_list_is_list: ∀ (l : List plane_tree), ((list_to_plane_tree l).to_List_plane_tree) = l := by
  exact fun l ↦ rfl

theorem plane_tree_of_list_of_plane_tree_is_plane_tree: ∀ (pt : plane_tree), (list_to_plane_tree (pt.to_List_plane_tree)) = pt := by
  intro pt
  sorry
  /- TODO -/
