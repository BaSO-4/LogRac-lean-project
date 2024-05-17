import Mathlib
open List
/- 5.4. -/

/- The type of binary trees -/
/-A Binary tree is a tree that branches in at most 2 subtrees at every node
  A full binary tree is a binary tree that branches in either 2 or 0 subtrees-/

/- declaring an inductive type in lean -/
inductive binary_tree : Type
| leaf : binary_tree
| node₁ : binary_tree → binary_tree
| node₂ : binary_tree → binary_tree → binary_tree

/- The height of a binary tree -/
def binary_tree.height : binary_tree → ℕ
| .leaf => 1
| .node₁ T => T.height + 1
| .node₂ T1 T2 => max T1.height T2.height + 1

/- The number of nodes (including leaves) of a binary tree -/
def binary_tree.number_of_nodes : binary_tree → ℕ
| .leaf => 1
| .node₁ T => T.number_of_nodes + 1
| .node₂ T1 T2 => T1.number_of_nodes + T2.number_of_nodes + 1

/- The type of full binary trees -/
/- Small task 3 -/
inductive full_binary_tree: Type
| leaf : full_binary_tree
| node₂: (T1 T2 : full_binary_tree) → full_binary_tree

def full_binary_tree.height : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => max T1.height T2.height + 1

def full_binary_tree.number_of_nodes : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => T1.number_of_nodes + T2.number_of_nodes + 1

def binary_tree_of_full_binary_tree : full_binary_tree → binary_tree
| .leaf => .leaf
| .node₂ T1 T2 => .node₂ (binary_tree_of_full_binary_tree T1) (binary_tree_of_full_binary_tree T2)

theorem eq_height_binary_tree_of_full_binary_tree :
  (T : full_binary_tree) → T.height = (binary_tree_of_full_binary_tree T).height := by
intro T
induction T with
| leaf => rfl
| node₂ T1 T2 HT1 HT2 =>
  simp [full_binary_tree.height, binary_tree.height]
  rw [HT1, HT2]

theorem eq_number_of_nodes_binary_tree_of_full_binary_tree:
  (T : full_binary_tree) → T.number_of_nodes = (binary_tree_of_full_binary_tree T).number_of_nodes := by
intro T
induction T with
| leaf => rfl
| node₂ T1 T2 HT1 HT2 =>
  simp [full_binary_tree.number_of_nodes, binary_tree.number_of_nodes]
  rw [HT1, HT2]

inductive binary_tree_with_nodes : (n : ℕ) → Type
| leaf : binary_tree_with_nodes 1
| node₁ : {n : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes (n + 1)
| node₂ : {m n : ℕ} → binary_tree_with_nodes m → binary_tree_with_nodes n → binary_tree_with_nodes (m + n + 1)

/- The tyhe of vectors of elements in a type A (aka. labeled unary trees) -/
inductive vector (A : Type) : (n : ℕ) → Type
| nil : vector A 0
| cons : (n : ℕ) → A → vector A n → vector A (n + 1)

/- A function converting binary trees with n nodes to ordinary binary trees -/
def binary_tree_of_binary_tree_with_nodes {n : ℕ} : binary_tree_with_nodes n → binary_tree
| .leaf => .leaf
| .node₁ T => .node₁ (binary_tree_of_binary_tree_with_nodes T)
| .node₂ T1 T2 => .node₂ (binary_tree_of_binary_tree_with_nodes T1) (binary_tree_of_binary_tree_with_nodes T2)

theorem eq_number_of_nodes_binary_tree_of_binary_tree_with_nodes:
  ∀ (n : ℕ) (T : binary_tree_with_nodes n),
  n = (binary_tree_of_binary_tree_with_nodes T).number_of_nodes := by
intros n T
induction T with
| leaf => rfl
| node₁ T HT1 =>
  simp [binary_tree.number_of_nodes]
  exact HT1
| node₂ T1 T2 HT1 HT2 =>
  simp [binary_tree.number_of_nodes]
  rw [← HT1, ← HT2]

/- 12.4 -/

/- Small task 2 -/
inductive plane_tree: Type
| node : (List plane_tree) → plane_tree

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


def plane_tree.to_full_binary_tree: plane_tree → full_binary_tree
| .node nil => full_binary_tree.leaf
| .node (cons T l) => .node₂ T.to_full_binary_tree (node l).to_full_binary_tree


/- TODO -/
/- def full_binary_tree.to_plane_tree : full_binary_tree → plane_tree
| .leaf => .node nil
| .node₂ T1 T2 => -/



/- theorem plane_tree_eq_list_plane_tree :
  (l : List plane_tree) -> (PT : plane_tree) -> l = (PT.definicija) := by
  intro l PT
  cases PT with N -/


  /- TODO:
  This theorem and show that plane trees are isomorphic to Full binary trees
   -define function from FBT to Plane tree and show if you use one after another you get what you started with-/

-- note: Stanley Catalan numbers p 5-9


/- 19.4. -/

/- Define the Catalan numbers by their recursive relation (or use their existing definition in  matlib)
  C_0 = 1
  C_n+1 = sum(c_i * c_n-i)
  Deduce that C_n is the number of full binary trees with n nodes(excluding leaves)

  Outline of proof:
    # : FBT → ℕ
    sum(# T = n) → (bijection) FinCn; where sum is over T:FBT

  Make a githup repo for project
    import «Lograc».path_to_file


  TODO: slika table-/

open BigOperators
open Finset
open Finset.antidiagonal

/- Small task 1 -/
def catalan_number: (n : ℕ) → ℕ
| 0 => 1
| n+1 => ∑ i : Fin (n+1), (catalan_number i) * (catalan_number (n-i))


/- 10.5 -/
/- inductive ballot : (sum n : ℕ) → Type
| nil : ballot 0 0
| next_1 : ballot sum n → ballot (sum + 1) (n + 1)
| next_minus1 : ballot sum n → ballot (sum - 1) (n + 1) -/


/- 17.5 -/
