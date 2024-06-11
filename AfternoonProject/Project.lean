import Mathlib
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
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
  intro lpt
  cases lpt
  case nil => rfl
  case cons h t => rfl

theorem plane_tree_of_list_of_plane_tree_is_plane_tree: ∀ (pt : plane_tree), (list_to_plane_tree (pt.to_List_plane_tree)) = pt := by
  intro pt
  cases pt
  case node N => rfl

/- 6 -/
/- Prove that bin{2n}{n} is divisible by n+1 -/

lemma twon_minus_n_eq_n (n : ℕ) : 2 * n - n = n := by
  omega

lemma two_n_minus_n_plus_one_eq_n_minus_one (n : ℕ): 2*n - (n+1) = n-1 := by
  omega

lemma one_over_n_minus_one_factorial_eq_n_over_n_factorial (n : ℕ) (h : n > 0) :
1 / Nat.factorial (n - 1) = n / Nat.factorial n := by
apply Nat.div_eq_of_eq_mul_right
apply Nat.factorial_pos
-- rw [← mul_div_assoc] -- zakaj to ne dela? Če uporabimo spodnjo, dobimo še pogoj n! | n ...
rw [← Nat.mul_div_assoc]
rw [mul_comm]
rw [Nat.mul_factorial_pred]
rw [Nat.div_self]
apply Nat.factorial_pos
apply h
sorry

-- tole je samo kot helper: če se nam v equality rata znebit imenovalcev
lemma no_denoms (n : ℕ) (h : n > 0) :
Nat.factorial (2 * n) * (n + 1) * Nat.factorial n * Nat.factorial n = n * Nat.factorial (2 * n) * Nat.factorial (n - 1) * Nat.factorial (n + 1) := by
rw [mul_comm n (Nat.factorial (2 * n))]
rw [mul_assoc, mul_assoc, ← mul_assoc (n + 1)]
rw [← Nat.factorial_succ]
rw [mul_assoc, mul_assoc, ← mul_assoc n]
rw [Nat.mul_factorial_pred]
rw [mul_comm (Nat.factorial n) (Nat.factorial (n + 1))]
apply h

lemma equality (n : ℕ) (h : n > 0):
Nat.choose (2 * n) (n + 1) = n / (n + 1) * Nat.choose (2 * n) n := by
rw [Nat.choose_eq_factorial_div_factorial, Nat.choose_eq_factorial_div_factorial]
rw [twon_minus_n_eq_n, two_n_minus_n_plus_one_eq_n_minus_one]
apply Nat.div_eq_of_eq_mul_right
apply Nat.mul_pos
apply Nat.factorial_pos
apply Nat.factorial_pos
sorry

-- rešimo za n>0
theorem n_plus_one_divides_2n_choose_n_non_zero (n : Nat) (h : n > 0) :
n + 1 ∣ Nat.choose (2 * n) n := by sorry


-- razdelimo na 0 in succ: 0 je obv, n>0 pa rabimo kot predpostavko za naprej
theorem n_plus_one_divides_2n_choose_n (n : Nat) :
n + 1 ∣ Nat.choose (2 * n) n := by
match n with
  | 0 =>
    omega
  | Nat.succ k =>
    apply n_plus_one_divides_2n_choose_n_non_zero (Nat.succ k)
    exact Nat.zero_lt_succ k
