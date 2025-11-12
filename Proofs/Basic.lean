import Mathlib.Computability.Language
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Lemmas
import Proofs.FoolingSet

def zero : Bool := false
def one : Bool := true

def L01 : Language Bool :=
  { w | ∃ n : ℕ, w = List.replicate n zero ++ List.replicate n one }

theorem L01_is_irregular : ¬L01.IsRegular := by
  let F := fun n => List.replicate n zero -- fooling set: 0^n
  refine fooling_set_argument F ?_
  intro i j i_ne_j
  exists (List.replicate i one) -- distinguishing suffix: 1^i
  apply And.intro _ _
  · -- 0^i 1^i ∈ L01 (take n=i)
    use i
  · -- 0^j 1^i ∉ L01 by counting
    intro h
    obtain ⟨n, hn⟩ := h

    have i_eq_n : i = n := by
      have := congrArg (fun l => l.count one) hn
      simp [F, List.count_replicate, zero, one] at this
      exact this

    have j_eq_n : j = n := by
      have := congrArg (fun l => l.count zero) hn
      simp [F, List.count_replicate, zero, one] at this
      exact this

    rw [i_eq_n, j_eq_n] at i_ne_j
    exact i_ne_j rfl

def palindrome : Language Bool :=
  { w | w = w.reverse }

theorem palindrome_is_irregular : ¬palindrome.IsRegular := by
  let F := fun n => (List.replicate n zero) ++ [one] -- fooling set: 0^n 1
  refine fooling_set_argument F ?_
  intro i j i_ne_j
  exists (List.replicate i zero) -- distinguishing suffix: 0^i
  apply And.intro _ _
  · -- 0^i 1^i ∈ L01 (take n=i)
    rw [palindrome, Set.mem_setOf_eq]
    simp [F]
  · -- 0^j 1^i ∉ palindrome by element comparison
    rw [palindrome, Set.mem_setOf_eq]
    simp [F]
    intro hn
    have str_diff := congrArg (fun str => str.getD i zero) hn

    have x : (List.replicate j zero ++ one :: List.replicate i zero).length = j + 1 + i := by
      simp
      omega

    simp [x] at str_diff

    /-
Prove: i ≠ j => 0^j 1 0^i ≠ 0^i 1 0^j
if i < j:
  consider the i'th element of each string
  0^j 1 0^i has i'th element 0
  0^i 1 0^j has i'th element 1
    -/
    cases lt_or_gt_of_ne i_ne_j with
    | inl i_lt_j =>
      simp [i_lt_j] at str_diff
      contradiction
    | inr j_lt_i =>
      simp [List.getElem_append, List.getElem_cons] at str_diff
      simp [j_lt_i, Nat.lt_asymm, Nat.sub_ne_zero_of_lt] at str_diff
      contradiction
