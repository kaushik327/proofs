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
  intro i j i_lt_j
  exists (List.replicate i one) -- distinguishing suffix: 1^i
  apply And.intro _ _
  · -- 0^i 1^i ∈ L01 (take n=i)
    use i
  · -- 0^j 1^i ∉ L01 by counting
    intro h
    obtain ⟨n, hn⟩ := h

    have := congrArg (fun l => (l.count one, l.count zero)) hn
    simp [F, List.count_replicate, zero, one] at this
    omega

def palindrome : Language Bool :=
  { w | w = w.reverse }

theorem palindrome_is_irregular : ¬palindrome.IsRegular := by
  let F := fun n => (List.replicate n zero) ++ [one] -- fooling set: 0^n 1
  refine fooling_set_argument F ?_
  intro i j i_lt_j
  exists (List.replicate i zero) -- distinguishing suffix: 0^i

  rw [palindrome, Set.mem_setOf_eq, Set.mem_setOf_eq]

  simp [F] -- reduces to yz case: 0^j 1 0^i ≠ 0^i 1 0^j
  intro hn
  apply congrArg (fun str => str[i]?) at hn

  -- proving that index i is valid
  let s := List.replicate j zero ++ one :: List.replicate i zero
  have : s.length = j + 1 + i := by simp [s]; omega

  simp [s, this, i_lt_j] at hn
  contradiction
