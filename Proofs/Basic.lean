import Mathlib.Computability.Language
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Finite.Basic
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
