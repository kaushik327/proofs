import Mathlib.Computability.Language
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Set.Finite.Basic

def zero : Bool := false
def one : Bool := true

def L01 : Language Bool :=
  { w | ∃ n : ℕ, w = List.replicate n zero ++ List.replicate n one }

theorem L01_is_irregular : ¬L01.IsRegular := by

  have h : (Set.range L01.leftQuotient).Infinite := by {

    -- "fooling set"
    let f := fun n : ℕ => L01.leftQuotient (List.replicate n zero)

    let f_is_injective : Function.Injective f := by {
      intro (i : ℕ) (j : ℕ)
      contrapose
      intro i_ne_j

      let x := List.replicate i zero
      let y := List.replicate j zero
      let z := List.replicate i one -- distinguishing suffix

      have xz_in_L : (x ++ z ∈ L01) := by use i
      have yz_not_in_L : (y ++ z ∉ L01) := by {
        by_contra h

        sorry
      }
      exact ne_of_mem_of_not_mem' xz_in_L yz_not_in_L
    }

    let f_within_s : (∀ (x : ℕ), f x ∈ (Set.range L01.leftQuotient)) := by {
      exact fun x ↦ Set.mem_range_self (List.replicate x zero)
    }

    exact Set.infinite_of_injective_forall_mem f_is_injective f_within_s
  }

  by_contra l_is_regular
  let set_is_finite := Language.IsRegular.finite_range_leftQuotient l_is_regular
  contradiction
