import Mathlib.Computability.Language
import Mathlib.Computability.MyhillNerode

theorem fooling_set_argument {L : Language α} (f : ℕ → List α)
  (hf : ∀ i j : ℕ, i < j → ∃ z, (f i ++ z) ∈ L ∧ (f j ++ z) ∉ L) : ¬L.IsRegular := by

  let F := fun n => L.leftQuotient (f n)

  have F_is_injective : Function.Injective F := by {
    intro u v
    contrapose
    intro u_ne_v
    cases lt_or_gt_of_ne u_ne_v with
    | inl u_lt_v =>
      obtain ⟨z, h₁, h₂⟩ := hf u v u_lt_v
      exact ne_of_mem_of_not_mem' h₁ h₂
    | inr v_lt_u =>
      obtain ⟨z, h₁, h₂⟩ := hf v u v_lt_u
      exact Ne.symm (ne_of_mem_of_not_mem' h₁ h₂)
  }

  let F_within_s : (∀ (x : ℕ), F x ∈ (Set.range L.leftQuotient)) := by {
    intro x
    exact Set.mem_range_self _
  }

  have infinite_states : (Set.range L.leftQuotient).Infinite :=
    Set.infinite_of_injective_forall_mem F_is_injective F_within_s

  exact mt Language.IsRegular.finite_range_leftQuotient infinite_states
