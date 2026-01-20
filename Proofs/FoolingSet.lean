import Mathlib.Computability.Language
import Mathlib.Computability.MyhillNerode

theorem fooling_set_argument {L : Language α} (f : ℕ → List α)
  (hf : ∀ i j : ℕ, i < j → ∃ z, (f i ++ z) ∈ L ∧ (f j ++ z) ∉ L) : ¬L.IsRegular := by

  refine (mt Language.IsRegular.finite_range_leftQuotient) ?_
  let F := fun n => L.leftQuotient (f n)
  apply Set.infinite_of_injective_forall_mem (f := F)

  · -- 1) Function.Injective F
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

  · -- 2) ∀ (x : ℕ), F x ∈ Set.range L.leftQuotient
    intro x
    exact Set.mem_range_self (f x)
