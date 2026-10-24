import Strictness.Semantics.FixAdmissibility
import Strictness.Semantics.FixEnvironment
import Strictness.Semantics.SemanticSubstitution

namespace Strictness

open Usage
open Term

/-- The semantic case for T-Fix* with outer strict raising.

The simple-typing premise is the erasure of the body judgment,
before identifying the erased
recursive-variable type with the erased result type.

V is established for every finite approximation. D is established for all
positive approximations, which suffices for the cofinal limit lemma; no
assumption that the result type is non-Lazy is needed. -/
theorem fundamental_fix_of_simpleTyping
    {Γ Δ : Env} {σ τ : Ty} {body : Term} {ρ : Substitution}
    (hBodySimple : HasType (Env.erase (σ :: Γ)) body τ.erase)
    (hSub : Ty.Subtype τ (Ty.raiseStrict σ))
    (hPlus : Env.plus Γ (Env.scale (Usage.scale σ.outer top) Γ) = some Δ)
    (ihBody : ∀ η : Substitution,
      Valid (σ :: Γ) η →
      V τ (Substitution.apply η body) ∧
        (SatisfiesD (σ :: Γ) η → D τ (Substitution.apply η body)))
    (hValid : Valid Δ ρ) :
    V τ (Substitution.apply ρ (.fix body)) ∧
      (SatisfiesD Δ ρ → D τ (Substitution.apply ρ (.fix body))) := by
  have hValidΓ : Valid Γ ρ := valid_of_fix_context hPlus hValid
  have hErase : τ.erase = σ.erase := by
    have h := Ty.subtype_erase hSub
    simpa only [Ty.erase_raiseStrict] using h
  have hSimpleBody : HasType (τ.erase :: Env.erase Γ) body τ.erase := by
    have h : HasType (σ.erase :: Env.erase Γ) body τ.erase := hBodySimple
    rw [← hErase] at h
    exact h
  let closedBody : Term := Substitution.applyAt ρ 1 body
  have hFix : AllTerms τ.erase (.fix closedBody) := by
    exact allTerms_fix_closed hSimpleBody
      (fun i A hi => (hValidΓ.simpleValid_erased i A hi).2)
  have hIntoHead : ∀ {a : Term}, V τ a → V σ a := by
    intro a ha
    have hRaised : V (Ty.raiseStrict σ) a := (semantic_subtype hSub).1 ha
    rw [V_raiseStrict σ] at hRaised
    exact hRaised
  have hNext (n : Nat) :
      Substitution.apply
        (Substitution.extend ρ (Term.fixApprox closedBody n)) body =
        Term.fixApprox closedBody (n + 1) := by
    exact Substitution.apply_extend_eq_instantiate_of_closed
      ρ (Term.fixApprox closedBody n) body hValidΓ.1
      (fixApprox_mem_allTerms hFix n).1
  have hApproxV : ∀ n, V τ (Term.fixApprox closedBody n) := by
    intro n
    induction n with
    | zero =>
        exact divergentTerms_subset_V τ
          ⟨omega_mem_allTerms τ.erase, Term.omega_diverges⟩
    | succ n ih =>
        have hExt : Valid (σ :: Γ)
            (Substitution.extend ρ (Term.fixApprox closedBody n)) :=
          valid_extend_head (hIntoHead ih) hValidΓ
        have hV := (ihBody _ hExt).1
        rw [hNext n] at hV
        exact hV
  have hApproxHeadV (n : Nat) : V σ (Term.fixApprox closedBody n) :=
    hIntoHead (hApproxV n)
  have hStepD (n : Nat)
      (hWitness : D σ (Term.fixApprox closedBody n) ∨ SatisfiesD Γ ρ) :
      D τ (Term.fixApprox closedBody (n + 1)) := by
    have hExt : Valid (σ :: Γ)
        (Substitution.extend ρ (Term.fixApprox closedBody n)) :=
      valid_extend_head (hApproxHeadV n) hValidΓ
    have hExtD : SatisfiesD (σ :: Γ)
        (Substitution.extend ρ (Term.fixApprox closedBody n)) := by
      rcases hWitness with hHead | hTail
      · exact satisfiesD_extend_head hHead
      · exact satisfiesD_extend_tail hTail
    have hD := (ihBody _ hExt).2 hExtD
    rw [hNext n] at hD
    exact hD
  change V τ (.fix closedBody) ∧
    (SatisfiesD Δ ρ → D τ (.fix closedBody))
  constructor
  · exact fixApprox_mem_V_limit hFix hApproxV
  · intro hD
    apply fixApprox_mem_D_of_cofinal hFix
    by_cases hStrict : strict ≤ σ.outer
    · have hOuter : σ.outer = strict ∨ σ.outer = top :=
        Usage.le_strict_iff.mp hStrict
      have hNotLazy : ¬ Ty.IsLazy σ := by
        rcases hOuter with hS | hTop
        · exact not_lazy_of_outer_strict hS
        · exact not_lazy_of_outer_top hTop
      have hOrdinary : Ty.Subtype τ σ := by
        have hRaise : Ty.raiseStrict σ = σ :=
          Ty.raiseStrict_eq_self_of_outer hOuter
        rw [hRaise] at hSub
        exact hSub
      have hApproxHeadD : ∀ n, D σ (Term.fixApprox closedBody n) := by
        intro n
        induction n with
        | zero => exact omega_mem_D_of_not_lazy hNotLazy
        | succ n ih =>
            exact (semantic_subtype hOrdinary).2 (hStepD n (Or.inl ih))
      intro N
      exact ⟨N + 1, Nat.le_succ N, hStepD N (Or.inl (hApproxHeadD N))⟩
    · have hContext : Δ = Γ := fix_context_eq_of_not_strict hStrict hPlus
      have hTail : SatisfiesD Γ ρ := by
        rw [hContext] at hD
        exact hD
      intro N
      exact ⟨N + 1, Nat.le_succ N, hStepD N (Or.inr hTail)⟩

end Strictness
