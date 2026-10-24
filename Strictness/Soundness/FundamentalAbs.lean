import Strictness.Semantics.SemanticSubstitution
import Strictness.Semantics.SemanticEquivalence
import Strictness.Soundness.FundamentalRules
import Strictness.Language.Erasure
import Strictness.Language.SimpleSubstitution

namespace Strictness

open Usage
open Term

/-- A simply typed lambda abstraction remains in the erased simple type
after applying a valid semantic substitution.  This is the simple-typing
component needed by the function clauses of `V` and `D`. -/
theorem lambda_allTerms_of_simpleTyping
    {Γ : Env} {σ τ : Ty} {body : Term} {ρ : Substitution}
    (hBody : Term.HasType (σ.erase :: Env.erase Γ) body τ.erase)
    (hImages : ∀ i α, Term.lookup (Env.erase Γ) i = some α → AllTerms α (ρ i)) :
    AllTerms (.arrow σ.erase τ.erase) (Substitution.apply ρ (.lam body)) := by
  have hBodySimple0 := hBody
  have hBodySimple :
      Term.HasType ([σ.erase] ++ Env.erase Γ) body τ.erase := by
    simpa [Env.erase] using hBodySimple0
  have hBodyApplied :
      Term.HasType [σ.erase] (Substitution.applyAt ρ 1 body) τ.erase := by
    apply Term.hasType_applyAt (B := [σ.erase]) (Γ := Env.erase Γ)
      (e := body) (τ := τ.erase) (ρ := ρ)
    · exact hBodySimple
    · intro i α hi
      exact (hImages i α hi).2
  have hLam :
      Term.HasType [] (Substitution.apply ρ (.lam body))
        (.arrow σ.erase τ.erase) := by
    simpa [Substitution.apply] using (Term.HasType.lam hBodyApplied)
  exact ⟨Term.hasType_nil_closed hLam, hLam⟩

/-- The T-Abs V-case, with the typing induction hypotheses supplied explicitly.
The only nontrivial usage cases are `?` and `S`; `L` and `⊤` are whole-type
cases in the logical relation. -/
theorem fundamental_abs_V_of_simpleTyping
    {Γ : Env} {σ τ : Ty} {u : Usage} {body : Term} {ρ : Substitution}
    (hBody : Term.HasType (σ.erase :: Env.erase Γ) body τ.erase)
    (ihV : ∀ {ρ : Substitution},
      Valid (σ :: Γ) ρ → V τ (Substitution.apply ρ body))
    (ihD : ∀ {ρ : Substitution},
      Valid (σ :: Γ) ρ → SatisfiesD (σ :: Γ) ρ →
        D τ (Substitution.apply ρ body))
    (hValid : Valid (Env.scale u Γ) ρ) :
    V (.arrow σ τ u) (Substitution.apply ρ (.lam body)) := by
  cases u with
      | unknown =>
          have hValidΓ : Valid Γ ρ := valid_of_unknown_scale hValid
          have hAll := lambda_allTerms_of_simpleTyping hBody
            hValidΓ.simpleValid_erased
          unfold V LogicalModel.acceptable operationalModel
          simp only [Usage.not_lazy_le_unknown]
          apply Or.inr
          refine ⟨hAll, Substitution.applyAt ρ 1 body, Eval.lam, ?_, ?_⟩
          · intro a ha
            have hExtValid := valid_extend_head ha hValidΓ
            have hBodyV := ihV hExtValid
            have hEq := Substitution.apply_extend_eq_instantiate_of_closed
              ρ a body hValidΓ.1 (V_closed ha)
            rw [hEq] at hBodyV
            have hContractAll : AllTerms τ.erase
                (Term.instantiate (Substitution.applyAt ρ 1 body) a) :=
              V_subset_allTerms τ hBodyV
            have hBeta := semEq_beta hAll
              (V_subset_allTerms σ ha) hContractAll
            have hApp := (semantic_equiv_VD hBeta).1.mpr hBodyV
            simpa [Substitution.apply] using hApp
          · intro a ha
            have hExtValid := valid_extend_head
              (D_subset_V σ ha) hValidΓ
            have hExtD := satisfiesD_extend_head (Γ := Γ) (ρ := ρ) ha
            have hBodyD := ihD hExtValid hExtD
            have hEq := Substitution.apply_extend_eq_instantiate_of_closed
              ρ a body hValidΓ.1 (D_closed ha)
            rw [hEq] at hBodyD
            have hContractAll : AllTerms τ.erase
                (Term.instantiate (Substitution.applyAt ρ 1 body) a) :=
              D_subset_allTerms τ hBodyD
            have hBeta := semEq_beta hAll
              (D_subset_allTerms σ ha) hContractAll
            have hApp := (semantic_equiv_VD hBeta).2.mpr hBodyD
            simpa [Substitution.apply] using hApp
      | strict =>
          have hValidΓ : Valid Γ ρ := valid_of_strict_scale hValid
          have hAll := lambda_allTerms_of_simpleTyping hBody
            hValidΓ.simpleValid_erased
          unfold V LogicalModel.acceptable operationalModel
          simp only [Usage.not_lazy_le_strict]
          apply Or.inr
          refine ⟨hAll, Substitution.applyAt ρ 1 body, Eval.lam, ?_, ?_⟩
          · intro a ha
            have hExtValid := valid_extend_head ha hValidΓ
            have hBodyV := ihV hExtValid
            have hEq := Substitution.apply_extend_eq_instantiate_of_closed
              ρ a body hValidΓ.1 (V_closed ha)
            rw [hEq] at hBodyV
            have hContractAll : AllTerms τ.erase
                (Term.instantiate (Substitution.applyAt ρ 1 body) a) :=
              V_subset_allTerms τ hBodyV
            have hBeta := semEq_beta hAll
              (V_subset_allTerms σ ha) hContractAll
            have hApp := (semantic_equiv_VD hBeta).1.mpr hBodyV
            simpa [Substitution.apply] using hApp
          · intro a ha
            have hExtValid := valid_extend_head
              (D_subset_V σ ha) hValidΓ
            have hExtD := satisfiesD_extend_head (Γ := Γ) (ρ := ρ) ha
            have hBodyD := ihD hExtValid hExtD
            have hEq := Substitution.apply_extend_eq_instantiate_of_closed
              ρ a body hValidΓ.1 (D_closed ha)
            rw [hEq] at hBodyD
            have hContractAll : AllTerms τ.erase
                (Term.instantiate (Substitution.applyAt ρ 1 body) a) :=
              D_subset_allTerms τ hBodyD
            have hBeta := semEq_beta hAll
              (D_subset_allTerms σ ha) hContractAll
            have hApp := (semantic_equiv_VD hBeta).2.mpr hBodyD
            simpa [Substitution.apply] using hApp
      | lazy =>
          have hImages0 := hValid.simpleValid_erased
          have hImages :
              ∀ i α, Term.lookup (Env.erase Γ) i = some α → AllTerms α (ρ i) := by
            simpa [Env.erase_scale] using hImages0
          have hAll := lambda_allTerms_of_simpleTyping hBody hImages
          rw [V_eq_allTerms_of_outer_lazy rfl]
          exact hAll
      | top =>
          have hImages0 := hValid.simpleValid_erased
          have hImages :
              ∀ i α, Term.lookup (Env.erase Γ) i = some α → AllTerms α (ρ i) := by
            simpa [Env.erase_scale] using hImages0
          have hAll := lambda_allTerms_of_simpleTyping hBody hImages
          rw [V_eq_allTerms_of_outer_top rfl]
          exact hAll

/-- The T-Abs D-case.  For `?` and `L`, the scaled environment is entirely
Lazy, so the D-side premise is impossible.  For `⊤`, the result D-set is the
whole erased type.  For `S`, an existing D-witness in the outer environment is
preserved when the argument is added to the binder. -/
theorem fundamental_abs_D_of_simpleTyping
    {Γ : Env} {σ τ : Ty} {u : Usage} {body : Term} {ρ : Substitution}
    (hBody : Term.HasType (σ.erase :: Env.erase Γ) body τ.erase)
    (ihV : ∀ {ρ : Substitution},
      Valid (σ :: Γ) ρ → V τ (Substitution.apply ρ body))
    (ihD : ∀ {ρ : Substitution},
      Valid (σ :: Γ) ρ → SatisfiesD (σ :: Γ) ρ →
        D τ (Substitution.apply ρ body))
    (hValid : Valid (Env.scale u Γ) ρ)
    (hD : SatisfiesD (Env.scale u Γ) ρ) :
    D (.arrow σ τ u) (Substitution.apply ρ (.lam body)) := by
  cases u with
      | unknown =>
          exact False.elim ((not_satisfiesD_of_lazy
            (Env.isLazy_unknown_scale Γ)) hD)
      | strict =>
          have hValidΓ : Valid Γ ρ := valid_of_strict_scale hValid
          have hDΓ : SatisfiesD Γ ρ := by
            simpa [Env.strict_scale] using hD
          have hAll := lambda_allTerms_of_simpleTyping hBody
            hValidΓ.simpleValid_erased
          have hLamV : V (.arrow σ τ strict)
              (Substitution.apply ρ (.lam body)) :=
            fundamental_abs_V_of_simpleTyping hBody ihV ihD hValid
          unfold D LogicalModel.divergentSide operationalModel
          simp only [not_lazy_of_outer_strict (τ := .arrow σ τ strict) rfl,
            Usage.not_lazy_le_strict]
          apply Or.inr
          refine ⟨hLamV, Substitution.applyAt ρ 1 body, Eval.lam, ?_⟩
          intro a ha
          have hExtValid := valid_extend_head ha hValidΓ
          have hExtD := satisfiesD_extend_tail (σ := σ) (a := a) hDΓ
          have hBodyD := ihD hExtValid hExtD
          have hEq := Substitution.apply_extend_eq_instantiate_of_closed
            ρ a body hValidΓ.1 (V_closed ha)
          rw [hEq] at hBodyD
          have hContractAll : AllTerms τ.erase
              (Term.instantiate (Substitution.applyAt ρ 1 body) a) :=
            D_subset_allTerms τ hBodyD
          have hBeta := semEq_beta hAll
            (V_subset_allTerms σ ha) hContractAll
          have hApp := (semantic_equiv_VD hBeta).2.mpr hBodyD
          simpa [Substitution.apply] using hApp
      | lazy =>
          exact False.elim ((not_satisfiesD_of_lazy
            (Env.isLazy_lazy_scale Γ)) hD)
      | top =>
          have hImages0 := hValid.simpleValid_erased
          have hImages :
              ∀ i α, Term.lookup (Env.erase Γ) i = some α → AllTerms α (ρ i) := by
            simpa [Env.erase_scale] using hImages0
          have hAll := lambda_allTerms_of_simpleTyping hBody hImages
          rw [D_eq_allTerms_of_outer_top rfl]
          exact hAll

end Strictness
