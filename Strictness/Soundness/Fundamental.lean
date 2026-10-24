import Strictness.Language.Typing
import Strictness.Soundness.FundamentalControl
import Strictness.Semantics.DefiniteD
import Strictness.Soundness.FundamentalFix

namespace Strictness

open Usage
open Term

/-- Fundamental lemma for the declarative typing judgment. -/
theorem fundamental
    {Γ : Env} {e : Term} {τ : Ty}
    (hTyping : Typing Γ e τ) :
    ∀ ρ : Substitution,
      Valid Γ ρ →
      V τ (Substitution.apply ρ e) ∧
      (SatisfiesD Γ ρ → D τ (Substitution.apply ρ e)) := by
  induction hTyping with
  | const hLazy =>
      intro ρ hValid
      constructor
      · exact fundamental_const_V hValid
      · intro hD
        exact fundamental_const_D hLazy hValid hD

  | var hLazy =>
      intro ρ hValid
      constructor
      · exact fundamental_var_V hValid
      · intro hD
        exact fundamental_var_D hLazy hValid hD

  | varSkip hVar hLazy ihVar =>
      intro ρ hValid
      have ihV := fun {ρ : Substitution} hValid' =>
        (ihVar ρ hValid').1
      have ihD := fun {ρ : Substitution} hValid' hD' =>
        (ihVar ρ hValid').2 hD'
      constructor
      · exact fundamental_varSkip_V ihV hValid
      · intro hD
        exact fundamental_varSkip_D hLazy ihV ihD hValid hD

  | abs hBody hu ihBody =>
      intro ρ hValid
      have ihV := fun {ρ : Substitution} hValid' =>
        (ihBody ρ hValid').1
      have ihD := fun {ρ : Substitution} hValid' hD' =>
        (ihBody ρ hValid').2 hD'
      constructor
      · exact fundamental_abs_V_of_simpleTyping
          (typing_erasure hBody) ihV ihD hValid
      · intro hD
        exact fundamental_abs_D_of_simpleTyping
          (typing_erasure hBody) ihV ihD hValid hD

  | app hFun hArg hSub hu hPlus ihFun ihArg =>
      intro ρ hValid
      have hValidSplit :=
        valid_plus_split_of_semantic semantic_plus_V hPlus hValid
      have ihV₁ := fun {ρ : Substitution} hValid' =>
        (ihFun ρ hValid').1
      have ihD₁ := fun {ρ : Substitution} hValid' hD' =>
        (ihFun ρ hValid').2 hD'
      have ihV₂ := fun {ρ : Substitution} hValid' =>
        (ihArg ρ hValid').1
      have ihD₂ := fun {ρ : Substitution} hValid' hD' =>
        (ihArg ρ hValid').2 hD'
      constructor
      · exact fundamental_app_V_of_simpleTyping
          (typing_erasure hArg) hSub hu
          ihV₁ ihV₂ hValidSplit.1 hValidSplit.2
      · intro hD
        exact fundamental_app_D_of_simpleTyping
          (typing_erasure hArg) hSub hu
          ihV₁ ihD₁ ihV₂ ihD₂ hValidSplit.1 hValidSplit.2
          (satisfiesD_plus_split_of_semantic semantic_plus_D hPlus hD)

  | pair hLeft hRight hσOuter hτOuter hPlus ihLeft ihRight =>
      intro ρ hValid
      have hValidSplit :=
        valid_plus_split_of_semantic semantic_plus_V hPlus hValid
      have ihV₁ := fun {ρ : Substitution} hValid' =>
        (ihLeft ρ hValid').1
      have ihD₁ := fun {ρ : Substitution} hValid' hD' =>
        (ihLeft ρ hValid').2 hD'
      have ihV₂ := fun {ρ : Substitution} hValid' =>
        (ihRight ρ hValid').1
      have ihD₂ := fun {ρ : Substitution} hValid' hD' =>
        (ihRight ρ hValid').2 hD'
      constructor
      · exact fundamental_pair_V
          ihV₁ ihV₂ hValidSplit.1 hValidSplit.2
      · intro hD
        exact fundamental_pair_D
          hσOuter hτOuter ihV₁ ihD₁ ihV₂ ihD₂
          hValidSplit.1 hValidSplit.2
          (satisfiesD_plus_split_of_semantic semantic_plus_D hPlus hD)

  | projLeft hPair hu hLazy ihPair =>
      intro ρ hValid
      constructor
      · exact fundamental_proj_left_V
          hu hLazy (fun h => (ihPair ρ h).1) hValid
      · intro hD
        exact fundamental_proj_left_D
          hu hLazy
          (fun h => (ihPair ρ h).1)
          (fun h hD' => (ihPair ρ h).2 hD') hValid hD

  | projRight hPair hu hLazy ihPair =>
      intro ρ hValid
      constructor
      · exact fundamental_proj_right_V
          hu hLazy (fun h => (ihPair ρ h).1) hValid
      · intro hD
        exact fundamental_proj_right_D
          hu hLazy
          (fun h => (ihPair ρ h).1)
          (fun h hD' => (ihPair ρ h).2 hD') hValid hD

  | op o hLeft hRight hu₁ hu₂ hPlus ihLeft ihRight =>
      intro ρ hValid
      have ihV₁ := fun {ρ : Substitution} hValid' =>
        (ihLeft ρ hValid').1
      have ihD₁ := fun {ρ : Substitution} hValid' hD' =>
        (ihLeft ρ hValid').2 hD'
      have ihV₂ := fun {ρ : Substitution} hValid' =>
        (ihRight ρ hValid').1
      have ihD₂ := fun {ρ : Substitution} hValid' hD' =>
        (ihRight ρ hValid').2 hD'
      constructor
      · exact fundamental_op_V
          hu₁ hu₂ hPlus ihV₁ ihV₂ hValid
      · intro hD
        exact fundamental_op_D
          hu₁ hu₂ hPlus ihV₁ ihD₁ ihV₂ ihD₂ hValid hD

  | ite hCond hThen hElse hSubThen hSubElse hu hCap hPlus
      ihCond ihThen ihElse =>
      intro ρ hValid
      have ihV₀ := fun {ρ : Substitution} hValid' =>
        (ihCond ρ hValid').1
      have ihD₀ := fun {ρ : Substitution} hValid' hD' =>
        (ihCond ρ hValid').2 hD'
      have ihV₁ := fun {ρ : Substitution} hValid' =>
        (ihThen ρ hValid').1
      have ihD₁ := fun {ρ : Substitution} hValid' hD' =>
        (ihThen ρ hValid').2 hD'
      have ihV₂ := fun {ρ : Substitution} hValid' =>
        (ihElse ρ hValid').1
      have ihD₂ := fun {ρ : Substitution} hValid' hD' =>
        (ihElse ρ hValid').2 hD'
      constructor
      · exact fundamental_if_V
          hSubThen hSubElse hu hCap hPlus
          ihV₀ ihV₁ ihV₂ hValid
      · intro hD
        exact fundamental_if_D
          hSubThen hSubElse hu hCap hPlus
          ihV₀ ihD₀ ihV₁ ihD₁ ihV₂ ihD₂ hValid hD

  | letE hDef hBody hSub hPlus ihDef ihBody =>
      intro ρ hValid
      have hSimple :=
        typing_erasure (Typing.letE hDef hBody hSub hPlus)
      have ihV₁ := fun {ρ : Substitution} hValid' =>
        (ihDef ρ hValid').1
      have ihD₁ := fun {ρ : Substitution} hValid' hD' =>
        (ihDef ρ hValid').2 hD'
      have ihV₂ := fun {ρ : Substitution} hValid' =>
        (ihBody ρ hValid').1
      have ihD₂ := fun {ρ : Substitution} hValid' hD' =>
        (ihBody ρ hValid').2 hD'
      constructor
      · exact fundamental_let_V_of_simpleTyping
          hSimple hSub hPlus ihV₁ ihV₂ hValid
      · intro hD
        exact fundamental_let_D_of_simpleTyping
          hSimple hSub hPlus ihV₁ ihD₁ ihD₂ hValid hD

  | fix hBody hSub hPlus ihBody =>
      intro ρ hValid
      exact fundamental_fix_of_simpleTyping
        (typing_erasure hBody) hSub hPlus ihBody hValid

  | sub hBody hEnvSub hTySub ihBody =>
      intro ρ hValid
      constructor
      · exact fundamental_sub_V
          (fun h => (ihBody ρ h).1)
          hEnvSub hTySub hValid
      · intro hD
        exact fundamental_sub_D
          (fun h hD' => (ihBody ρ h).2 hD')
          hEnvSub hTySub hValid hD

end Strictness
