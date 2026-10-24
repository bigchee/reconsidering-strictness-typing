import Strictness.Inference.Construction.BasicRules
import Strictness.Inference.Construction.BinaryRules
import Strictness.Inference.Construction.ControlRules

/-!
Declarative typing and constraint generation describe the same judgments.

`typing_buildable` assembles the rule-specific constructions by induction on
typing. `typing_complete` exports the generated witness, and
`typing_correspondence` gives the final equivalence. The dual-definite variant
also certifies the syntactic form required of the generated constraints.
-/

namespace Strictness.RawInference.CoreBoundary

open Raw

/-- Every Typing derivation, including fix, has a supported realization. -/
theorem typing_buildable
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty}
    (h : Typing Γ e τ) :
    Buildable Γ e τ := by
  induction h with
  | const hLazy => exact buildable_const hLazy
  | var hLazy => exact buildable_var hLazy
  | varSkip hVar hLazy ih => exact buildable_varSkip ih hLazy
  | abs hBody hu ih => exact buildable_abs ih hu
  | app hFun hArg hSub hu hPlus ihFun ihArg =>
      exact buildable_app ihFun ihArg hSub hu hPlus
  | pair hLeft hRight hσ hτ hPlus ihLeft ihRight =>
      exact buildable_pair ihLeft ihRight hσ hτ hPlus
  | projLeft hPair hu hLazy ih => exact buildable_proj true ih hu hLazy
  | projRight hPair hu hLazy ih => exact buildable_proj false ih hu hLazy
  | op o hLeft hRight hu₁ hu₂ hPlus ihLeft ihRight =>
      exact buildable_op ihLeft ihRight hu₁ hu₂ hPlus
  | ite hCond hThen hElse hSubThen hSubElse hu hCap hPlus
      ihCond ihThen ihElse =>
      exact buildable_ite ihCond ihThen ihElse hSubThen hSubElse hu hCap hPlus
  | letE hDef hBody hSub hPlus ihDef ihBody =>
      exact buildable_let ihDef ihBody hSub hPlus
  | fix hBody hSub hPlus ih => exact buildable_fix ih hSub hPlus
  | sub hBody hEnv hTy ih => exact buildable_sub ih hEnv hTy

/-- Existential completeness of the generator, including fix terms. -/
theorem typing_complete
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty}
    (h : Typing Γ e τ) :
    ∃ (G : REnv) (T : RTy) (C : UC) (ν : Raw.Valuation),
      Derives G e T C ∧
      C.Satisfies ν ∧
      Raw.Env.eval ν G = Γ ∧
      T.eval ν = τ := by
  obtain ⟨w⟩ :=
    typing_buildable h 0 (fun _ => Usage.unknown)
  exact ⟨w.ctx, w.ty, w.constraints, w.valuation,
    w.supported.toDerives, w.satisfies, w.ctx_eval, w.ty_eval⟩

/-- Both systems represent the same concrete judgments. -/
theorem typing_correspondence
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty} :
    Typing Γ e τ ↔
      ∃ (G : REnv) (T : RTy) (C : UC) (ν : Raw.Valuation),
        Derives G e T C ∧
        C.Satisfies ν ∧
        Raw.Env.eval ν G = Γ ∧
        T.eval ν = τ := by
  constructor
  · intro h
    exact typing_complete h
  · rintro ⟨G, T, C, ν, hDerives, hSat, hΓ, hτ⟩
    have hCore := hDerives.toTyping hSat
    simpa only [hΓ, hτ] using hCore

/-- Full correspondence with the Algorithm-D shape certified in the witness. -/
theorem typing_correspondence_dualDefinite
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty} :
    Typing Γ e τ ↔
      ∃ (G : REnv) (T : RTy) (C : UC) (ν : Raw.Valuation),
        Derives G e T C ∧ C.DualDefinite ∧
        C.Satisfies ν ∧ Raw.Env.eval ν G = Γ ∧ T.eval ν = τ := by
  constructor
  · intro h
    obtain ⟨G, T, C, ν, hd, hs, hG, hT⟩ := typing_complete h
    exact ⟨G, T, C, ν, hd, hd.constraints_dualDefinite, hs, hG, hT⟩
  · rintro ⟨G, T, C, ν, hd, _, hs, hG, hT⟩
    simpa only [hG, hT] using hd.toTyping hs

end Strictness.RawInference.CoreBoundary
