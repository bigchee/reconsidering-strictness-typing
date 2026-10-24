import Strictness.Language.Erasure

namespace Strictness

open Usage
open Term

/-- Declarative type assignment. The premises are the local usage
inequalities, structural subtyping, and recursive laziness conditions of
the paper. Context composition is pointwise on De Bruijn bindings. -/
inductive Typing : Env → Term → Ty → Prop where
  | const {Γ n u} :
      Env.IsLazy Γ →
      Typing (Env.scale u Γ) (.int n) (.int u)

  | var {Γ τ} :
      Env.IsLazy Γ →
      Typing (τ :: Env.scale τ.outer Γ) (.var 0) τ

  | varSkip {Γ τ σ i} :
      Typing Γ (.var i) τ →
      Ty.IsLazy σ →
      Typing (Ty.scale τ.outer σ :: Γ) (.var (i + 1)) τ

  | abs {Γ σ τ u e} :
      Typing (σ :: Γ) e τ →
      u ≤ τ.outer →
      Typing (Env.scale u Γ) (.lam e) (.arrow σ τ u)

  | app {Γ Γ₁ Γ₂ σ σ' τ u e₁ e₂} :
      Typing Γ₁ e₁ (.arrow σ τ u) →
      Typing Γ₂ e₂ σ' →
      Ty.Subtype σ' σ →
      u ≤ τ.outer →
      Env.plus Γ₁ (Env.scale u Γ₂) = some Γ →
      Typing Γ (.app e₁ e₂) τ

  | pair {Γ Γ₁ Γ₂ σ τ u e₁ e₂} :
      Typing Γ₁ e₁ σ →
      Typing Γ₂ e₂ τ →
      σ.outer ≤ (u ⊔ lazy) →
      τ.outer ≤ (u ⊔ lazy) →
      Env.plus Γ₁ Γ₂ = some Γ →
      Typing Γ (.pair e₁ e₂) (.prod σ τ u)

  | projLeft {Γ σ τ u e} :
      Typing Γ e (.prod σ τ u) →
      u ≤ σ.outer →
      Ty.IsLazy τ →
      Typing Γ (.proj true e) σ

  | projRight {Γ σ τ u e} :
      Typing Γ e (.prod σ τ u) →
      u ≤ τ.outer →
      Ty.IsLazy σ →
      Typing Γ (.proj false e) τ

  | op (o : PrimOp) {Γ Γ₁ Γ₂ u₁ u₂ u e₁ e₂} :
      Typing Γ₁ e₁ (.int u₁) →
      Typing Γ₂ e₂ (.int u₂) →
      u₁ ≤ u →
      u₂ ≤ u →
      Env.plus Γ₁ Γ₂ = some Γ →
      Typing Γ (.op o e₁ e₂) (.int u)

  | ite {Γ Γ₀ Γ₁ Γ₂ Γ₁₂ u τ₁ τ₂ τ e₀ e₁ e₂} :
      Typing Γ₀ e₀ (.int u) →
      Typing Γ₁ e₁ τ₁ →
      Typing Γ₂ e₂ τ₂ →
      Ty.Subtype τ₁ τ →
      Ty.Subtype τ₂ τ →
      u ≤ τ.outer →
      Env.cap Γ₁ Γ₂ = some Γ₁₂ →
      Env.plus Γ₀ Γ₁₂ = some Γ →
      Typing Γ (.ite e₀ e₁ e₂) τ

  | letE {Γ Γ₁ Γ₂ σ σ' τ e₁ e₂} :
      Typing Γ₁ e₁ σ →
      Typing (σ' :: Γ₂) e₂ τ →
      Ty.Subtype σ σ' →
      Env.plus Γ₁ Γ₂ = some Γ →
      Typing Γ (.letE e₁ e₂) τ

  | fix {Γ Δ σ τ body} :
      Typing (σ :: Γ) body τ →
      Ty.Subtype τ (Ty.raiseStrict σ) →
      Env.plus Γ (Env.scale (Usage.scale σ.outer top) Γ) = some Δ →
      Typing Δ (.fix body) τ

  | sub {Γ Γ' τ τ' e} :
      Typing Γ e τ →
      Env.Subtype Γ' Γ →
      Ty.Subtype τ τ' →
      Typing Γ' e τ'

/-- Erasing a `Typing` derivation gives ordinary simple typing. -/
theorem typing_erasure {Γ : Env} {e : Term} {τ : Ty}
    (h : Typing Γ e τ) :
    Term.HasType (Env.erase Γ) e τ.erase := by
  induction h with
  | const hLazy =>
      exact Term.HasType.int
  | var hLazy =>
      exact Term.HasType.var rfl
  | varSkip hVar hLazy ih =>
      cases ih with
      | var hLookup =>
          exact Term.HasType.var (by simpa [Ty.erase_scale] using hLookup)
  | abs hBody hu ih =>
      exact Term.HasType.lam (by simpa [Env.erase_scale] using ih)
  | @app Γ Γ₁ Γ₂ σ σ' τ u e₁ e₂ hFun hArg hSub hu hPlus ihFun ihArg =>
      have hEq := Env.plus_erase_of_some hPlus
      have hFun' := ihFun
      have hArg' : Term.HasType (Env.scale u Γ₂).erase e₂ σ'.erase := by
        simpa only [Env.erase_scale] using ihArg
      rw [← hEq.2] at hFun'
      rw [← hEq.1, ← hEq.2] at hArg'
      rw [Ty.subtype_erase hSub] at hArg'
      exact Term.HasType.app hFun' hArg'
  | pair h₁ h₂ hσ hτ hPlus ih₁ ih₂ =>
      have hEq := Env.plus_erase_of_some hPlus
      have h₁' := ih₁
      have h₂' := ih₂
      rw [← hEq.2] at h₁'
      rw [← hEq.1, ← hEq.2] at h₂'
      exact Term.HasType.pair h₁' h₂'
  | projLeft hPair hu hLazy ih =>
      exact Term.HasType.projLeft ih
  | projRight hPair hu hLazy ih =>
      exact Term.HasType.projRight ih
  | op o h₁ h₂ hu₁ hu₂ hPlus ih₁ ih₂ =>
      have hEq := Env.plus_erase_of_some hPlus
      have h₁' := ih₁
      have h₂' := ih₂
      rw [← hEq.2] at h₁'
      rw [← hEq.1, ← hEq.2] at h₂'
      exact Term.HasType.op o h₁' h₂'
  | ite h₀ h₁ h₂ hτ₁ hτ₂ hu hCap hPlus ih₀ ih₁ ih₂ =>
      have hCapEq := Env.cap_erase_of_some hCap
      have hPlusEq := Env.plus_erase_of_some hPlus
      have h₀' := ih₀
      have h₁' := ih₁
      have h₂' := ih₂
      rw [← hPlusEq.2] at h₀'
      rw [← hCapEq.2, ← hPlusEq.1, ← hPlusEq.2] at h₁'
      rw [← hCapEq.1, ← hCapEq.2, ← hPlusEq.1, ← hPlusEq.2] at h₂'
      rw [Ty.subtype_erase hτ₁] at h₁'
      rw [Ty.subtype_erase hτ₂] at h₂'
      exact Term.HasType.ite h₀' h₁' h₂'
  | letE hDef hBody hSub hPlus ihDef ihBody =>
      have hEq := Env.plus_erase_of_some hPlus
      have hDef' := ihDef
      have hBody' := ihBody
      rw [← hEq.2] at hDef'
      exact Term.HasType.letE hDef' (by
        simpa [Env.erase, Ty.subtype_erase hSub, ← hEq.1, ← hEq.2] using hBody')
  | @fix Γ Δ σ τ body hBody hSub hPlus ih =>
      have hContext : Env.erase Δ = Env.erase Γ :=
        (Env.plus_erase_of_some hPlus).2
      have hErase : τ.erase = σ.erase := by
        have h := Ty.subtype_erase hSub
        simpa only [Ty.erase_raiseStrict] using h
      have hBody' : Term.HasType (τ.erase :: Env.erase Γ) body τ.erase := by
        have h : Term.HasType (σ.erase :: Env.erase Γ) body τ.erase := ih
        rw [← hErase] at h
        exact h
      rw [hContext]
      exact Term.HasType.fix hBody'
  | sub hBody hEnv hTy ih =>
      rw [Env.subtype_erase hEnv, ← Ty.subtype_erase hTy]
      exact ih


/-- The non-head variable rule derives lambda x. lambda y. x. -/
example : ∃ τ, Typing [] (.lam (.lam (.var 1))) τ := by
  let α : Ty := .int lazy
  let β : Ty := .arrow α α lazy
  have hHead : Typing [α] (.var 0) α :=
    Typing.var (Γ := []) (τ := α) (by trivial)
  have hOuter : Typing [α, α] (.var 1) α := by
    simpa [α, Ty.scale, Usage.scale] using
      (Typing.varSkip (σ := α) hHead (by trivial))
  have hInner : Typing [α] (.lam (.var 1)) β := by
    simpa [α, β, Env.scale, Ty.scale, Usage.scale] using
      (Typing.abs (σ := α) (τ := α) (u := lazy) hOuter (by trivial))
  refine ⟨.arrow α β lazy, ?_⟩
  simpa [β, Env.scale] using
    (Typing.abs (σ := α) (τ := β) (u := lazy) hInner (by trivial))

end Strictness
