import Strictness.Language.Syntax

namespace Strictness

namespace Term

/-- Simple typing contexts, indexed by De Bruijn level (nearest binder first). -/
abbrev Ctx := List SimpleTy

def lookup : Ctx → Nat → Option SimpleTy
  | [], _ => none
  | τ :: _, 0 => some τ
  | _ :: Γ, n + 1 => lookup Γ n

/-- Ordinary simple typing for the semantic term language.

`omega` and `err` are semantic terms and are polymorphically typable; they
are not source-language typing rules.
-/
inductive HasType : Ctx → Term → SimpleTy → Prop where
  | var {Γ τ i} : lookup Γ i = some τ → HasType Γ (.var i) τ
  | int {Γ n} : HasType Γ (.int n) .int
  | lam {Γ σ τ body} :
      HasType (σ :: Γ) body τ →
      HasType Γ (.lam body) (.arrow σ τ)
  | app {Γ σ τ e₁ e₂} :
      HasType Γ e₁ (.arrow σ τ) →
      HasType Γ e₂ σ →
      HasType Γ (.app e₁ e₂) τ
  | pair {Γ σ τ e₁ e₂} :
      HasType Γ e₁ σ →
      HasType Γ e₂ τ →
      HasType Γ (.pair e₁ e₂) (.prod σ τ)
  | projLeft {Γ σ τ e} :
      HasType Γ e (.prod σ τ) →
      HasType Γ (.proj true e) σ
  | projRight {Γ σ τ e} :
      HasType Γ e (.prod σ τ) →
      HasType Γ (.proj false e) τ
  | op (o : PrimOp) {Γ e₁ e₂} :
      HasType Γ e₁ .int →
      HasType Γ e₂ .int →
      HasType Γ (.op o e₁ e₂) .int
  | ite {Γ τ e₀ e₁ e₂} :
      HasType Γ e₀ .int →
      HasType Γ e₁ τ →
      HasType Γ e₂ τ →
      HasType Γ (.ite e₀ e₁ e₂) τ
  | letE {Γ σ τ e₁ e₂} :
      HasType Γ e₁ σ →
      HasType (σ :: Γ) e₂ τ →
      HasType Γ (.letE e₁ e₂) τ
  | fix {Γ τ body} :
      HasType (τ :: Γ) body τ →
      HasType Γ (.fix body) τ
  | omega {Γ τ} : HasType Γ .omega τ
  | err {Γ τ} : HasType Γ .err τ

abbrev ClosedTyped (τ : SimpleTy) (e : Term) : Prop :=
  Term.Closed e ∧ HasType [] e τ

end Term

end Strictness
