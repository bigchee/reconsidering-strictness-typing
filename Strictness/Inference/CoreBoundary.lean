import Strictness.Inference.RawBoundary
import Strictness.Language.Typing
import Strictness.Soundness.Fundamental

namespace Strictness.RawInference.CoreBoundary

open Raw

abbrev RTy := Raw.Ty
abbrev REnv := Raw.Env
abbrev UC := Raw.UseConstraints

/-- Boundary annotations are variables, not compound expressions or literals. -/
def VariableExpr : Raw.Expr → Prop
  | .var _ => True
  | _ => False

def VariableTy : RTy → Prop
  | .int u => VariableExpr u
  | .prod A B u =>
      VariableTy A ∧ VariableTy B ∧ VariableExpr u
  | .arrow A B u =>
      VariableTy A ∧ VariableTy B ∧ VariableExpr u

def VariableEnv (Γ : REnv) : Prop :=
  ∀ A ∈ Γ, VariableTy A

/-- Reuse structural composition, including equality constraints at arrows. -/
noncomputable abbrev composeEnv := Boundary.composeEnv

/-- Expand structural subtyping into annotation inequalities. -/
noncomputable def rawSub (A B : RTy) : Option UC :=
  Raw.Ty.subtypeConstraints A B

/--
Connect the computed result to the boundary exported to the parent.
Computed contexts may contain compound surface annotations.
All result-type and exported-boundary annotations are variables.
-/
def Finish
    (E : REnv) (B : RTy)
    (Δ : REnv) (T : RTy) (C : UC) : Prop :=
  VariableEnv Δ ∧ VariableTy B ∧ VariableTy T ∧
  ∃ CΓ Cτ,
    Raw.Env.subtypeConstraints Δ E = some CΓ ∧
    Raw.Ty.subtypeConstraints B T = some Cτ ∧
    C = CΓ ++ Cτ

structure Premise where
  ctx : REnv
  term : Term
  ty : RTy
  constraints : UC

def premiseConstraints (ps : List Premise) : UC :=
  ps.flatMap (fun P => P.constraints)

/--
One syntax-directed computation before its boundary comparison.
Local inequalities are those retained by Typing.
-/
inductive Rule : List Premise → Term → REnv → RTy → UC → Prop where
  | const {Γ u n} :
      VariableEnv Γ →
      VariableExpr u →
      Rule [] (.int n)
        (Raw.Env.scale u Γ) (.int u)
        Γ.lazyConstraints

  | var {Γ A} :
      VariableEnv Γ →
      VariableTy A →
      Rule [] (.var 0)
        (A :: Raw.Env.scale A.outer Γ) A
        Γ.lazyConstraints

  | varSkip {Γ A S i C} :
      VariableTy S →
      Rule [⟨Γ, .var i, A, C⟩] (.var (i + 1))
        (Raw.Ty.scale A.outer S :: Γ) A
        S.lazyConstraints

  | abs {Γ A B u e C} :
      VariableExpr u →
      Rule [⟨A :: Γ, e, B, C⟩] (.lam e)
        (Raw.Env.scale u Γ) (.arrow A B u)
        [⟨u, B.outer⟩]

  | app {Γ₁ Γ₂ A A' B u e₁ e₂ C₁ C₂ E Cplus Csub} :
      composeEnv .plus Γ₁ (Raw.Env.scale u Γ₂) =
        some (E, Cplus) →
      rawSub A' A = some Csub →
      Rule
        [⟨Γ₁, e₁, .arrow A B u, C₁⟩,
         ⟨Γ₂, e₂, A', C₂⟩]
        (.app e₁ e₂) E B
        (Cplus ++ Csub ++ [⟨u, B.outer⟩])

  | pair {Γ₁ Γ₂ A B u e₁ e₂ C₁ C₂ E Cplus} :
      composeEnv .plus Γ₁ Γ₂ = some (E, Cplus) →
      Rule
        [⟨Γ₁, e₁, A, C₁⟩, ⟨Γ₂, e₂, B, C₂⟩]
        (.pair e₁ e₂) E (.prod A B u)
        (Cplus ++
          [⟨A.outer, .join u (.lit .lazy)⟩,
           ⟨B.outer, .join u (.lit .lazy)⟩])

  | projLeft {Γ A B u e C} :
      Rule [⟨Γ, e, .prod A B u, C⟩]
        (.proj true e) Γ A
        ([⟨u, A.outer⟩] ++ B.lazyConstraints)

  | projRight {Γ A B u e C} :
      Rule [⟨Γ, e, .prod A B u, C⟩]
        (.proj false e) Γ B
        ([⟨u, B.outer⟩] ++ A.lazyConstraints)

  | op (o : PrimOp) {Γ₁ Γ₂ u₁ u₂ u e₁ e₂ C₁ C₂ E Cplus} :
      composeEnv .plus Γ₁ Γ₂ = some (E, Cplus) →
      Rule
        [⟨Γ₁, e₁, .int u₁, C₁⟩,
         ⟨Γ₂, e₂, .int u₂, C₂⟩]
        (.op o e₁ e₂) E (.int u)
        (Cplus ++ [⟨u₁, u⟩, ⟨u₂, u⟩])

  | ite
      {Γ₀ Γ₁ Γ₂ Γ₁₂ u A B T e₀ e₁ e₂ C₀ C₁ C₂
       E Ccap Cplus CA CB} :
      VariableTy T →
      composeEnv .cap Γ₁ Γ₂ = some (Γ₁₂, Ccap) →
      composeEnv .plus Γ₀ Γ₁₂ = some (E, Cplus) →
      rawSub A T = some CA →
      rawSub B T = some CB →
      Rule
        [⟨Γ₀, e₀, .int u, C₀⟩,
         ⟨Γ₁, e₁, A, C₁⟩,
         ⟨Γ₂, e₂, B, C₂⟩]
        (.ite e₀ e₁ e₂) E T
        (Ccap ++ Cplus ++ CA ++ CB ++ [⟨u, T.outer⟩])

  | letE {Γ₁ Γ₂ A A' B e₁ e₂ C₁ C₂ E Cplus Csub} :
      composeEnv .plus Γ₁ Γ₂ = some (E, Cplus) →
      rawSub A A' = some Csub →
      Rule
        [⟨Γ₁, e₁, A, C₁⟩,
         ⟨A' :: Γ₂, e₂, B, C₂⟩]
        (.letE e₁ e₂) E B
        (Cplus ++ Csub)

  /-- Fix computation; Finish incorporates the context and result subsumption. -/
  | fix {Γ A B body C E Cplus Csub} :
      composeEnv .plus Γ
        (Raw.Env.scale (.scale A.outer (.lit .top)) Γ) =
          some (E, Cplus) →
      rawSub B A.raiseStrict = some Csub →
      Rule [⟨A :: Γ, body, B, C⟩] (.fix body) E B
        (Cplus ++ Csub)

/--
Each term constructor computes a result and exports a variable boundary.
Subsumption is included in Finish rather than a recursive Sub constructor.
-/
inductive Derives : REnv → Term → RTy → UC → Prop where
  | node {ps e E B C₀ Δ T Cb} :
      Rule ps e E B C₀ →
      (∀ P ∈ ps, Derives P.ctx P.term P.ty P.constraints) →
      Finish E B Δ T Cb →
      Derives Δ e T (premiseConstraints ps ++ C₀ ++ Cb)

/-- Every generated derivation exports variable-annotated boundaries. -/
theorem Derives.boundary_variables
    {Γ : REnv} {e : Term} {T : RTy} {C : UC}
    (d : Derives Γ e T C) :
    VariableEnv Γ ∧ VariableTy T := by
  cases d with
  | node hRule hPremises hFinish =>
      exact ⟨hFinish.1, hFinish.2.2.1⟩

/-- Variable annotations are also atoms in the symbolic annotation syntax. -/
theorem variableExpr_isAtom
    {p : Raw.Expr} (hp : VariableExpr p) :
    p.IsAtom := by
  cases p <;> simp_all [VariableExpr, Raw.Expr.IsAtom]

theorem variableTy_allAtoms
    {A : RTy} (hA : VariableTy A) :
    A.AllAtoms := by
  induction A with
  | int u =>
      exact variableExpr_isAtom hA
  | prod A B u ihA ihB =>
      exact ⟨ihA hA.1, ihB hA.2.1,
        variableExpr_isAtom hA.2.2⟩
  | arrow A B u ihA ihB =>
      exact ⟨ihA hA.1, ihB hA.2.1,
        variableExpr_isAtom hA.2.2⟩

theorem variableEnv_allAtoms
    {Γ : REnv} (hΓ : VariableEnv Γ) :
    Γ.AllAtoms := by
  intro A hMem
  exact variableTy_allAtoms (hΓ A hMem)

/-- Satisfying structural subtype constraints gives concrete subtyping. -/
theorem rawSub_sound
    {ν : Raw.Valuation} {A B : RTy} {C : UC}
    (hSub : rawSub A B = some C)
    (hSat : C.Satisfies ν) :
    Strictness.Ty.Subtype (A.eval ν) (B.eval ν) := by
  exact (Raw.Ty.eval_subtypeConstraints hSub).mp hSat

/-- Structural comparison between variable types has dual-definite form. -/
theorem rawSub_dual
    {A B : RTy} {C : UC}
    (hA : VariableTy A)
    (hB : VariableTy B)
    (hSub : rawSub A B = some C) :
    C.DualDefinite := by
  exact Raw.Ty.subtypeConstraints_dualDefinite
    (variableTy_allAtoms hA)
    (variableTy_allAtoms hB)
    hSub

/-- Finish evaluates to precisely the comparisons required by Typing.sub. -/
theorem finish_bounds
    {ν : Raw.Valuation}
    {E Δ : REnv} {B T : RTy} {C : UC}
    (hFinish : Finish E B Δ T C)
    (hSat : C.Satisfies ν) :
    Strictness.Env.Subtype (Δ.eval ν) (E.eval ν) ∧
    Strictness.Ty.Subtype (B.eval ν) (T.eval ν) := by
  rcases hFinish with ⟨_, _, _, CΓ, Cτ, hΓ, hτ, hC⟩
  subst C
  rcases Raw.UseConstraints.satisfies_append.mp hSat with
    ⟨hSatΓ, hSatτ⟩
  exact ⟨
    (Raw.Env.eval_subtypeConstraints hΓ).mp hSatΓ,
    (Raw.Ty.eval_subtypeConstraints hτ).mp hSatτ⟩

/-- A computed Typing judgment can be exported through Finish. -/
theorem finish_typing
    {ν : Raw.Valuation}
    {E Δ : REnv} {B T : RTy} {C : UC} {e : Term}
    (hCore : Typing (E.eval ν) e (B.eval ν))
    (hFinish : Finish E B Δ T C)
    (hSat : C.Satisfies ν) :
    Typing (Δ.eval ν) e (T.eval ν) := by
  obtain ⟨hEnv, hTy⟩ := finish_bounds hFinish hSat
  exact Typing.sub hCore hEnv hTy

/-- Structural subtyping is antisymmetric. -/
theorem subtype_antisymm
    {A B : Strictness.Ty}
    (hAB : Strictness.Ty.Subtype A B)
    (hBA : Strictness.Ty.Subtype B A) :
    A = B := by
  induction hAB with
  | int hu =>
      cases hBA with
      | int hv =>
          exact congrArg Strictness.Ty.int
            (Usage.le_antisymm hu hv)
  | prod hA hB hu ihA ihB =>
      cases hBA with
      | prod hA' hB' hv =>
          cases ihA hA'
          cases ihB hB'
          cases Usage.le_antisymm hu hv
          rfl
  | arrow hA hB hu ihA ihB =>
      cases hBA with
      | arrow hA' hB' hv =>
          cases ihA hA'
          cases ihB hB'
          cases Usage.le_antisymm hu hv
          rfl

/-- Bidirectional subtype constraints enforce equality after evaluation. -/
theorem equalTypes_sound
    {ν : Raw.Valuation} {A B : RTy} {C : UC}
    (hEqual : Boundary.equalTypes A B = some C)
    (hSat : C.Satisfies ν) :
    A.eval ν = B.eval ν := by
  cases hAB : Raw.Ty.subtypeConstraints A B with
  | none =>
      simp [Boundary.equalTypes, hAB] at hEqual
  | some CAB =>
      cases hBA : Raw.Ty.subtypeConstraints B A with
      | none =>
          simp [Boundary.equalTypes, hAB, hBA] at hEqual
      | some CBA =>
          have hC : C = CAB ++ CBA := by
            simpa [Boundary.equalTypes, hAB, hBA] using hEqual.symm
          subst C
          obtain ⟨hSatAB, hSatBA⟩ :=
            Raw.UseConstraints.satisfies_append.mp hSat
          exact subtype_antisymm
            ((Raw.Ty.eval_subtypeConstraints hAB).mp hSatAB)
            ((Raw.Ty.eval_subtypeConstraints hBA).mp hSatBA)

/-- Raw composition evaluates to the corresponding concrete type operation. -/
theorem composeTy_sound
    {ν : Raw.Valuation}
    (op : Boundary.CombineOp)
    {A B D : RTy} {C : UC}
    (hCompose : Boundary.composeTy op A B = some (D, C))
    (hSat : C.Satisfies ν) :
    Strictness.Ty.combine op.usage
      (A.eval ν) (B.eval ν) = some (D.eval ν) := by
  induction A generalizing B D C with
  | int u =>
      cases B with
      | int v =>
          have hEq :
              D = .int (op.expr u v) ∧ C = [] := by
            simpa [Boundary.composeTy] using hCompose.symm
          rcases hEq with ⟨rfl, rfl⟩
          cases op <;>
            rfl
      | prod A B v =>
          simp [Boundary.composeTy] at hCompose
      | arrow A B v =>
          simp [Boundary.composeTy] at hCompose

  | prod A₁ A₂ u ih₁ ih₂ =>
      cases B with
      | int v =>
          simp [Boundary.composeTy] at hCompose
      | arrow B₁ B₂ v =>
          simp [Boundary.composeTy] at hCompose
      | prod B₁ B₂ v =>
          cases h₁ : Boundary.composeTy op A₁ B₁ with
          | none =>
              simp [Boundary.composeTy, h₁] at hCompose
          | some result₁ =>
              rcases result₁ with ⟨D₁, C₁⟩
              cases h₂ : Boundary.composeTy op A₂ B₂ with
              | none =>
                  simp [Boundary.composeTy, h₁, h₂] at hCompose
              | some result₂ =>
                  rcases result₂ with ⟨D₂, C₂⟩
                  have hEq :
                      D = .prod D₁ D₂ (op.expr u v) ∧
                      C = C₁ ++ C₂ := by
                    simpa [Boundary.composeTy, h₁, h₂]
                      using hCompose.symm
                  rcases hEq with ⟨rfl, rfl⟩
                  obtain ⟨hSat₁, hSat₂⟩ :=
                    Raw.UseConstraints.satisfies_append.mp hSat
                  have hEval₁ := ih₁ h₁ hSat₁
                  have hEval₂ := ih₂ h₂ hSat₂
                  cases op <;>
                    simp [Strictness.Ty.combine, Raw.Ty.eval,
                      Boundary.CombineOp.expr,
                      Boundary.CombineOp.usage,
                      Raw.Expr.eval] at hEval₁ hEval₂ ⊢ <;>
                    rw [hEval₁, hEval₂] <;>
                    rfl

  | arrow A₁ A₂ u =>
      cases B with
      | int v =>
          simp [Boundary.composeTy] at hCompose
      | prod B₁ B₂ v =>
          simp [Boundary.composeTy] at hCompose
      | arrow B₁ B₂ v =>
          cases h₁ : Boundary.equalTypes A₁ B₁ with
          | none =>
              simp [Boundary.composeTy, h₁] at hCompose
          | some C₁ =>
              cases h₂ : Boundary.equalTypes A₂ B₂ with
              | none =>
                  simp [Boundary.composeTy, h₁, h₂] at hCompose
              | some C₂ =>
                  have hEq :
                      D = .arrow A₁ A₂ (op.expr u v) ∧
                      C = C₁ ++ C₂ := by
                    simpa [Boundary.composeTy, h₁, h₂]
                      using hCompose.symm
                  rcases hEq with ⟨rfl, rfl⟩
                  obtain ⟨hSat₁, hSat₂⟩ :=
                    Raw.UseConstraints.satisfies_append.mp hSat
                  have hDom := equalTypes_sound h₁ hSat₁
                  have hCod := equalTypes_sound h₂ hSat₂
                  cases op <;>
                    simp [Strictness.Ty.combine, Raw.Ty.eval,
                      Boundary.CombineOp.expr,
                      Boundary.CombineOp.usage,
                      Raw.Expr.eval, hDom, hCod]

/-- Raw environment composition evaluates to concrete environment composition. -/
theorem composeEnv_sound
    {ν : Raw.Valuation}
    (op : Boundary.CombineOp)
    {Γ Δ E : REnv} {C : UC}
    (hCompose : composeEnv op Γ Δ = some (E, C))
    (hSat : C.Satisfies ν) :
    Strictness.Env.combine op.usage
      (Γ.eval ν) (Δ.eval ν) = some (E.eval ν) := by
  induction Γ generalizing Δ E C with
  | nil =>
      cases Δ with
      | nil =>
          have hEq : E = [] ∧ C = [] := by
            simpa [composeEnv, Boundary.composeEnv] using hCompose.symm
          rcases hEq with ⟨rfl, rfl⟩
          rfl
      | cons B Δ =>
          simp [composeEnv, Boundary.composeEnv] at hCompose

  | cons A Γ ih =>
      cases Δ with
      | nil =>
          simp [composeEnv, Boundary.composeEnv] at hCompose
      | cons B Δ =>
          cases hHead : Boundary.composeTy op A B with
          | none =>
              simp [composeEnv, Boundary.composeEnv, hHead] at hCompose
          | some headResult =>
              rcases headResult with ⟨D, CHead⟩
              cases hTail : Boundary.composeEnv op Γ Δ with
              | none =>
                  simp [composeEnv, Boundary.composeEnv, hHead, hTail]
                    at hCompose
              | some tailResult =>
                  rcases tailResult with ⟨Ξ, CTail⟩
                  have hEq :
                      E = D :: Ξ ∧ C = CHead ++ CTail := by
                    simpa [composeEnv, Boundary.composeEnv, hHead, hTail]
                      using hCompose.symm
                  rcases hEq with ⟨rfl, rfl⟩
                  obtain ⟨hSatHead, hSatTail⟩ :=
                    Raw.UseConstraints.satisfies_append.mp hSat
                  have hEvalHead := composeTy_sound op hHead hSatHead
                  have hEvalTail :=
                    ih (by simpa only [composeEnv] using hTail) hSatTail
                  simp only [Raw.Env.eval, Strictness.Env.combine]
                  rw [hEvalHead, hEvalTail]
                  rfl

theorem composeEnv_plus_sound
    {ν : Raw.Valuation} {Γ Δ E : REnv} {C : UC}
    (hCompose : composeEnv .plus Γ Δ = some (E, C))
    (hSat : C.Satisfies ν) :
    Strictness.Env.plus (Γ.eval ν) (Δ.eval ν) =
      some (E.eval ν) := by
  exact composeEnv_sound .plus hCompose hSat

theorem composeEnv_cap_sound
    {ν : Raw.Valuation} {Γ Δ E : REnv} {C : UC}
    (hCompose : composeEnv .cap Γ Δ = some (E, C))
    (hSat : C.Satisfies ν) :
    Strictness.Env.cap (Γ.eval ν) (Δ.eval ν) =
      some (E.eval ν) := by
  exact composeEnv_sound .cap hCompose hSat

/-- Split the constraints accumulated by a generated node. -/
theorem node_constraints_satisfied
    {ν : Raw.Valuation} {ps : List Premise} {C₀ Cb : UC}
    (hSat :
      (premiseConstraints ps ++ C₀ ++ Cb).Satisfies ν) :
    (premiseConstraints ps).Satisfies ν ∧
    C₀.Satisfies ν ∧ Cb.Satisfies ν := by
  obtain ⟨hPrevious, hBoundary⟩ :=
    Raw.UseConstraints.satisfies_append.mp hSat
  obtain ⟨hPremises, hLocal⟩ :=
    Raw.UseConstraints.satisfies_append.mp hPrevious
  exact ⟨hPremises, hLocal, hBoundary⟩

/-- Every child's constraints are included in the premise constraint list. -/
theorem premise_constraints_satisfied
    {ν : Raw.Valuation} {ps : List Premise} {P : Premise}
    (hSat : (premiseConstraints ps).Satisfies ν)
    (hMem : P ∈ ps) :
    P.constraints.Satisfies ν := by
  intro c hc
  apply hSat c
  change c ∈ ps.flatMap (fun Q => Q.constraints)
  exact List.mem_flatMap.mpr ⟨P, hMem, hc⟩

/-- Every satisfied generated rule gives its computed Typing judgment. -/
theorem rule_typing
    {ν : Raw.Valuation}
    {ps : List Premise} {e : Term}
    {E : REnv} {B : RTy} {C : UC}
    (r : Rule ps e E B C)
    (hPremises :
      ∀ P ∈ ps, Typing (P.ctx.eval ν) P.term (P.ty.eval ν))
    (hSat : C.Satisfies ν) :
    Typing (E.eval ν) e (B.eval ν) := by
  cases r with
  | const hΓ hu =>
      have hLazy := (Raw.Env.eval_lazyConstraints ν _).mp hSat
      simpa only [Raw.Env.eval_scale, Raw.Ty.eval] using
        (Typing.const (n := _) (u := _) hLazy)

  | var hΓ hA =>
      have hLazy := (Raw.Env.eval_lazyConstraints ν _).mp hSat
      simpa only [Raw.Env.eval, Raw.Env.eval_scale,
        Raw.Ty.eval_outer] using
        (Typing.var hLazy)

  | varSkip hS =>
      have hChild := hPremises _ (List.mem_singleton_self _)
      have hLazy := (Raw.Ty.eval_lazyConstraints ν _).mp hSat
      simpa only [Raw.Env.eval, Raw.Ty.eval_scale,
        Raw.Ty.eval_outer] using
        (Typing.varSkip hChild hLazy)

  | @abs Γ A B u e C hu =>
      have hChild := hPremises _ (List.mem_singleton_self _)
      have hBound : u.eval ν ≤ (B.eval ν).outer := by
        simpa only [Raw.UseConstraint.Holds, Raw.Ty.eval_outer] using
          hSat ⟨u, B.outer⟩ (by simp)
      simpa only [Raw.Env.eval_scale, Raw.Ty.eval] using
        (Typing.abs hChild hBound)

  | @app Γ₁ Γ₂ A A' B u e₁ e₂ C₁ C₂ E Cplus Csub
      hCompose hSub =>
      have hFun := hPremises
        ⟨Γ₁, e₁, .arrow A B u, C₁⟩ (by simp)
      have hArg := hPremises
        ⟨Γ₂, e₂, A', C₂⟩ (by simp)
      obtain ⟨hPrevious, hBounds⟩ :=
        Raw.UseConstraints.satisfies_append.mp hSat
      obtain ⟨hPlusSat, hSubSat⟩ :=
        Raw.UseConstraints.satisfies_append.mp hPrevious
      have hPlus := composeEnv_plus_sound hCompose hPlusSat
      have hSubtype := rawSub_sound hSub hSubSat
      have hBound : u.eval ν ≤ (B.eval ν).outer := by
        simpa only [Raw.UseConstraint.Holds, Raw.Ty.eval_outer] using
          hBounds ⟨u, B.outer⟩ (by simp)
      rw [Raw.Env.eval_scale] at hPlus
      exact Typing.app hFun hArg hSubtype hBound hPlus

  | @pair Γ₁ Γ₂ A B u e₁ e₂ C₁ C₂ E Cplus hCompose =>
      have hLeft := hPremises ⟨Γ₁, e₁, A, C₁⟩ (by simp)
      have hRight := hPremises ⟨Γ₂, e₂, B, C₂⟩ (by simp)
      obtain ⟨hPlusSat, hBounds⟩ :=
        Raw.UseConstraints.satisfies_append.mp hSat
      have hPlus := composeEnv_plus_sound hCompose hPlusSat
      have hLeftBound :
          (A.eval ν).outer ≤ u.eval ν ⊔ Usage.lazy := by
        simpa only [Raw.UseConstraint.Holds, Raw.Ty.eval_outer,
          Raw.Expr.eval] using
          hBounds ⟨A.outer, .join u (.lit .lazy)⟩ (by simp)
      have hRightBound :
          (B.eval ν).outer ≤ u.eval ν ⊔ Usage.lazy := by
        simpa only [Raw.UseConstraint.Holds, Raw.Ty.eval_outer,
          Raw.Expr.eval] using
          hBounds ⟨B.outer, .join u (.lit .lazy)⟩ (by simp)
      exact Typing.pair
        hLeft hRight hLeftBound hRightBound hPlus

  | @projLeft Γ A B u e C =>
      rename_i A
      have hChild := hPremises _ (List.mem_singleton_self _)
      obtain ⟨hBounds, hLazySat⟩ :=
        Raw.UseConstraints.satisfies_append.mp hSat
      have hBound : u.eval ν ≤ (A.eval ν).outer := by
        simpa only [Raw.UseConstraint.Holds, Raw.Ty.eval_outer] using
          hBounds ⟨u, A.outer⟩ (by simp)
      have hLazy := (Raw.Ty.eval_lazyConstraints ν B).mp hLazySat
      exact Typing.projLeft hChild hBound hLazy

  | @projRight Γ A B u e C =>
      have hChild := hPremises _ (List.mem_singleton_self _)
      obtain ⟨hBounds, hLazySat⟩ :=
        Raw.UseConstraints.satisfies_append.mp hSat
      have hBound : u.eval ν ≤ (B.eval ν).outer := by
        simpa only [Raw.UseConstraint.Holds, Raw.Ty.eval_outer] using
          hBounds ⟨u, B.outer⟩ (by simp)
      have hLazy := (Raw.Ty.eval_lazyConstraints ν A).mp hLazySat
      exact Typing.projRight hChild hBound hLazy

  | @op o Γ₁ Γ₂ u₁ u₂ u e₁ e₂ C₁ C₂ E Cplus hCompose =>
      have hLeft := hPremises
        ⟨Γ₁, e₁, .int u₁, C₁⟩ (by simp)
      have hRight := hPremises
        ⟨Γ₂, e₂, .int u₂, C₂⟩ (by simp)
      obtain ⟨hPlusSat, hBounds⟩ :=
        Raw.UseConstraints.satisfies_append.mp hSat
      have hPlus := composeEnv_plus_sound hCompose hPlusSat
      have hBound₁ : u₁.eval ν ≤ u.eval ν :=
        hBounds ⟨u₁, u⟩ (by simp)
      have hBound₂ : u₂.eval ν ≤ u.eval ν :=
        hBounds ⟨u₂, u⟩ (by simp)
      exact Typing.op o hLeft hRight hBound₁ hBound₂ hPlus

  | @ite Γ₀ Γ₁ Γ₂ Γ₁₂ u A B T e₀ e₁ e₂ C₀ C₁ C₂
      E Ccap Cplus CA CB hT hCap hPlus hSubA hSubB =>
      rename_i T
      have hCond := hPremises
        ⟨Γ₀, e₀, .int u, C₀⟩ (by simp)
      have hThen := hPremises
        ⟨Γ₁, e₁, A, C₁⟩ (by simp)
      have hElse := hPremises
        ⟨Γ₂, e₂, B, C₂⟩ (by simp)
      obtain ⟨hPrevious₃, hBounds⟩ :=
        Raw.UseConstraints.satisfies_append.mp hSat
      obtain ⟨hPrevious₂, hSubBSat⟩ :=
        Raw.UseConstraints.satisfies_append.mp hPrevious₃
      obtain ⟨hPrevious₁, hSubASat⟩ :=
        Raw.UseConstraints.satisfies_append.mp hPrevious₂
      obtain ⟨hCapSat, hPlusSat⟩ :=
        Raw.UseConstraints.satisfies_append.mp hPrevious₁
      have hCapEval := composeEnv_cap_sound hCap hCapSat
      have hPlusEval := composeEnv_plus_sound hPlus hPlusSat
      have hSubtypeA := rawSub_sound hSubA hSubASat
      have hSubtypeB := rawSub_sound hSubB hSubBSat
      have hBound : u.eval ν ≤ (T.eval ν).outer := by
        simpa only [Raw.UseConstraint.Holds, Raw.Ty.eval_outer] using
          hBounds ⟨u, T.outer⟩ (by simp)
      exact Typing.ite hCond hThen hElse
        hSubtypeA hSubtypeB hBound hCapEval hPlusEval

  | @letE Γ₁ Γ₂ A A' B e₁ e₂ C₁ C₂ E Cplus Csub
      hCompose hSub =>
      have hDef := hPremises
        ⟨Γ₁, e₁, A, C₁⟩ (by simp)
      have hBody := hPremises
        ⟨A' :: Γ₂, e₂, B, C₂⟩ (by simp)
      obtain ⟨hPlusSat, hSubSat⟩ :=
        Raw.UseConstraints.satisfies_append.mp hSat
      have hPlus := composeEnv_plus_sound hCompose hPlusSat
      have hSubtype := rawSub_sound hSub hSubSat
      exact Typing.letE hDef hBody hSubtype hPlus

  | @fix Γ A B body C E Cplus Csub hCompose hSub =>
      have hBody := hPremises _ (List.mem_singleton_self _)
      obtain ⟨hPlusSat, hSubSat⟩ :=
        Raw.UseConstraints.satisfies_append.mp hSat
      have hPlus := composeEnv_plus_sound hCompose hPlusSat
      have hSubtype := rawSub_sound hSub hSubSat
      rw [Raw.Ty.eval_raiseStrict] at hSubtype
      simp only [Raw.Env.eval_scale, Raw.Expr.eval, Raw.Ty.eval_outer] at hPlus
      exact Typing.fix hBody hSubtype hPlus

/-- Every satisfied generated derivation elaborates to Typing. -/
theorem Derives.toTyping
    {Γ : REnv} {e : Term} {T : RTy} {C : UC}
    (d : Derives Γ e T C)
    {ν : Raw.Valuation}
    (hSat : C.Satisfies ν) :
    Typing (Γ.eval ν) e (T.eval ν) := by
  induction d with
  | node hRule hChildren hFinish ih =>
      obtain ⟨hPremisesSat, hLocalSat, hBoundarySat⟩ :=
        node_constraints_satisfied hSat
      have hComputed :=
        rule_typing hRule
          (fun P hMem =>
            ih P hMem
              (premise_constraints_satisfied hPremisesSat hMem))
          hLocalSat
      exact finish_typing hComputed hFinish hBoundarySat

/-- The generated system inherits the established fundamental lemma. -/
theorem Derives.fundamental
    {Γ : REnv} {e : Term} {T : RTy} {C : UC}
    (d : Derives Γ e T C)
    {ν : Raw.Valuation}
    (hSat : C.Satisfies ν) :
    ∀ ρ : Substitution,
      Valid (Γ.eval ν) ρ →
      V (T.eval ν) (Substitution.apply ρ e) ∧
      (SatisfiesD (Γ.eval ν) ρ →
        D (T.eval ν) (Substitution.apply ρ e)) := by
  exact Strictness.fundamental (d.toTyping hSat)

end Strictness.RawInference.CoreBoundary
