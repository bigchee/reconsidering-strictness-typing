import Strictness.Inference.CoreBoundary

namespace Strictness.RawInference.CoreBoundary

open Raw

/-- Every left-hand side is a variable; every right-hand side is monotone. -/
def VariableDefinite (C : UC) : Prop :=
  ∀ c ∈ C, VariableExpr c.lhs ∧ c.rhs.Monotone

theorem variableDefinite_nil :
    VariableDefinite [] := by
  intro c hc
  simp at hc

theorem variableDefinite_append {C D : UC} :
    VariableDefinite (C ++ D) ↔
      VariableDefinite C ∧ VariableDefinite D := by
  constructor
  · intro h
    constructor
    · intro c hc
      exact h c (List.mem_append_left _ hc)
    · intro c hc
      exact h c (List.mem_append_right _ hc)
  · rintro ⟨hC, hD⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hC c hc
    · exact hD c hc

theorem variableDefinite_singleton {p q : Raw.Expr} :
    VariableDefinite [⟨p, q⟩] ↔
      VariableExpr p ∧ q.Monotone := by
  constructor
  · intro h
    exact h ⟨p, q⟩ (by simp)
  · intro h c hc
    simp only [List.mem_singleton] at hc
    subst c
    exact h

theorem variable_inequality
    {p q : Raw.Expr} (hp : VariableExpr p) :
    VariableDefinite [⟨p, q⟩] := by
  exact variableDefinite_singleton.mpr
    ⟨hp, Raw.Expr.monotone q⟩

/--
Compound expressions are allowed through products and at arrow roots.
Inside arrows, annotations must remain variables.
-/
def VariableSurface : RTy → Prop
  | .int _ => True
  | .prod A B _ => VariableSurface A ∧ VariableSurface B
  | .arrow A B _ => VariableTy A ∧ VariableTy B

def VariableSurfaceEnv (Γ : REnv) : Prop :=
  ∀ A ∈ Γ, VariableSurface A

theorem variableTy_surface
    {A : RTy} (hA : VariableTy A) :
    VariableSurface A := by
  induction A with
  | int u =>
      trivial
  | prod A B u ihA ihB =>
      exact ⟨ihA hA.1, ihB hA.2.1⟩
  | arrow A B u =>
      exact ⟨hA.1, hA.2.1⟩

theorem variableSurface_raiseStrict
    {A : RTy} (hA : VariableTy A) :
    VariableSurface A.raiseStrict := by
  cases A with
  | int u => trivial
  | prod A B u => exact ⟨variableTy_surface hA.1, variableTy_surface hA.2.1⟩
  | arrow A B u => exact ⟨hA.1, hA.2.1⟩

theorem variableSurface_scale
    (p : Raw.Expr) {A : RTy}
    (hA : VariableSurface A) :
    VariableSurface (Raw.Ty.scale p A) := by
  induction A with
  | int u =>
      trivial
  | prod A B u ihA ihB =>
      exact ⟨ihA hA.1, ihB hA.2⟩
  | arrow A B u =>
      exact hA

/-- Subtyping from a variable boundary to a surface type has the required form. -/
private theorem subtypeFuel_variableDefinite
    {n : Nat} {A B : RTy} {C : UC}
    (hA : VariableTy A)
    (hB : VariableSurface B)
    (hC : Raw.Ty.subtypeConstraintsFuel n A B = some C) :
    VariableDefinite C := by
  induction n generalizing A B C with
  | zero =>
      simp [Raw.Ty.subtypeConstraintsFuel] at hC
  | succ n ih =>
      cases A with
      | int u =>
          cases B with
          | int v =>
              simp [Raw.Ty.subtypeConstraintsFuel] at hC
              subst C
              exact variable_inequality hA
          | prod _ _ _ =>
              simp [Raw.Ty.subtypeConstraintsFuel] at hC
          | arrow _ _ _ =>
              simp [Raw.Ty.subtypeConstraintsFuel] at hC

      | prod A₁ A₂ u =>
          cases B with
          | int _ =>
              simp [Raw.Ty.subtypeConstraintsFuel] at hC
          | arrow _ _ _ =>
              simp [Raw.Ty.subtypeConstraintsFuel] at hC
          | prod B₁ B₂ v =>
              cases h₁ : Raw.Ty.subtypeConstraintsFuel n A₁ B₁ with
              | none =>
                  simp [Raw.Ty.subtypeConstraintsFuel, h₁] at hC
              | some C₁ =>
                  cases h₂ : Raw.Ty.subtypeConstraintsFuel n A₂ B₂ with
                  | none =>
                      simp [Raw.Ty.subtypeConstraintsFuel, h₁, h₂] at hC
                  | some C₂ =>
                      simp [Raw.Ty.subtypeConstraintsFuel, h₁, h₂] at hC
                      subst C
                      exact variableDefinite_append.mpr
                        ⟨ih hA.1 hB.1 h₁,
                         variableDefinite_append.mpr
                           ⟨ih hA.2.1 hB.2 h₂,
                            variable_inequality
                              (q := v) hA.2.2⟩⟩

      | arrow A₁ A₂ u =>
          cases B with
          | int _ =>
              simp [Raw.Ty.subtypeConstraintsFuel] at hC
          | prod _ _ _ =>
              simp [Raw.Ty.subtypeConstraintsFuel] at hC
          | arrow B₁ B₂ v =>
              cases h₁ : Raw.Ty.subtypeConstraintsFuel n B₁ A₁ with
              | none =>
                  simp [Raw.Ty.subtypeConstraintsFuel, h₁] at hC
              | some C₁ =>
                  cases h₂ : Raw.Ty.subtypeConstraintsFuel n A₂ B₂ with
                  | none =>
                      simp [Raw.Ty.subtypeConstraintsFuel, h₁, h₂] at hC
                  | some C₂ =>
                      simp [Raw.Ty.subtypeConstraintsFuel, h₁, h₂] at hC
                      subst C
                      exact variableDefinite_append.mpr
                        ⟨ih hB.1 (variableTy_surface hA.1) h₁,
                         variableDefinite_append.mpr
                           ⟨ih hA.2.1 (variableTy_surface hB.2) h₂,
                            variable_inequality
                              (q := v) hA.2.2⟩⟩

theorem subtype_variableDefinite
    {A B : RTy} {C : UC}
    (hA : VariableTy A)
    (hB : VariableSurface B)
    (hC : Raw.Ty.subtypeConstraints A B = some C) :
    VariableDefinite C := by
  exact subtypeFuel_variableDefinite hA hB hC

theorem rawSub_variableDefinite
    {A B : RTy} {C : UC}
    (hA : VariableTy A)
    (hB : VariableTy B)
    (hSub : rawSub A B = some C) :
    VariableDefinite C := by
  exact subtype_variableDefinite hA (variableTy_surface hB) hSub

theorem lazyTy_variableDefinite
    {A : RTy} (hA : VariableTy A) :
    VariableDefinite A.lazyConstraints := by
  induction A with
  | int u =>
      exact variable_inequality hA
  | prod A B u ihA ihB =>
      change VariableDefinite
        ([⟨u, .lit .lazy⟩] ++ A.lazyConstraints ++ B.lazyConstraints)
      exact variableDefinite_append.mpr
        ⟨variableDefinite_append.mpr
          ⟨variable_inequality hA.2.2, ihA hA.1⟩,
         ihB hA.2.1⟩
  | arrow A B u =>
      exact variable_inequality hA.2.2

theorem variableEnv_surface
    {Γ : REnv} (hΓ : VariableEnv Γ) :
    VariableSurfaceEnv Γ := by
  intro A hMem
  exact variableTy_surface (hΓ A hMem)

theorem variableSurfaceEnv_scale
    (p : Raw.Expr) {Γ : REnv}
    (hΓ : VariableSurfaceEnv Γ) :
    VariableSurfaceEnv (Raw.Env.scale p Γ) := by
  induction Γ with
  | nil =>
      intro A hMem
      simp [Raw.Env.scale] at hMem
  | cons A Γ ih =>
      have hTail : VariableSurfaceEnv Γ := by
        intro B hMem
        exact hΓ B (List.mem_cons_of_mem _ hMem)
      intro B hMem
      change B ∈ Raw.Ty.scale p A :: Raw.Env.scale p Γ at hMem
      rcases List.mem_cons.mp hMem with hHead | hRest
      · subst B
        exact variableSurface_scale p (hΓ A (by simp))
      · exact ih hTail B hRest

theorem lazyEnv_variableDefinite
    {Γ : REnv} (hΓ : VariableEnv Γ) :
    VariableDefinite Γ.lazyConstraints := by
  induction Γ with
  | nil =>
      exact variableDefinite_nil
  | cons A Γ ih =>
      have hTail : VariableEnv Γ := by
        intro B hMem
        exact hΓ B (List.mem_cons_of_mem _ hMem)
      exact variableDefinite_append.mpr
        ⟨lazyTy_variableDefinite (hΓ A (by simp)), ih hTail⟩

theorem equalTypes_variableDefinite
    {A B : RTy} {C : UC}
    (hA : VariableTy A)
    (hB : VariableTy B)
    (hEqual : Boundary.equalTypes A B = some C) :
    VariableDefinite C := by
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
          exact variableDefinite_append.mpr
            ⟨subtype_variableDefinite hA (variableTy_surface hB) hAB,
             subtype_variableDefinite hB (variableTy_surface hA) hBA⟩

/-- Composition preserves the surface invariant and emits variable-left constraints. -/
theorem composeTy_surface_variableDefinite
    (op : Boundary.CombineOp)
    {A B D : RTy} {C : UC}
    (hA : VariableSurface A)
    (hB : VariableSurface B)
    (hCompose : Boundary.composeTy op A B = some (D, C)) :
    VariableSurface D ∧ VariableDefinite C := by
  induction A generalizing B D C with
  | int u =>
      cases B with
      | int v =>
          have hEq :
              D = .int (op.expr u v) ∧ C = [] := by
            simpa [Boundary.composeTy] using hCompose.symm
          rcases hEq with ⟨rfl, rfl⟩
          exact ⟨True.intro, variableDefinite_nil⟩
      | prod _ _ _ =>
          simp [Boundary.composeTy] at hCompose
      | arrow _ _ _ =>
          simp [Boundary.composeTy] at hCompose

  | prod A₁ A₂ u ih₁ ih₂ =>
      cases B with
      | int _ =>
          simp [Boundary.composeTy] at hCompose
      | arrow _ _ _ =>
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
                  obtain ⟨hD₁, hC₁⟩ := ih₁ hA.1 hB.1 h₁
                  obtain ⟨hD₂, hC₂⟩ := ih₂ hA.2 hB.2 h₂
                  exact ⟨⟨hD₁, hD₂⟩,
                    variableDefinite_append.mpr ⟨hC₁, hC₂⟩⟩

  | arrow A₁ A₂ u =>
      cases B with
      | int _ =>
          simp [Boundary.composeTy] at hCompose
      | prod _ _ _ =>
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
                  exact ⟨hA,
                    variableDefinite_append.mpr
                      ⟨equalTypes_variableDefinite hA.1 hB.1 h₁,
                       equalTypes_variableDefinite hA.2 hB.2 h₂⟩⟩

theorem composeEnv_surface_variableDefinite
    (op : Boundary.CombineOp)
    {Γ Δ E : REnv} {C : UC}
    (hΓ : VariableSurfaceEnv Γ)
    (hΔ : VariableSurfaceEnv Δ)
    (hCompose : composeEnv op Γ Δ = some (E, C)) :
    VariableSurfaceEnv E ∧ VariableDefinite C := by
  induction Γ generalizing Δ E C with
  | nil =>
      cases Δ with
      | nil =>
          have hEq : E = [] ∧ C = [] := by
            simpa [composeEnv, Boundary.composeEnv] using hCompose.symm
          rcases hEq with ⟨rfl, rfl⟩
          constructor
          · intro A hMem
            simp at hMem
          · exact variableDefinite_nil
      | cons _ _ =>
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
                  have hΓTail : VariableSurfaceEnv Γ := by
                    intro T hMem
                    exact hΓ T (List.mem_cons_of_mem _ hMem)
                  have hΔTail : VariableSurfaceEnv Δ := by
                    intro T hMem
                    exact hΔ T (List.mem_cons_of_mem _ hMem)
                  obtain ⟨hD, hHeadConstraints⟩ :=
                    composeTy_surface_variableDefinite op
                      (hΓ A (by simp)) (hΔ B (by simp)) hHead
                  obtain ⟨hΞ, hTailConstraints⟩ :=
                    ih hΓTail hΔTail
                      (by simpa only [composeEnv] using hTail)
                  constructor
                  · intro T hMem
                    rcases List.mem_cons.mp hMem with hHeadMem | hTailMem
                    · subst T
                      exact hD
                    · exact hΞ T hTailMem
                  · exact variableDefinite_append.mpr
                      ⟨hHeadConstraints, hTailConstraints⟩

theorem envSubtype_variableDefinite
    {Γ Δ : REnv} {C : UC}
    (hΓ : VariableEnv Γ)
    (hΔ : VariableSurfaceEnv Δ)
    (hSub : Raw.Env.subtypeConstraints Γ Δ = some C) :
    VariableDefinite C := by
  induction Γ generalizing Δ C with
  | nil =>
      cases Δ with
      | nil =>
          simp [Raw.Env.subtypeConstraints] at hSub
          subst C
          exact variableDefinite_nil
      | cons _ _ =>
          simp [Raw.Env.subtypeConstraints] at hSub
  | cons A Γ ih =>
      cases Δ with
      | nil =>
          simp [Raw.Env.subtypeConstraints] at hSub
      | cons B Δ =>
          cases hHead : Raw.Ty.subtypeConstraints A B with
          | none =>
              simp [Raw.Env.subtypeConstraints, hHead] at hSub
          | some CHead =>
              cases hTail : Raw.Env.subtypeConstraints Γ Δ with
              | none =>
                  simp [Raw.Env.subtypeConstraints, hHead, hTail] at hSub
              | some CTail =>
                  have hC : C = CHead ++ CTail := by
                    simpa [Raw.Env.subtypeConstraints, hHead, hTail]
                      using hSub.symm
                  subst C
                  have hΓTail : VariableEnv Γ := by
                    intro T hMem
                    exact hΓ T (List.mem_cons_of_mem _ hMem)
                  have hΔTail : VariableSurfaceEnv Δ := by
                    intro T hMem
                    exact hΔ T (List.mem_cons_of_mem _ hMem)
                  exact variableDefinite_append.mpr
                    ⟨subtype_variableDefinite
                       (hΓ A (by simp)) (hΔ B (by simp)) hHead,
                     ih hΓTail hΔTail hTail⟩

/-- Exporting a surface computation introduces only variable-left constraints. -/
theorem finish_variableDefinite
    {E Δ : REnv} {B T : RTy} {C : UC}
    (hE : VariableSurfaceEnv E)
    (hFinish : Finish E B Δ T C) :
    VariableDefinite C := by
  rcases hFinish with ⟨hΔ, hB, hT, CΓ, Cτ, hΓ, hτ, hC⟩
  subst C
  exact variableDefinite_append.mpr
    ⟨envSubtype_variableDefinite hΔ hE hΓ,
     subtype_variableDefinite hB (variableTy_surface hT) hτ⟩

theorem variableTy_outer
    {A : RTy} (hA : VariableTy A) :
    VariableExpr A.outer := by
  cases A with
  | int u => exact hA
  | prod A B u => exact hA.2.2
  | arrow A B u => exact hA.2.2

theorem variableEnv_tail
    {A : RTy} {Γ : REnv}
    (hΓ : VariableEnv (A :: Γ)) :
    VariableEnv Γ := by
  intro B hMem
  exact hΓ B (List.mem_cons_of_mem _ hMem)

theorem variableSurfaceEnv_cons
    {A : RTy} {Γ : REnv}
    (hA : VariableSurface A)
    (hΓ : VariableSurfaceEnv Γ) :
    VariableSurfaceEnv (A :: Γ) := by
  intro B hMem
  rcases List.mem_cons.mp hMem with hHead | hTail
  · subst B
    exact hA
  · exact hΓ B hTail

/-- Every rule preserves surface contexts and generates variable-left constraints. -/
theorem rule_surface_variableDefinite
    {ps : List Premise} {e : Term}
    {E : REnv} {B : RTy} {C : UC}
    (r : Rule ps e E B C)
    (hps : ∀ P ∈ ps, VariableEnv P.ctx ∧ VariableTy P.ty) :
    VariableSurfaceEnv E ∧ VariableDefinite C := by
  cases r with
  | const hΓ hu =>
      exact ⟨
        variableSurfaceEnv_scale _ (variableEnv_surface hΓ),
        lazyEnv_variableDefinite hΓ⟩

  | var hΓ hA =>
      exact ⟨
        variableSurfaceEnv_cons (variableTy_surface hA)
          (variableSurfaceEnv_scale _ (variableEnv_surface hΓ)),
        lazyEnv_variableDefinite hΓ⟩

  | varSkip hS =>
      have hp := hps _ (List.mem_singleton_self _)
      exact ⟨
        variableSurfaceEnv_cons
          (variableSurface_scale _ (variableTy_surface hS))
          (variableEnv_surface hp.1),
        lazyTy_variableDefinite hS⟩

  | abs hu =>
      have hp := hps _ (List.mem_singleton_self _)
      exact ⟨
        variableSurfaceEnv_scale _
          (variableEnv_surface (variableEnv_tail hp.1)),
        variable_inequality hu⟩

  | @app Γ₁ Γ₂ A A' B u e₁ e₂ C₁ C₂ E Cplus Csub
      hCompose hSub =>
      have hp₁ := hps
        ⟨Γ₁, e₁, .arrow A B u, C₁⟩ (by simp)
      have hp₂ := hps
        ⟨Γ₂, e₂, A', C₂⟩ (by simp)
      obtain ⟨hE, hPlus⟩ :=
        composeEnv_surface_variableDefinite .plus
          (variableEnv_surface hp₁.1)
          (variableSurfaceEnv_scale u (variableEnv_surface hp₂.1))
          hCompose
      exact ⟨hE,
        variableDefinite_append.mpr
          ⟨variableDefinite_append.mpr
             ⟨hPlus,
              rawSub_variableDefinite hp₂.2 hp₁.2.1 hSub⟩,
           variable_inequality hp₁.2.2.2⟩⟩

  | @pair Γ₁ Γ₂ A B u e₁ e₂ C₁ C₂ E Cplus hCompose =>
      have hp₁ := hps ⟨Γ₁, e₁, A, C₁⟩ (by simp)
      have hp₂ := hps ⟨Γ₂, e₂, B, C₂⟩ (by simp)
      obtain ⟨hE, hPlus⟩ :=
        composeEnv_surface_variableDefinite .plus
          (variableEnv_surface hp₁.1)
          (variableEnv_surface hp₂.1)
          hCompose
      have hBounds :
          VariableDefinite
            [⟨A.outer, .join u (.lit .lazy)⟩,
             ⟨B.outer, .join u (.lit .lazy)⟩] := by
        change VariableDefinite
          ([⟨A.outer, .join u (.lit .lazy)⟩] ++
           [⟨B.outer, .join u (.lit .lazy)⟩])
        exact variableDefinite_append.mpr
          ⟨variable_inequality (variableTy_outer hp₁.2),
           variable_inequality (variableTy_outer hp₂.2)⟩
      exact ⟨hE, variableDefinite_append.mpr ⟨hPlus, hBounds⟩⟩

  | projLeft =>
      have hp := hps _ (List.mem_singleton_self _)
      exact ⟨variableEnv_surface hp.1,
        variableDefinite_append.mpr
          ⟨variable_inequality hp.2.2.2,
           lazyTy_variableDefinite hp.2.2.1⟩⟩

  | projRight =>
      have hp := hps _ (List.mem_singleton_self _)
      exact ⟨variableEnv_surface hp.1,
        variableDefinite_append.mpr
          ⟨variable_inequality hp.2.2.2,
           lazyTy_variableDefinite hp.2.1⟩⟩

  | @op o Γ₁ Γ₂ u₁ u₂ u e₁ e₂ C₁ C₂ E Cplus hCompose =>
      have hp₁ := hps
        ⟨Γ₁, e₁, .int u₁, C₁⟩ (by simp)
      have hp₂ := hps
        ⟨Γ₂, e₂, .int u₂, C₂⟩ (by simp)
      obtain ⟨hE, hPlus⟩ :=
        composeEnv_surface_variableDefinite .plus
          (variableEnv_surface hp₁.1)
          (variableEnv_surface hp₂.1)
          hCompose
      have hBounds :
          VariableDefinite [⟨u₁, u⟩, ⟨u₂, u⟩] := by
        change VariableDefinite ([⟨u₁, u⟩] ++ [⟨u₂, u⟩])
        exact variableDefinite_append.mpr
          ⟨variable_inequality hp₁.2,
           variable_inequality hp₂.2⟩
      exact ⟨hE, variableDefinite_append.mpr ⟨hPlus, hBounds⟩⟩

  | @ite Γ₀ Γ₁ Γ₂ Γ₁₂ u A B T e₀ e₁ e₂ C₀ C₁ C₂
      E Ccap Cplus CA CB hT hCap hPlus hSubA hSubB =>
      have hp₀ := hps
        ⟨Γ₀, e₀, .int u, C₀⟩ (by simp)
      have hp₁ := hps
        ⟨Γ₁, e₁, A, C₁⟩ (by simp)
      have hp₂ := hps
        ⟨Γ₂, e₂, B, C₂⟩ (by simp)
      obtain ⟨hΓ₁₂, hCapConstraints⟩ :=
        composeEnv_surface_variableDefinite .cap
          (variableEnv_surface hp₁.1)
          (variableEnv_surface hp₂.1)
          hCap
      obtain ⟨hE, hPlusConstraints⟩ :=
        composeEnv_surface_variableDefinite .plus
          (variableEnv_surface hp₀.1) hΓ₁₂ hPlus
      exact ⟨hE,
        variableDefinite_append.mpr
          ⟨variableDefinite_append.mpr
             ⟨variableDefinite_append.mpr
                ⟨variableDefinite_append.mpr
                   ⟨hCapConstraints, hPlusConstraints⟩,
                 rawSub_variableDefinite hp₁.2 hT hSubA⟩,
              rawSub_variableDefinite hp₂.2 hT hSubB⟩,
           variable_inequality hp₀.2⟩⟩

  | @letE Γ₁ Γ₂ A A' B e₁ e₂ C₁ C₂ E Cplus Csub
      hCompose hSub =>
      have hp₁ := hps ⟨Γ₁, e₁, A, C₁⟩ (by simp)
      have hp₂ := hps
        ⟨A' :: Γ₂, e₂, B, C₂⟩ (by simp)
      have hA' : VariableTy A' := hp₂.1 A' (by simp)
      obtain ⟨hE, hPlus⟩ :=
        composeEnv_surface_variableDefinite .plus
          (variableEnv_surface hp₁.1)
          (variableEnv_surface (variableEnv_tail hp₂.1))
          hCompose
      exact ⟨hE,
        variableDefinite_append.mpr
          ⟨hPlus, rawSub_variableDefinite hp₁.2 hA' hSub⟩⟩

  | @fix Γ A B body C E Cplus Csub hCompose hSub =>
      have hp := hps ⟨A :: Γ, body, B, C⟩ (by simp)
      have hA := hp.1 A (by simp)
      have hΓ := variableEnv_tail hp.1
      obtain ⟨hE, hPlus⟩ :=
        composeEnv_surface_variableDefinite .plus
          (variableEnv_surface hΓ)
          (variableSurfaceEnv_scale _ (variableEnv_surface hΓ)) hCompose
      exact ⟨hE, variableDefinite_append.mpr
        ⟨hPlus, subtype_variableDefinite hp.2
          (variableSurface_raiseStrict hA) hSub⟩⟩

/-- Every generated constraint has a variable on the left and a monotone RHS. -/
theorem Derives.constraints_variableDefinite
    {Γ : REnv} {e : Term} {T : RTy} {C : UC}
    (d : Derives Γ e T C) :
    VariableDefinite C := by
induction d with
  | node hRule hChildren hFinish ih =>
      rename_i ps eNode E B CLocal Δ TNode CBoundary
      have hps :
          ∀ (P : Premise), P ∈ ps →
            VariableEnv P.ctx ∧ VariableTy P.ty :=
        fun P hMem => (hChildren P hMem).boundary_variables
      obtain ⟨hE, hLocal⟩ :=
        rule_surface_variableDefinite hRule hps
      have hPremises :
          VariableDefinite (premiseConstraints ps) := by
        intro c hc
        change c ∈ ps.flatMap (fun P => P.constraints) at hc
        obtain ⟨P, hMem, hcP⟩ := List.mem_flatMap.mp hc
        exact ih P hMem c hcP
      exact variableDefinite_append.mpr
        ⟨variableDefinite_append.mpr ⟨hPremises, hLocal⟩,
         finish_variableDefinite hE hFinish⟩

/-- The stronger variable-left form also satisfies the dual-D predicate. -/
theorem variableDefinite_dualDefinite
    {C : UC} (hC : VariableDefinite C) :
    C.DualDefinite := by
  intro c hc
  obtain ⟨hLeft, hRight⟩ := hC c hc
  exact ⟨variableExpr_isAtom hLeft, hRight⟩

theorem Derives.constraints_dualDefinite
    {Γ : REnv} {e : Term} {T : RTy} {C : UC}
    (d : Derives Γ e T C) :
    C.DualDefinite := by
  exact variableDefinite_dualDefinite d.constraints_variableDefinite

theorem subtype_refl (A : Strictness.Ty) :
    Strictness.Ty.Subtype A A := by
  induction A with
  | int u =>
      exact .int (Usage.le_refl u)
  | prod A B u ihA ihB =>
      exact .prod ihA ihB (Usage.le_refl u)
  | arrow A B u ihA ihB =>
      exact .arrow ihA ihB (Usage.le_refl u)

theorem envSubtype_refl (Γ : Strictness.Env) :
    Strictness.Env.Subtype Γ Γ := by
  induction Γ with
  | nil =>
      trivial
  | cons A Γ ih =>
      exact ⟨subtype_refl A, ih⟩

/--
Structural comparisons that hold after evaluation produce satisfied
boundary constraints, provided their structural expansion succeeds.
-/
theorem finish_of_bounds
    {ν : Raw.Valuation}
    {E Δ : REnv} {B T : RTy} {CΓ Cτ : UC}
    (hΔ : VariableEnv Δ)
    (hB : VariableTy B)
    (hT : VariableTy T)
    (hExpandΓ : Raw.Env.subtypeConstraints Δ E = some CΓ)
    (hExpandτ : Raw.Ty.subtypeConstraints B T = some Cτ)
    (hBoundΓ :
      Strictness.Env.Subtype (Δ.eval ν) (E.eval ν))
    (hBoundτ :
      Strictness.Ty.Subtype (B.eval ν) (T.eval ν)) :
    Finish E B Δ T (CΓ ++ Cτ) ∧
    (CΓ ++ Cτ).Satisfies ν := by
  constructor
  · exact ⟨hΔ, hB, hT, CΓ, Cτ, hExpandΓ, hExpandτ, rfl⟩
  · exact Raw.UseConstraints.satisfies_append.mpr
      ⟨(Raw.Env.eval_subtypeConstraints hExpandΓ).mpr hBoundΓ,
       (Raw.Ty.eval_subtypeConstraints hExpandτ).mpr hBoundτ⟩

/-- An exported boundary may reproduce the computed judgment exactly. -/
theorem finish_of_equal_eval
    {ν : Raw.Valuation}
    {E Δ : REnv} {B T : RTy} {CΓ Cτ : UC}
    (hΔ : VariableEnv Δ)
    (hB : VariableTy B)
    (hT : VariableTy T)
    (hExpandΓ : Raw.Env.subtypeConstraints Δ E = some CΓ)
    (hExpandτ : Raw.Ty.subtypeConstraints B T = some Cτ)
    (hEvalΓ : Δ.eval ν = E.eval ν)
    (hEvalτ : B.eval ν = T.eval ν) :
    Finish E B Δ T (CΓ ++ Cτ) ∧
    (CΓ ++ Cτ).Satisfies ν := by
  apply finish_of_bounds hΔ hB hT hExpandΓ hExpandτ
  · rw [hEvalΓ]
    exact envSubtype_refl _
  · rw [hEvalτ]
    exact subtype_refl _

end Strictness.RawInference.CoreBoundary
