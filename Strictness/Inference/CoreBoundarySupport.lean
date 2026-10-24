import Strictness.Inference.CoreBoundaryCompleteness

namespace Strictness.RawInference.CoreBoundary

open Raw

def ExprBelow (limit : Nat) : Raw.Expr → Prop
  | .var a => a < limit
  | .lit _ => True
  | .add p q | .meet p q | .join p q | .scale p q =>
      ExprBelow limit p ∧ ExprBelow limit q

def TyBelow (limit : Nat) : RTy → Prop
  | .int u => ExprBelow limit u
  | .prod A B u | .arrow A B u =>
      TyBelow limit A ∧ TyBelow limit B ∧ ExprBelow limit u

def EnvBelow (limit : Nat) (Γ : REnv) : Prop :=
  ∀ A ∈ Γ, TyBelow limit A

def ConstraintsBelow (limit : Nat) (C : UC) : Prop :=
  ∀ c ∈ C, ExprBelow limit c.lhs ∧ ExprBelow limit c.rhs

def AgreeBelow
    (limit : Nat) (ν' ν : Raw.Valuation) : Prop :=
  ∀ i, i < limit → ν' i = ν i

theorem exprBelow_mono
    {p : Raw.Expr} {lo hi : Nat}
    (h : ExprBelow lo p) (hLe : lo ≤ hi) :
    ExprBelow hi p := by
  induction p with
  | var a =>
      exact Nat.lt_of_lt_of_le h hLe
  | lit u =>
      trivial
  | add p q ihP ihQ
  | meet p q ihP ihQ
  | join p q ihP ihQ
  | scale p q ihP ihQ =>
      exact ⟨ihP h.1, ihQ h.2⟩

theorem tyBelow_mono
    {A : RTy} {lo hi : Nat}
    (h : TyBelow lo A) (hLe : lo ≤ hi) :
    TyBelow hi A := by
  induction A with
  | int u =>
      exact exprBelow_mono h hLe
  | prod A B u ihA ihB
  | arrow A B u ihA ihB =>
      exact ⟨ihA h.1, ihB h.2.1,
        exprBelow_mono h.2.2 hLe⟩

theorem exprInRange_below
    {p : Raw.Expr} {lo hi : Nat}
    (h : ExprInRange lo hi p) :
    ExprBelow hi p := by
  cases p with
  | var a => exact h.2
  | lit u => exact False.elim h
  | add p q => exact False.elim h
  | meet p q => exact False.elim h
  | join p q => exact False.elim h
  | scale p q => exact False.elim h

theorem tyInRange_below
    {A : RTy} {lo hi : Nat}
    (h : TyInRange lo hi A) :
    TyBelow hi A := by
  induction A with
  | int u =>
      exact exprInRange_below h
  | prod A B u ihA ihB
  | arrow A B u ihA ihB =>
      exact ⟨ihA h.1, ihB h.2.1, exprInRange_below h.2.2⟩

theorem allocatedTy_below
    (A : Strictness.Ty) (start : Nat) :
    TyBelow (start + annotationCount A) (allocatedTy start A) := by
  exact tyInRange_below (allocatedTy_range A start)

theorem allocatedEnv_below
    (Γ : Strictness.Env) (start : Nat) :
    EnvBelow (start + envAnnotationCount Γ)
      (allocatedEnv start Γ) := by
  induction Γ generalizing start with
  | nil =>
      intro A hMem
      simp [allocatedEnv] at hMem
  | cons A Γ ih =>
      intro B hMem
      change B ∈ allocatedTy start A ::
        allocatedEnv (start + annotationCount A) Γ at hMem
      rcases List.mem_cons.mp hMem with hHead | hTail
      · subst B
        apply tyBelow_mono (allocatedTy_below A start)
        simp only [envAnnotationCount]
        omega
      · have hTailBound :=
          ih (start + annotationCount A) B hTail
        simpa only [envAnnotationCount, Nat.add_assoc] using hTailBound

/-- Values of bounded expressions depend only on the preserved prefix. -/
theorem eval_expr_agreeBelow
    {limit : Nat} {ν ν' : Raw.Valuation}
    {p : Raw.Expr}
    (hBound : ExprBelow limit p)
    (hAgree : AgreeBelow limit ν' ν) :
    p.eval ν' = p.eval ν := by
  induction p with
  | var a =>
      exact hAgree a hBound
  | lit u =>
      rfl
  | add p q ihP ihQ
  | meet p q ihP ihQ
  | join p q ihP ihQ
  | scale p q ihP ihQ =>
      simp only [Raw.Expr.eval, ihP hBound.1, ihQ hBound.2]

theorem eval_ty_agreeBelow
    {limit : Nat} {ν ν' : Raw.Valuation}
    {A : RTy}
    (hBound : TyBelow limit A)
    (hAgree : AgreeBelow limit ν' ν) :
    A.eval ν' = A.eval ν := by
  induction A with
  | int u =>
      simp only [Raw.Ty.eval,
        eval_expr_agreeBelow hBound hAgree]
  | prod A B u ihA ihB
  | arrow A B u ihA ihB =>
      simp only [Raw.Ty.eval, ihA hBound.1, ihB hBound.2.1,
        eval_expr_agreeBelow hBound.2.2 hAgree]

theorem eval_env_agreeBelow
    {limit : Nat} {ν ν' : Raw.Valuation}
    {Γ : REnv}
    (hBound : EnvBelow limit Γ)
    (hAgree : AgreeBelow limit ν' ν) :
    Raw.Env.eval ν' Γ = Raw.Env.eval ν Γ := by
  induction Γ with
  | nil =>
      rfl
  | cons A Γ ih =>
      have hHead := hBound A (by simp)
      have hTail : EnvBelow limit Γ := by
        intro B hMem
        exact hBound B (List.mem_cons_of_mem _ hMem)
      simp only [Raw.Env.eval,
        eval_ty_agreeBelow hHead hAgree, ih hTail]

theorem satisfies_agreeBelow
    {limit : Nat} {ν ν' : Raw.Valuation}
    {C : UC}
    (hBound : ConstraintsBelow limit C)
    (hAgree : AgreeBelow limit ν' ν)
    (hSat : C.Satisfies ν) :
    C.Satisfies ν' := by
  intro c hc
  obtain ⟨hLeft, hRight⟩ := hBound c hc
  change c.lhs.eval ν' ≤ c.rhs.eval ν'
  rw [eval_expr_agreeBelow hLeft hAgree,
      eval_expr_agreeBelow hRight hAgree]
  exact hSat c hc

/-- Writing at or above limit preserves the entire earlier prefix. -/
theorem writeTy_agreeBelow
    (A : Strictness.Ty) (ν : Raw.Valuation)
    {limit start : Nat}
    (hStart : limit ≤ start) :
    AgreeBelow limit (writeTy A ν start) ν := by
  intro i hi
  exact writeTy_outside A ν start i
    (Or.inl (Nat.lt_of_lt_of_le hi hStart))

theorem writeEnv_agreeBelow
    (Γ : Strictness.Env) (ν : Raw.Valuation)
    {limit start : Nat}
    (hStart : limit ≤ start) :
    AgreeBelow limit (writeEnv Γ ν start) ν := by
  intro i hi
  exact writeEnv_outside Γ ν start i
    (Or.inl (Nat.lt_of_lt_of_le hi hStart))

theorem writeBoundary_agreeBelow
    (Γ : Strictness.Env) (T : Strictness.Ty)
    (ν : Raw.Valuation)
    {limit start : Nat}
    (hStart : limit ≤ start) :
    AgreeBelow limit (writeBoundary Γ T ν start) ν := by
  intro i hi
  exact writeBoundary_outside Γ T ν start i
    (Or.inl (Nat.lt_of_lt_of_le hi hStart))

theorem satisfies_writeBoundary
    {limit start : Nat} {ν : Raw.Valuation} {C : UC}
    (Γ : Strictness.Env) (T : Strictness.Ty)
    (hBound : ConstraintsBelow limit C)
    (hStart : limit ≤ start)
    (hSat : C.Satisfies ν) :
    C.Satisfies (writeBoundary Γ T ν start) := by
  exact satisfies_agreeBelow hBound
    (writeBoundary_agreeBelow Γ T ν hStart) hSat

theorem constraintsBelow_nil (limit : Nat) :
    ConstraintsBelow limit [] := by
  intro c hc
  simp at hc

theorem constraintsBelow_append
    {limit : Nat} {C D : UC}
    (hC : ConstraintsBelow limit C)
    (hD : ConstraintsBelow limit D) :
    ConstraintsBelow limit (C ++ D) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hC c hc
  · exact hD c hc

theorem constraintsBelow_singleton
    {limit : Nat} {p q : Raw.Expr}
    (hp : ExprBelow limit p)
    (hq : ExprBelow limit q) :
    ConstraintsBelow limit [⟨p, q⟩] := by
  intro c hc
  simp only [List.mem_singleton] at hc
  subst c
  exact ⟨hp, hq⟩

theorem constraintsBelow_three
    {limit : Nat} {C₁ C₂ C₃ : UC}
    (h₁ : ConstraintsBelow limit C₁)
    (h₂ : ConstraintsBelow limit C₂)
    (h₃ : ConstraintsBelow limit C₃) :
    ConstraintsBelow limit (C₁ ++ C₂ ++ C₃) := by
  exact constraintsBelow_append
    (constraintsBelow_append h₁ h₂) h₃

theorem tyBelow_outer
    {limit : Nat} {A : RTy}
    (hA : TyBelow limit A) :
    ExprBelow limit A.outer := by
  cases A with
  | int u => exact hA
  | prod A B u => exact hA.2.2
  | arrow A B u => exact hA.2.2

theorem tyBelow_raiseStrict
    {limit : Nat} {A : RTy} (hA : TyBelow limit A) :
    TyBelow limit A.raiseStrict := by
  cases A with
  | int u => exact ⟨hA, True.intro⟩
  | prod A B u => exact ⟨hA.1, hA.2.1, hA.2.2, True.intro⟩
  | arrow A B u => exact ⟨hA.1, hA.2.1, hA.2.2, True.intro⟩

theorem tyBelow_scale
    {limit : Nat} {p : Raw.Expr} {A : RTy}
    (hp : ExprBelow limit p)
    (hA : TyBelow limit A) :
    TyBelow limit (Raw.Ty.scale p A) := by
  induction A with
  | int u =>
      exact ⟨hp, hA⟩
  | prod A B u ihA ihB =>
      exact ⟨ihA hA.1, ihB hA.2.1, hp, hA.2.2⟩
  | arrow A B u =>
      exact ⟨hA.1, hA.2.1, hp, hA.2.2⟩

theorem envBelow_scale
    {limit : Nat} {p : Raw.Expr} {Γ : REnv}
    (hp : ExprBelow limit p)
    (hΓ : EnvBelow limit Γ) :
    EnvBelow limit (Raw.Env.scale p Γ) := by
  induction Γ with
  | nil =>
      intro A hMem
      simp [Raw.Env.scale] at hMem
  | cons A Γ ih =>
      have hTail : EnvBelow limit Γ := by
        intro B hMem
        exact hΓ B (List.mem_cons_of_mem _ hMem)
      intro B hMem
      change B ∈ Raw.Ty.scale p A :: Raw.Env.scale p Γ at hMem
      rcases List.mem_cons.mp hMem with hHead | hRest
      · subst B
        exact tyBelow_scale hp (hΓ A (by simp))
      · exact ih hTail B hRest

private theorem subtypeFuel_below
    {limit n : Nat} {A B : RTy} {C : UC}
    (hA : TyBelow limit A)
    (hB : TyBelow limit B)
    (hC : Raw.Ty.subtypeConstraintsFuel n A B = some C) :
    ConstraintsBelow limit C := by
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
              exact constraintsBelow_singleton hA hB
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
                      simpa only [List.append_assoc] using
                        constraintsBelow_three
                          (ih hA.1 hB.1 h₁)
                          (ih hA.2.1 hB.2.1 h₂)
                          (constraintsBelow_singleton hA.2.2 hB.2.2)
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
                      simpa only [List.append_assoc] using
                        constraintsBelow_three
                          (ih hB.1 hA.1 h₁)
                          (ih hA.2.1 hB.2.1 h₂)
                          (constraintsBelow_singleton hA.2.2 hB.2.2)

theorem subtypeConstraints_below
    {limit : Nat} {A B : RTy} {C : UC}
    (hA : TyBelow limit A)
    (hB : TyBelow limit B)
    (hC : Raw.Ty.subtypeConstraints A B = some C) :
    ConstraintsBelow limit C := by
  exact subtypeFuel_below hA hB hC

theorem equalTypes_below
    {limit : Nat} {A B : RTy} {C : UC}
    (hA : TyBelow limit A)
    (hB : TyBelow limit B)
    (hEqual : Boundary.equalTypes A B = some C) :
    ConstraintsBelow limit C := by
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
          exact constraintsBelow_append
            (subtypeConstraints_below hA hB hAB)
            (subtypeConstraints_below hB hA hBA)

theorem combineOp_expr_below
    (op : Boundary.CombineOp)
    {limit : Nat} {p q : Raw.Expr}
    (hp : ExprBelow limit p)
    (hq : ExprBelow limit q) :
    ExprBelow limit (op.expr p q) := by
  cases op <;> exact ⟨hp, hq⟩

theorem composeTy_below
    (op : Boundary.CombineOp)
    {limit : Nat} {A B D : RTy} {C : UC}
    (hA : TyBelow limit A)
    (hB : TyBelow limit B)
    (hCompose : Boundary.composeTy op A B = some (D, C)) :
    TyBelow limit D ∧ ConstraintsBelow limit C := by
  induction A generalizing B D C with
  | int u =>
      cases B with
      | int v =>
          have hEq : D = .int (op.expr u v) ∧ C = [] := by
            simpa [Boundary.composeTy] using hCompose.symm
          rcases hEq with ⟨rfl, rfl⟩
          exact ⟨combineOp_expr_below op hA hB,
            constraintsBelow_nil limit⟩
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
                      D = .prod D₁ D₂ (op.expr u v) ∧ C = C₁ ++ C₂ := by
                    simpa [Boundary.composeTy, h₁, h₂] using hCompose.symm
                  rcases hEq with ⟨rfl, rfl⟩
                  obtain ⟨hD₁, hC₁⟩ := ih₁ hA.1 hB.1 h₁
                  obtain ⟨hD₂, hC₂⟩ := ih₂ hA.2.1 hB.2.1 h₂
                  exact ⟨⟨hD₁, hD₂,
                    combineOp_expr_below op hA.2.2 hB.2.2⟩,
                    constraintsBelow_append hC₁ hC₂⟩
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
                      D = .arrow A₁ A₂ (op.expr u v) ∧ C = C₁ ++ C₂ := by
                    simpa [Boundary.composeTy, h₁, h₂] using hCompose.symm
                  rcases hEq with ⟨rfl, rfl⟩
                  exact ⟨⟨hA.1, hA.2.1,
                    combineOp_expr_below op hA.2.2 hB.2.2⟩,
                    constraintsBelow_append
                      (equalTypes_below hA.1 hB.1 h₁)
                      (equalTypes_below hA.2.1 hB.2.1 h₂)⟩

theorem composeEnv_below
    (op : Boundary.CombineOp)
    {limit : Nat} {Γ Δ E : REnv} {C : UC}
    (hΓ : EnvBelow limit Γ)
    (hΔ : EnvBelow limit Δ)
    (hCompose : composeEnv op Γ Δ = some (E, C)) :
    EnvBelow limit E ∧ ConstraintsBelow limit C := by
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
          · exact constraintsBelow_nil limit
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
                  have hEq : E = D :: Ξ ∧ C = CHead ++ CTail := by
                    simpa [composeEnv, Boundary.composeEnv, hHead, hTail]
                      using hCompose.symm
                  rcases hEq with ⟨rfl, rfl⟩
                  have hΓTail : EnvBelow limit Γ := by
                    intro T hMem
                    exact hΓ T (List.mem_cons_of_mem _ hMem)
                  have hΔTail : EnvBelow limit Δ := by
                    intro T hMem
                    exact hΔ T (List.mem_cons_of_mem _ hMem)
                  obtain ⟨hD, hCHead⟩ :=
                    composeTy_below op
                      (hΓ A (by simp)) (hΔ B (by simp)) hHead
                  obtain ⟨hΞ, hCTail⟩ :=
                    ih hΓTail hΔTail
                      (by simpa only [composeEnv] using hTail)
                  constructor
                  · intro T hMem
                    rcases List.mem_cons.mp hMem with hHeadMem | hTailMem
                    · subst T
                      exact hD
                    · exact hΞ T hTailMem
                  · exact constraintsBelow_append hCHead hCTail

theorem envSubtypeConstraints_below
    {limit : Nat} {Γ Δ : REnv} {C : UC}
    (hΓ : EnvBelow limit Γ)
    (hΔ : EnvBelow limit Δ)
    (hSub : Raw.Env.subtypeConstraints Γ Δ = some C) :
    ConstraintsBelow limit C := by
  induction Γ generalizing Δ C with
  | nil =>
      cases Δ with
      | nil =>
          simp [Raw.Env.subtypeConstraints] at hSub
          subst C
          exact constraintsBelow_nil limit
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
                  have hΓTail : EnvBelow limit Γ := by
                    intro T hMem
                    exact hΓ T (List.mem_cons_of_mem _ hMem)
                  have hΔTail : EnvBelow limit Δ := by
                    intro T hMem
                    exact hΔ T (List.mem_cons_of_mem _ hMem)
                  exact constraintsBelow_append
                    (subtypeConstraints_below
                      (hΓ A (by simp)) (hΔ B (by simp)) hHead)
                    (ih hΓTail hΔTail hTail)

theorem finish_constraints_below
    {limit : Nat}
    {E Δ : REnv} {B T : RTy} {C : UC}
    (hE : EnvBelow limit E)
    (hΔ : EnvBelow limit Δ)
    (hB : TyBelow limit B)
    (hT : TyBelow limit T)
    (hFinish : Finish E B Δ T C) :
    ConstraintsBelow limit C := by
  rcases hFinish with ⟨_, _, _, CΓ, Cτ, hΓ, hτ, hC⟩
  subst C
  exact constraintsBelow_append
    (envSubtypeConstraints_below hΔ hE hΓ)
    (subtypeConstraints_below hB hT hτ)

end Strictness.RawInference.CoreBoundary
