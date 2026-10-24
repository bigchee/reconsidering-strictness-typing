import Strictness.Inference.CoreBoundarySupport

/-!
Shared witnesses and operations for completeness of constraint generation.

`ConstructionWitness` records a generated derivation and a satisfying
valuation while retaining all previously allocated variables. `ReadyPremise`
allows several child witnesses to be combined at one valuation. The common
completion lemmas handle exported boundaries and one, two or three premises.
-/

namespace Strictness.RawInference.CoreBoundary

open Raw

theorem envBelow_mono
    {lo hi : Nat} {Γ : REnv}
    (hΓ : EnvBelow lo Γ) (hLe : lo ≤ hi) :
    EnvBelow hi Γ := by
  intro A hMem
  exact tyBelow_mono (hΓ A hMem) hLe

theorem constraintsBelow_mono
    {lo hi : Nat} {C : UC}
    (hC : ConstraintsBelow lo C) (hLe : lo ≤ hi) :
    ConstraintsBelow hi C := by
  intro c hc
  obtain ⟨hLeft, hRight⟩ := hC c hc
  exact ⟨exprBelow_mono hLeft hLe, exprBelow_mono hRight hLe⟩

theorem lazyTy_below
    {limit : Nat} {A : RTy}
    (hA : TyBelow limit A) :
    ConstraintsBelow limit A.lazyConstraints := by
  induction A with
  | int u =>
      exact constraintsBelow_singleton hA True.intro
  | prod A B u ihA ihB =>
      exact constraintsBelow_three
        (constraintsBelow_singleton hA.2.2 True.intro)
        (ihA hA.1) (ihB hA.2.1)
  | arrow A B u =>
      exact constraintsBelow_singleton hA.2.2 True.intro

theorem lazyEnv_below
    {limit : Nat} {Γ : REnv}
    (hΓ : EnvBelow limit Γ) :
    ConstraintsBelow limit Γ.lazyConstraints := by
  induction Γ with
  | nil =>
      exact constraintsBelow_nil limit
  | cons A Γ ih =>
      have hTail : EnvBelow limit Γ := by
        intro B hMem
        exact hΓ B (List.mem_cons_of_mem _ hMem)
      exact constraintsBelow_append
        (lazyTy_below (hΓ A (by simp))) (ih hTail)

/--
A generated node together with the bounds needed to replace its root boundary.
Child derivations remain ordinary Derives judgments.
-/
inductive SupportedDerives (limit : Nat) :
    REnv → Term → RTy → UC → Prop where
  | node {ps e E B C₀ Δ T Cb} :
      Rule ps e E B C₀ →
      (∀ P ∈ ps, Derives P.ctx P.term P.ty P.constraints) →
      Finish E B Δ T Cb →
      EnvBelow limit E →
      TyBelow limit B →
      ConstraintsBelow limit (premiseConstraints ps) →
      ConstraintsBelow limit C₀ →
      ConstraintsBelow limit Cb →
      SupportedDerives limit Δ e T
        (premiseConstraints ps ++ C₀ ++ Cb)

theorem SupportedDerives.toDerives
    {limit : Nat} {Γ : REnv} {e : Term} {T : RTy} {C : UC}
    (d : SupportedDerives limit Γ e T C) :
    Derives Γ e T C := by
  cases d with
  | node hRule hChildren hFinish hE hB hPremises hLocal hBoundary =>
      exact Derives.node hRule hChildren hFinish

theorem SupportedDerives.constraints_below
    {limit : Nat} {Γ : REnv} {e : Term} {T : RTy} {C : UC}
    (d : SupportedDerives limit Γ e T C) :
    ConstraintsBelow limit C := by
  cases d with
  | node hRule hChildren hFinish hE hB hPremises hLocal hBoundary =>
      exact constraintsBelow_three hPremises hLocal hBoundary

/-- The strengthened witness returned by the completeness construction. -/
structure ConstructionWitness
    (start : Nat) (initial : Raw.Valuation)
    (Γ : Strictness.Env) (e : Term) (τ : Strictness.Ty) where
  stop : Nat
  valuation : Raw.Valuation
  ctx : REnv
  ty : RTy
  constraints : UC
  stop_ge : start ≤ stop
  preservesPrefix : AgreeBelow start valuation initial
  supported : SupportedDerives stop ctx e ty constraints
  satisfies : constraints.Satisfies valuation
  ctx_eval : Raw.Env.eval valuation ctx = Γ
  ty_eval : ty.eval valuation = τ
  ctx_below : EnvBelow stop ctx
  ty_below : TyBelow stop ty

def Buildable
    (Γ : Strictness.Env) (e : Term) (τ : Strictness.Ty) : Prop :=
  ∀ start initial, Nonempty (ConstructionWitness start initial Γ e τ)

/--
Shared final step for every rule.
Allocate the exported boundary after the variables already in use.
-/
theorem completeNode
    {start limit : Nat}
    {initial ν : Raw.Valuation}
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty}
    {ps : List Premise} {E : REnv} {B : RTy} {C₀ : UC}
    (hRule : Rule ps e E B C₀)
    (hChildren : ∀ P ∈ ps, Derives P.ctx P.term P.ty P.constraints)
    (hPremisesSat : (premiseConstraints ps).Satisfies ν)
    (hLocalSat : C₀.Satisfies ν)
    (hE : EnvBelow limit E)
    (hB : TyBelow limit B)
    (hBVariables : VariableTy B)
    (hPremisesBound : ConstraintsBelow limit (premiseConstraints ps))
    (hLocalBound : ConstraintsBelow limit C₀)
    (hEnv : Strictness.Env.Subtype Γ (Raw.Env.eval ν E))
    (hTy : Strictness.Ty.Subtype (B.eval ν) τ)
    (hStart : start ≤ limit)
    (hPrefix : AgreeBelow start ν initial) :
    Nonempty (ConstructionWitness start initial Γ e τ) := by
  let Δ := allocatedEnv limit Γ
  let T := allocatedTy (limit + envAnnotationCount Γ) τ
  let νFinal := writeBoundary Γ τ ν limit
  let stop := limit + envAnnotationCount Γ + annotationCount τ

  have hLimit : limit ≤ stop := by
    dsimp [stop]
    omega
  have hAgree : AgreeBelow limit νFinal ν :=
    writeBoundary_agreeBelow Γ τ ν (Nat.le_refl limit)

  obtain ⟨hΔEval, hTEval⟩ := allocatedBoundary_eval Γ τ ν limit

  have hNewEnv :
      Strictness.Env.Subtype
        (Raw.Env.eval νFinal Δ) (Raw.Env.eval νFinal E) := by
    rw [hΔEval, eval_env_agreeBelow hE hAgree]
    exact hEnv
  have hNewTy :
      Strictness.Ty.Subtype (B.eval νFinal) (T.eval νFinal) := by
    rw [hTEval, eval_ty_agreeBelow hB hAgree]
    exact hTy

  obtain ⟨Cb, hFinish, hBoundarySat⟩ :=
    finish_exists
      (allocatedEnv_variables Γ limit)
      hBVariables
      (allocatedTy_variables τ (limit + envAnnotationCount Γ))
      hNewEnv hNewTy

  have hΔBound : EnvBelow stop Δ := by
    apply envBelow_mono (allocatedEnv_below Γ limit)
    dsimp [stop]
    omega
  have hTBound : TyBelow stop T :=
    allocatedTy_below τ (limit + envAnnotationCount Γ)
  have hEBound := envBelow_mono hE hLimit
  have hBBound := tyBelow_mono hB hLimit
  have hPremisesFinalBound := constraintsBelow_mono hPremisesBound hLimit
  have hLocalFinalBound := constraintsBelow_mono hLocalBound hLimit
  have hBoundaryBound :=
    finish_constraints_below hEBound hΔBound hBBound hTBound hFinish

  have hPremisesFinalSat :=
    satisfies_agreeBelow hPremisesBound hAgree hPremisesSat
  have hLocalFinalSat :=
    satisfies_agreeBelow hLocalBound hAgree hLocalSat

  refine ⟨{
    stop := stop
    valuation := νFinal
    ctx := Δ
    ty := T
    constraints := premiseConstraints ps ++ C₀ ++ Cb
    stop_ge := Nat.le_trans hStart hLimit
    preservesPrefix := ?_
    supported := SupportedDerives.node
      hRule hChildren hFinish
      hEBound hBBound hPremisesFinalBound hLocalFinalBound hBoundaryBound
    satisfies := Raw.UseConstraints.satisfies_append.mpr
      ⟨Raw.UseConstraints.satisfies_append.mpr
        ⟨hPremisesFinalSat, hLocalFinalSat⟩, hBoundarySat⟩
    ctx_eval := hΔEval
    ty_eval := hTEval
    ctx_below := hΔBound
    ty_below := hTBound
  }⟩
  intro i hi
  exact (hAgree i (Nat.lt_of_lt_of_le hi hStart)).trans (hPrefix i hi)

/-- Move a witness to a valuation agreeing on all of its used variables. -/
def ConstructionWitness.revalue
    {start : Nat} {initial : Raw.Valuation}
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty}
    (w : ConstructionWitness start initial Γ e τ)
    {ν : Raw.Valuation}
    (hAgree : AgreeBelow w.stop ν w.valuation) :
    ConstructionWitness start initial Γ e τ where
  stop := w.stop
  valuation := ν
  ctx := w.ctx
  ty := w.ty
  constraints := w.constraints
  stop_ge := w.stop_ge
  preservesPrefix := by
    intro i hi
    exact
      (hAgree i (Nat.lt_of_lt_of_le hi w.stop_ge)).trans
        (w.preservesPrefix i hi)
  supported := w.supported
  satisfies :=
    satisfies_agreeBelow w.supported.constraints_below hAgree w.satisfies
  ctx_eval :=
    (eval_env_agreeBelow w.ctx_below hAgree).trans w.ctx_eval
  ty_eval :=
    (eval_ty_agreeBelow w.ty_below hAgree).trans w.ty_eval
  ctx_below := w.ctx_below
  ty_below := w.ty_below

theorem completeUnary
    {start limit : Nat} {initial ν : Raw.Valuation}
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty}
    {G : REnv} {body : Term} {A : RTy} {CChild : UC}
    {E : REnv} {B : RTy} {C₀ : UC}
    (hRule : Rule [⟨G, body, A, CChild⟩] e E B C₀)
    (hChild : Derives G body A CChild)
    (hChildSat : CChild.Satisfies ν)
    (hChildBound : ConstraintsBelow limit CChild)
    (hLocalSat : C₀.Satisfies ν)
    (hE : EnvBelow limit E)
    (hB : TyBelow limit B)
    (hBVariables : VariableTy B)
    (hLocalBound : ConstraintsBelow limit C₀)
    (hEnv : Strictness.Env.Subtype Γ (Raw.Env.eval ν E))
    (hTy : Strictness.Ty.Subtype (B.eval ν) τ)
    (hStart : start ≤ limit)
    (hPrefix : AgreeBelow start ν initial) :
    Nonempty (ConstructionWitness start initial Γ e τ) := by
  apply completeNode hRule
  · intro P hMem
    have hEq : P = ⟨G, body, A, CChild⟩ :=
      List.mem_singleton.mp hMem
    subst P
    exact hChild
  · simpa [premiseConstraints] using hChildSat
  · exact hLocalSat
  · exact hE
  · exact hB
  · exact hBVariables
  · simpa [premiseConstraints] using hChildBound
  · exact hLocalBound
  · exact hEnv
  · exact hTy
  · exact hStart
  · exact hPrefix

/-- Complete an already supported root with a different concrete boundary. -/
theorem completeSupported
    {start limit : Nat} {initial ν : Raw.Valuation}
    {G : REnv} {e : Term} {A : RTy} {C : UC}
    {Γ : Strictness.Env} {τ : Strictness.Ty}
    (d : SupportedDerives limit G e A C)
    (hSat : C.Satisfies ν)
    (hEnv : Strictness.Env.Subtype Γ (Raw.Env.eval ν G))
    (hTy : Strictness.Ty.Subtype (A.eval ν) τ)
    (hStart : start ≤ limit)
    (hPrefix : AgreeBelow start ν initial) :
    Nonempty (ConstructionWitness start initial Γ e τ) := by
  cases d with
  | node hRule hChildren hFinish hE hB hPremBound hLocalBound hBoundaryBound =>
      obtain ⟨hPremSat, hLocalSat, hBoundarySat⟩ :=
        node_constraints_satisfied hSat
      obtain ⟨hOldEnv, hOldTy⟩ :=
        finish_bounds hFinish hBoundarySat
      exact completeNode
        hRule hChildren hPremSat hLocalSat
        hE hB hFinish.2.1 hPremBound hLocalBound
        (envSubtype_trans hEnv hOldEnv)
        (subtype_trans hOldTy hTy)
        hStart hPrefix

theorem rawTy_prod_components
    {ν : Raw.Valuation} {T : RTy}
    {σ τ : Strictness.Ty} {u : Usage}
    (hEval : T.eval ν = .prod σ τ u) :
    ∃ A B p,
      T = .prod A B p ∧
      A.eval ν = σ ∧ B.eval ν = τ ∧ p.eval ν = u := by
  cases T with
  | int p =>
      cases hEval
  | arrow A B p =>
      cases hEval
  | prod A B p =>
      have hParts := Strictness.Ty.prod.inj hEval
      exact ⟨A, B, p, rfl, hParts.1, hParts.2.1, hParts.2.2⟩

structure ReadyPremise
    (limit : Nat) (ν : Raw.Valuation)
    (Γ : Strictness.Env) (e : Term) (τ : Strictness.Ty) where
  ctx : REnv
  ty : RTy
  constraints : UC
  derives : Derives ctx e ty constraints
  satisfies : constraints.Satisfies ν
  ctx_eval : Raw.Env.eval ν ctx = Γ
  ty_eval : ty.eval ν = τ
  ctx_below : EnvBelow limit ctx
  ty_below : TyBelow limit ty
  constraints_below : ConstraintsBelow limit constraints
  variables : VariableEnv ctx ∧ VariableTy ty

def ConstructionWitness.ready
    {start : Nat} {initial : Raw.Valuation}
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty}
    (w : ConstructionWitness start initial Γ e τ)
    {limit : Nat} (hLimit : w.stop ≤ limit) :
    ReadyPremise limit w.valuation Γ e τ where
  ctx := w.ctx
  ty := w.ty
  constraints := w.constraints
  derives := w.supported.toDerives
  satisfies := w.satisfies
  ctx_eval := w.ctx_eval
  ty_eval := w.ty_eval
  ctx_below := envBelow_mono w.ctx_below hLimit
  ty_below := tyBelow_mono w.ty_below hLimit
  constraints_below :=
    constraintsBelow_mono w.supported.constraints_below hLimit
  variables := w.supported.toDerives.boundary_variables

def ReadyPremise.revalue
    {limit : Nat} {ν ν' : Raw.Valuation}
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty}
    (v : ReadyPremise limit ν Γ e τ)
    (hAgree : AgreeBelow limit ν' ν) :
    ReadyPremise limit ν' Γ e τ where
  ctx := v.ctx
  ty := v.ty
  constraints := v.constraints
  derives := v.derives
  satisfies := satisfies_agreeBelow v.constraints_below hAgree v.satisfies
  ctx_eval := (eval_env_agreeBelow v.ctx_below hAgree).trans v.ctx_eval
  ty_eval := (eval_ty_agreeBelow v.ty_below hAgree).trans v.ty_eval
  ctx_below := v.ctx_below
  ty_below := v.ty_below
  constraints_below := v.constraints_below
  variables := v.variables

def ReadyPremise.weaken
    {lo hi : Nat} {ν : Raw.Valuation}
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty}
    (v : ReadyPremise lo ν Γ e τ)
    (hLe : lo ≤ hi) :
    ReadyPremise hi ν Γ e τ where
  ctx := v.ctx
  ty := v.ty
  constraints := v.constraints
  derives := v.derives
  satisfies := v.satisfies
  ctx_eval := v.ctx_eval
  ty_eval := v.ty_eval
  ctx_below := envBelow_mono v.ctx_below hLe
  ty_below := tyBelow_mono v.ty_below hLe
  constraints_below := constraintsBelow_mono v.constraints_below hLe
  variables := v.variables

def ReadyPremise.toPremise
    {limit : Nat} {ν : Raw.Valuation}
    {Γ : Strictness.Env} {e : Term} {τ : Strictness.Ty}
    (v : ReadyPremise limit ν Γ e τ) : Premise :=
  ⟨v.ctx, e, v.ty, v.constraints⟩

theorem buildable_two
    {Γ₁ Γ₂ : Strictness.Env}
    {e₁ e₂ : Term} {τ₁ τ₂ : Strictness.Ty}
    (h₁ : Buildable Γ₁ e₁ τ₁)
    (h₂ : Buildable Γ₂ e₂ τ₂)
    (start : Nat) (initial : Raw.Valuation) :
    ∃ (limit : Nat) (ν : Raw.Valuation),
      ∃ _ : ReadyPremise limit ν Γ₁ e₁ τ₁,
      ∃ _ : ReadyPremise limit ν Γ₂ e₂ τ₂,
        start ≤ limit ∧ AgreeBelow start ν initial := by
  obtain ⟨w₁⟩ := h₁ start initial
  obtain ⟨w₂⟩ := h₂ w₁.stop w₁.valuation
  let v₁ := w₁.revalue w₂.preservesPrefix
  exact ⟨w₂.stop, w₂.valuation,
    v₁.ready w₂.stop_ge,
    w₂.ready (Nat.le_refl w₂.stop),
    Nat.le_trans w₁.stop_ge w₂.stop_ge,
    v₁.preservesPrefix⟩

theorem setUsage_agreeBelow
    (ν : Raw.Valuation) (limit : Nat) (u : Usage) :
    AgreeBelow limit (setUsage ν limit u) ν := by
  intro i hi
  have hNe : i ≠ limit := by omega
  simp [setUsage, hNe]

theorem singleton_satisfied
    {ν : Raw.Valuation} {p q : Raw.Expr}
    (h : p.eval ν ≤ q.eval ν) :
    Raw.UseConstraints.Satisfies ν [⟨p, q⟩] := by
  intro c hc
  have hEq : c = ⟨p, q⟩ := List.mem_singleton.mp hc
  subst c
  exact h

theorem completeBinary
    {start limit : Nat} {initial ν : Raw.Valuation}
    {Γ₁ Γ₂ Γ : Strictness.Env}
    {e₁ e₂ e : Term} {τ₁ τ₂ τ : Strictness.Ty}
    (v₁ : ReadyPremise limit ν Γ₁ e₁ τ₁)
    (v₂ : ReadyPremise limit ν Γ₂ e₂ τ₂)
    {E : REnv} {B : RTy} {C₀ : UC}
    (hRule : Rule [v₁.toPremise, v₂.toPremise] e E B C₀)
    (hLocalSat : C₀.Satisfies ν)
    (hE : EnvBelow limit E)
    (hB : TyBelow limit B)
    (hBVariables : VariableTy B)
    (hLocalBound : ConstraintsBelow limit C₀)
    (hEnv : Strictness.Env.Subtype Γ (Raw.Env.eval ν E))
    (hTy : Strictness.Ty.Subtype (B.eval ν) τ)
    (hStart : start ≤ limit)
    (hPrefix : AgreeBelow start ν initial) :
    Nonempty (ConstructionWitness start initial Γ e τ) := by
  apply completeNode hRule
  · intro P hMem
    rcases List.mem_cons.mp hMem with hEq | hTail
    · subst P
      exact v₁.derives
    · have hEq : P = v₂.toPremise :=
        List.mem_singleton.mp hTail
      subst P
      exact v₂.derives
  · simpa [premiseConstraints, ReadyPremise.toPremise] using
      Raw.UseConstraints.satisfies_append.mpr
        ⟨v₁.satisfies, v₂.satisfies⟩
  · exact hLocalSat
  · exact hE
  · exact hB
  · exact hBVariables
  · simpa [premiseConstraints, ReadyPremise.toPremise] using
      constraintsBelow_append v₁.constraints_below v₂.constraints_below
  · exact hLocalBound
  · exact hEnv
  · exact hTy
  · exact hStart
  · exact hPrefix

theorem rawTy_arrow_components
    {ν : Raw.Valuation} {T : RTy}
    {σ τ : Strictness.Ty} {u : Usage}
    (hEval : T.eval ν = .arrow σ τ u) :
    ∃ A B p,
      T = .arrow A B p ∧
      A.eval ν = σ ∧ B.eval ν = τ ∧ p.eval ν = u := by
  cases T with
  | int p => cases hEval
  | prod A B p => cases hEval
  | arrow A B p =>
      have hParts := Strictness.Ty.arrow.inj hEval
      exact ⟨A, B, p, rfl, hParts.1, hParts.2.1, hParts.2.2⟩

theorem rawTy_int_component
    {ν : Raw.Valuation} {T : RTy} {u : Usage}
    (hEval : T.eval ν = .int u) :
    ∃ p, T = .int p ∧ p.eval ν = u := by
  cases T with
  | int p =>
      exact ⟨p, rfl, Strictness.Ty.int.inj hEval⟩
  | prod A B p => cases hEval
  | arrow A B p => cases hEval

theorem buildable_three
    {Γ₀ Γ₁ Γ₂ : Strictness.Env}
    {e₀ e₁ e₂ : Term} {τ₀ τ₁ τ₂ : Strictness.Ty}
    (h₀ : Buildable Γ₀ e₀ τ₀)
    (h₁ : Buildable Γ₁ e₁ τ₁)
    (h₂ : Buildable Γ₂ e₂ τ₂)
    (start : Nat) (initial : Raw.Valuation) :
    ∃ (limit : Nat) (ν : Raw.Valuation),
      ∃ _ : ReadyPremise limit ν Γ₀ e₀ τ₀,
      ∃ _ : ReadyPremise limit ν Γ₁ e₁ τ₁,
      ∃ _ : ReadyPremise limit ν Γ₂ e₂ τ₂,
        start ≤ limit ∧ AgreeBelow start ν initial := by
  obtain ⟨k, ν₀₁, r₀, r₁, hStart, hPrefix⟩ :=
    buildable_two h₀ h₁ start initial
  obtain ⟨w₂⟩ := h₂ k ν₀₁
  let v₀ := (r₀.revalue w₂.preservesPrefix).weaken w₂.stop_ge
  let v₁ := (r₁.revalue w₂.preservesPrefix).weaken w₂.stop_ge
  refine ⟨w₂.stop, w₂.valuation,
    v₀, v₁, w₂.ready (Nat.le_refl w₂.stop),
    Nat.le_trans hStart w₂.stop_ge, ?_⟩
  intro i hi
  exact
    (w₂.preservesPrefix i (Nat.lt_of_lt_of_le hi hStart)).trans
      (hPrefix i hi)

theorem completeTernary
    {start limit : Nat} {initial ν : Raw.Valuation}
    {Γ₀ Γ₁ Γ₂ Γ : Strictness.Env}
    {e₀ e₁ e₂ e : Term} {τ₀ τ₁ τ₂ τ : Strictness.Ty}
    (v₀ : ReadyPremise limit ν Γ₀ e₀ τ₀)
    (v₁ : ReadyPremise limit ν Γ₁ e₁ τ₁)
    (v₂ : ReadyPremise limit ν Γ₂ e₂ τ₂)
    {E : REnv} {B : RTy} {C₀ : UC}
    (hRule :
      Rule [v₀.toPremise, v₁.toPremise, v₂.toPremise] e E B C₀)
    (hLocalSat : C₀.Satisfies ν)
    (hE : EnvBelow limit E)
    (hB : TyBelow limit B)
    (hBVariables : VariableTy B)
    (hLocalBound : ConstraintsBelow limit C₀)
    (hEnv : Strictness.Env.Subtype Γ (Raw.Env.eval ν E))
    (hTy : Strictness.Ty.Subtype (B.eval ν) τ)
    (hStart : start ≤ limit)
    (hPrefix : AgreeBelow start ν initial) :
    Nonempty (ConstructionWitness start initial Γ e τ) := by
  apply completeNode hRule
  · intro P hMem
    rcases List.mem_cons.mp hMem with hEq | hTail
    · subst P
      exact v₀.derives
    · rcases List.mem_cons.mp hTail with hEq | hLast
      · subst P
        exact v₁.derives
      · have hEq : P = v₂.toPremise :=
          List.mem_singleton.mp hLast
        subst P
        exact v₂.derives
  · simpa [premiseConstraints, ReadyPremise.toPremise] using
      Raw.UseConstraints.satisfies_append.mpr
        ⟨v₀.satisfies,
         Raw.UseConstraints.satisfies_append.mpr
           ⟨v₁.satisfies, v₂.satisfies⟩⟩
  · exact hLocalSat
  · exact hE
  · exact hB
  · exact hBVariables
  · simpa [premiseConstraints, ReadyPremise.toPremise] using
      constraintsBelow_append v₀.constraints_below
        (constraintsBelow_append v₁.constraints_below v₂.constraints_below)
  · exact hLocalBound
  · exact hEnv
  · exact hTy
  · exact hStart
  · exact hPrefix

end Strictness.RawInference.CoreBoundary
