import Strictness.Inference.CoreBoundaryConstraints

namespace Strictness.RawInference.CoreBoundary

open Raw

/-- Number of annotation positions, including annotations inside arrows. -/
def annotationCount : Strictness.Ty → Nat
  | .int _ => 1
  | .prod A B _ | .arrow A B _ =>
      1 + annotationCount A + annotationCount B

/-- Allocate the outer annotation first, then the two component types. -/
def allocatedTy (start : Nat) : Strictness.Ty → RTy
  | .int _ => .int (.var start)
  | .prod A B _ =>
      .prod
        (allocatedTy (start + 1) A)
        (allocatedTy (start + 1 + annotationCount A) B)
        (.var start)
  | .arrow A B _ =>
      .arrow
        (allocatedTy (start + 1) A)
        (allocatedTy (start + 1 + annotationCount A) B)
        (.var start)

/-- Values required of the common valuation on an allocated type. -/
def RealizesTy
    (ν : Raw.Valuation) (start : Nat) : Strictness.Ty → Prop
  | .int u => ν start = u
  | .prod A B u | .arrow A B u =>
      ν start = u ∧
      RealizesTy ν (start + 1) A ∧
      RealizesTy ν (start + 1 + annotationCount A) B

theorem allocatedTy_variables
    (A : Strictness.Ty) (start : Nat) :
    VariableTy (allocatedTy start A) := by
  induction A generalizing start with
  | int u =>
      trivial
  | prod A B u ihA ihB =>
      exact ⟨ihA _, ihB _, True.intro⟩
  | arrow A B u ihA ihB =>
      exact ⟨ihA _, ihB _, True.intro⟩

/-- An agreeing valuation recovers the original concrete type. -/
theorem allocatedTy_eval
    {ν : Raw.Valuation}
    (A : Strictness.Ty) (start : Nat)
    (hν : RealizesTy ν start A) :
    (allocatedTy start A).eval ν = A := by
  induction A generalizing start with
  | int u =>
      change Strictness.Ty.int (ν start) = .int u
      rw [hν]
  | prod A B u ihA ihB =>
      rcases hν with ⟨hu, hA, hB⟩
      simp only [allocatedTy, Raw.Ty.eval, Raw.Expr.eval,
        hu, ihA _ hA, ihB _ hB]
  | arrow A B u ihA ihB =>
      rcases hν with ⟨hu, hA, hB⟩
      simp only [allocatedTy, Raw.Ty.eval, Raw.Expr.eval,
        hu, ihA _ hA, ihB _ hB]

/-- A variable belongs to the half-open interval [lo, hi). -/
def ExprInRange (lo hi : Nat) : Raw.Expr → Prop
  | .var a => lo ≤ a ∧ a < hi
  | _ => False

def TyInRange (lo hi : Nat) : RTy → Prop
  | .int u => ExprInRange lo hi u
  | .prod A B u | .arrow A B u =>
      TyInRange lo hi A ∧
      TyInRange lo hi B ∧
      ExprInRange lo hi u

theorem exprInRange_weaken
    {p : Raw.Expr} {lo hi lo' hi' : Nat}
    (h : ExprInRange lo hi p)
    (hLo : lo' ≤ lo)
    (hHi : hi ≤ hi') :
    ExprInRange lo' hi' p := by
  cases p with
  | var a =>
      change lo ≤ a ∧ a < hi at h
      change lo' ≤ a ∧ a < hi'
      rcases h with ⟨hLower, hUpper⟩
      exact ⟨Nat.le_trans hLo hLower,
        Nat.lt_of_lt_of_le hUpper hHi⟩
  | lit u => exact False.elim h
  | add p q => exact False.elim h
  | meet p q => exact False.elim h
  | join p q => exact False.elim h
  | scale p q => exact False.elim h

theorem tyInRange_weaken
    {A : RTy} {lo hi lo' hi' : Nat}
    (h : TyInRange lo hi A)
    (hLo : lo' ≤ lo)
    (hHi : hi ≤ hi') :
    TyInRange lo' hi' A := by
  induction A with
  | int u =>
      exact exprInRange_weaken h hLo hHi
  | prod A B u ihA ihB =>
      exact ⟨ihA h.1, ihB h.2.1,
        exprInRange_weaken h.2.2 hLo hHi⟩
  | arrow A B u ihA ihB =>
      exact ⟨ihA h.1, ihB h.2.1,
        exprInRange_weaken h.2.2 hLo hHi⟩

/-- Allocation uses only its reserved interval. -/
theorem allocatedTy_range
    (A : Strictness.Ty) (start : Nat) :
    TyInRange start (start + annotationCount A)
      (allocatedTy start A) := by
  induction A generalizing start with
  | int u =>
      change start ≤ start ∧ start < start + 1
      omega
  | prod A B u ihA ihB =>
      change
        TyInRange start (start + (1 + annotationCount A + annotationCount B))
          (allocatedTy (start + 1) A) ∧
        TyInRange start (start + (1 + annotationCount A + annotationCount B))
          (allocatedTy (start + 1 + annotationCount A) B) ∧
        (start ≤ start ∧
          start < start + (1 + annotationCount A + annotationCount B))
      constructor
      · apply tyInRange_weaken (ihA (start + 1)) <;> omega
      · constructor
        · apply tyInRange_weaken
            (ihB (start + 1 + annotationCount A)) <;> omega
        · omega
  | arrow A B u ihA ihB =>
      change
        TyInRange start (start + (1 + annotationCount A + annotationCount B))
          (allocatedTy (start + 1) A) ∧
        TyInRange start (start + (1 + annotationCount A + annotationCount B))
          (allocatedTy (start + 1 + annotationCount A) B) ∧
        (start ≤ start ∧
          start < start + (1 + annotationCount A + annotationCount B))
      constructor
      · apply tyInRange_weaken (ihA (start + 1)) <;> omega
      · constructor
        · apply tyInRange_weaken
            (ihB (start + 1 + annotationCount A)) <;> omega
        · omega

def envAnnotationCount : Strictness.Env → Nat
  | [] => 0
  | A :: Γ => annotationCount A + envAnnotationCount Γ

def allocatedEnv (start : Nat) : Strictness.Env → REnv
  | [] => []
  | A :: Γ =>
      allocatedTy start A ::
        allocatedEnv (start + annotationCount A) Γ

def RealizesEnv
    (ν : Raw.Valuation) (start : Nat) : Strictness.Env → Prop
  | [] => True
  | A :: Γ =>
      RealizesTy ν start A ∧
      RealizesEnv ν (start + annotationCount A) Γ

theorem allocatedEnv_variables
    (Γ : Strictness.Env) (start : Nat) :
    VariableEnv (allocatedEnv start Γ) := by
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
        exact allocatedTy_variables A start
      · exact ih _ B hTail

theorem allocatedEnv_eval
    {ν : Raw.Valuation}
    (Γ : Strictness.Env) (start : Nat)
    (hν : RealizesEnv ν start Γ) :
    (allocatedEnv start Γ).eval ν = Γ := by
  induction Γ generalizing start with
  | nil =>
      rfl
  | cons A Γ ih =>
      rcases hν with ⟨hA, hΓ⟩
      simp only [allocatedEnv, Raw.Env.eval,
        allocatedTy_eval A start hA, ih _ hΓ]

/-- Update one annotation variable. -/
def setUsage
    (ν : Raw.Valuation) (a : Nat) (u : Usage) : Raw.Valuation :=
  fun i => if i = a then u else ν i

/-- Write the concrete annotations into the interval reserved by allocatedTy. -/
def writeTy :
    Strictness.Ty → Raw.Valuation → Nat → Raw.Valuation
  | .int u, ν, start =>
      setUsage ν start u
  | .prod A B u, ν, start =>
      writeTy B
        (writeTy A (setUsage ν start u) (start + 1))
        (start + 1 + annotationCount A)
  | .arrow A B u, ν, start =>
      writeTy B
        (writeTy A (setUsage ν start u) (start + 1))
        (start + 1 + annotationCount A)

/-- Writing a type preserves every variable outside its reserved interval. -/
theorem writeTy_outside
    (A : Strictness.Ty)
    (ν : Raw.Valuation) (start i : Nat)
    (hOutside : i < start ∨ start + annotationCount A ≤ i) :
    writeTy A ν start i = ν i := by
  induction A generalizing ν start i with
  | int u =>
      have hNe : i ≠ start := by
        simp only [annotationCount] at hOutside
        omega
      simp [writeTy, setUsage, hNe]

  | prod A B u ihA ihB
  | arrow A B u ihA ihB =>
      have hOutsideB :
          i < start + 1 + annotationCount A ∨
          start + 1 + annotationCount A + annotationCount B ≤ i := by
        simp only [annotationCount] at hOutside
        omega
      have hOutsideA :
          i < start + 1 ∨ start + 1 + annotationCount A ≤ i := by
        simp only [annotationCount] at hOutside
        omega
      have hNe : i ≠ start := by
        simp only [annotationCount] at hOutside
        omega
      change
        writeTy B
          (writeTy A (setUsage ν start u) (start + 1))
          (start + 1 + annotationCount A) i = ν i
      rw [ihB _ _ _ hOutsideB, ihA _ _ _ hOutsideA]
      simp [setUsage, hNe]

/-- Realization depends only on values inside the allocated interval. -/
theorem realizesTy_congr
    {ν ν' : Raw.Valuation}
    (A : Strictness.Ty) (start : Nat)
    (hReal : RealizesTy ν start A)
    (hAgree :
      ∀ i, start ≤ i → i < start + annotationCount A →
        ν' i = ν i) :
    RealizesTy ν' start A := by
  induction A generalizing start with
  | int u =>
      change ν' start = u
      rw [hAgree start (Nat.le_refl _) (by
        simp only [annotationCount]
        omega)]
      exact hReal

  | prod A B u ihA ihB
  | arrow A B u ihA ihB =>
      rcases hReal with ⟨hu, hA, hB⟩
      change
        ν' start = u ∧
        RealizesTy ν' (start + 1) A ∧
        RealizesTy ν' (start + 1 + annotationCount A) B
      constructor
      · rw [hAgree start (Nat.le_refl _) (by
          simp only [annotationCount]
          omega)]
        exact hu
      · constructor
        · apply ihA _ hA
          intro i hLo hHi
          apply hAgree i
          · omega
          · simp only [annotationCount]
            omega
        · apply ihB _ hB
          intro i hLo hHi
          apply hAgree i
          · omega
          · simp only [annotationCount]
            omega

/-- Writing a type establishes all of its required annotation values. -/
theorem writeTy_realizes
    (A : Strictness.Ty)
    (ν : Raw.Valuation) (start : Nat) :
    RealizesTy (writeTy A ν start) start A := by
  induction A generalizing ν start with
  | int u =>
      simp [RealizesTy, writeTy, setUsage]

  | prod A B u ihA ihB
  | arrow A B u ihA ihB =>
      let ν₀ := setUsage ν start u
      let νA := writeTy A ν₀ (start + 1)
      let νB := writeTy B νA (start + 1 + annotationCount A)

      have hA : RealizesTy νA (start + 1) A :=
        ihA ν₀ (start + 1)
      have hB :
          RealizesTy νB (start + 1 + annotationCount A) B :=
        ihB νA (start + 1 + annotationCount A)

      have hRootA : νA start = ν₀ start :=
        writeTy_outside A ν₀ (start + 1) start
          (Or.inl (by omega))
      have hRootB : νB start = νA start :=
        writeTy_outside B νA
          (start + 1 + annotationCount A) start
          (Or.inl (by omega))

      have hAPreserved : RealizesTy νB (start + 1) A := by
        apply realizesTy_congr A (start + 1) hA
        intro i hLo hHi
        exact writeTy_outside B νA
          (start + 1 + annotationCount A) i
          (Or.inl (by omega))

      change
        νB start = u ∧
        RealizesTy νB (start + 1) A ∧
        RealizesTy νB (start + 1 + annotationCount A) B
      constructor
      · rw [hRootB, hRootA]
        simp [ν₀, setUsage]
      · exact ⟨hAPreserved, hB⟩

/-- Allocation followed by writing recovers the original concrete type. -/
theorem allocatedTy_eval_writeTy
    (A : Strictness.Ty)
    (ν : Raw.Valuation) (start : Nat) :
    (allocatedTy start A).eval (writeTy A ν start) = A := by
  exact allocatedTy_eval A start (writeTy_realizes A ν start)

/-- Write an environment into consecutive annotation intervals. -/
def writeEnv :
    Strictness.Env → Raw.Valuation → Nat → Raw.Valuation
  | [], ν, _ => ν
  | A :: Γ, ν, start =>
      writeEnv Γ (writeTy A ν start)
        (start + annotationCount A)

theorem writeEnv_outside
    (Γ : Strictness.Env)
    (ν : Raw.Valuation) (start i : Nat)
    (hOutside : i < start ∨ start + envAnnotationCount Γ ≤ i) :
    writeEnv Γ ν start i = ν i := by
  induction Γ generalizing ν start i with
  | nil =>
      rfl
  | cons A Γ ih =>
      have hOutsideTail :
          i < start + annotationCount A ∨
          start + annotationCount A + envAnnotationCount Γ ≤ i := by
        simp only [envAnnotationCount] at hOutside
        omega
      have hOutsideHead :
          i < start ∨ start + annotationCount A ≤ i := by
        simp only [envAnnotationCount] at hOutside
        omega
      change
        writeEnv Γ (writeTy A ν start)
          (start + annotationCount A) i = ν i
      rw [ih _ _ _ hOutsideTail]
      exact writeTy_outside A ν start i hOutsideHead

theorem realizesEnv_congr
    {ν ν' : Raw.Valuation}
    (Γ : Strictness.Env) (start : Nat)
    (hReal : RealizesEnv ν start Γ)
    (hAgree :
      ∀ i, start ≤ i → i < start + envAnnotationCount Γ →
        ν' i = ν i) :
    RealizesEnv ν' start Γ := by
  induction Γ generalizing start with
  | nil =>
      trivial
  | cons A Γ ih =>
      rcases hReal with ⟨hA, hΓ⟩
      change
        RealizesTy ν' start A ∧
        RealizesEnv ν' (start + annotationCount A) Γ
      constructor
      · apply realizesTy_congr A start hA
        intro i hLo hHi
        apply hAgree i hLo
        simp only [envAnnotationCount]
        omega
      · apply ih _ hΓ
        intro i hLo hHi
        apply hAgree i
        · omega
        · simp only [envAnnotationCount]
          omega

theorem writeEnv_realizes
    (Γ : Strictness.Env)
    (ν : Raw.Valuation) (start : Nat) :
    RealizesEnv (writeEnv Γ ν start) start Γ := by
  induction Γ generalizing ν start with
  | nil =>
      trivial
  | cons A Γ ih =>
      let νA := writeTy A ν start
      let νΓ := writeEnv Γ νA (start + annotationCount A)

      have hA : RealizesTy νA start A :=
        writeTy_realizes A ν start
      have hΓ :
          RealizesEnv νΓ (start + annotationCount A) Γ :=
        ih νA (start + annotationCount A)

      have hAPreserved : RealizesTy νΓ start A := by
        apply realizesTy_congr A start hA
        intro i hLo hHi
        exact writeEnv_outside Γ νA
          (start + annotationCount A) i
          (Or.inl hHi)

      change RealizesTy νΓ start A ∧
        RealizesEnv νΓ (start + annotationCount A) Γ
      exact ⟨hAPreserved, hΓ⟩

theorem allocatedEnv_eval_writeEnv
    (Γ : Strictness.Env)
    (ν : Raw.Valuation) (start : Nat) :
    (allocatedEnv start Γ).eval (writeEnv Γ ν start) = Γ := by
  exact allocatedEnv_eval Γ start (writeEnv_realizes Γ ν start)

/--
Reserve the environment first, then the result type.
The resulting valuation realizes both simultaneously.
-/
def writeBoundary
    (Γ : Strictness.Env) (T : Strictness.Ty)
    (ν : Raw.Valuation) (start : Nat) : Raw.Valuation :=
  writeTy T (writeEnv Γ ν start)
    (start + envAnnotationCount Γ)

theorem writeBoundary_realizes
    (Γ : Strictness.Env) (T : Strictness.Ty)
    (ν : Raw.Valuation) (start : Nat) :
    RealizesEnv (writeBoundary Γ T ν start) start Γ ∧
    RealizesTy (writeBoundary Γ T ν start)
      (start + envAnnotationCount Γ) T := by
  constructor
  · apply realizesEnv_congr Γ start (writeEnv_realizes Γ ν start)
    intro i hLo hHi
    exact writeTy_outside T (writeEnv Γ ν start)
      (start + envAnnotationCount Γ) i
      (Or.inl hHi)
  · exact writeTy_realizes T (writeEnv Γ ν start)
      (start + envAnnotationCount Γ)

theorem allocatedBoundary_eval
    (Γ : Strictness.Env) (T : Strictness.Ty)
    (ν : Raw.Valuation) (start : Nat) :
    (allocatedEnv start Γ).eval (writeBoundary Γ T ν start) = Γ ∧
    (allocatedTy (start + envAnnotationCount Γ) T).eval
      (writeBoundary Γ T ν start) = T := by
  obtain ⟨hΓ, hT⟩ := writeBoundary_realizes Γ T ν start
  exact ⟨allocatedEnv_eval Γ start hΓ,
    allocatedTy_eval T (start + envAnnotationCount Γ) hT⟩

theorem writeBoundary_outside
    (Γ : Strictness.Env) (T : Strictness.Ty)
    (ν : Raw.Valuation) (start i : Nat)
    (hOutside :
      i < start ∨
      start + envAnnotationCount Γ + annotationCount T ≤ i) :
    writeBoundary Γ T ν start i = ν i := by
  have hOutsideTy :
      i < start + envAnnotationCount Γ ∨
      start + envAnnotationCount Γ + annotationCount T ≤ i := by
    omega
  have hOutsideEnv :
      i < start ∨ start + envAnnotationCount Γ ≤ i := by
    omega
  unfold writeBoundary
  rw [writeTy_outside T _ _ i hOutsideTy]
  exact writeEnv_outside Γ ν start i hOutsideEnv

end Strictness.RawInference.CoreBoundary
