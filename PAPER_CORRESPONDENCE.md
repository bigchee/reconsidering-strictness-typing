# Correspondence with the paper

This table maps the paper's definitions and results to Lean declarations and source modules. Entries are grouped by mathematical content rather than section numbers.
They identify the main declaration for each result; rule-specific proof steps are reached through those declarations.

Unless otherwise indicated, declaration names omit the namespace prefix `Strictness`. The type `Usage` is defined at the root namespace, and its operations have names such as `Usage.add` and `Usage.scale`. Nested namespace prefixes, such as `RawInference.CoreBoundary`, are shown explicitly.

## Definitions and rules

| Paper reference | Definition or statement | Lean declarations | Module |
|---|---|---|---|
| Sections 2, 4.1 | Source and semantic terms; arithmetic operators $\mathrm{op}$ | `Term`, `PrimOp`, `PrimOp.eval` | [Syntax.lean](Strictness/Language/Syntax.lean) |
| Section 2; Appendix A | Values and finite value/error observations (see representation notes) | `Value`, `Eval`, `EvalErr` | [BigStep.lean](Strictness/Operational/BigStep.lean) |
| Section 2; Appendix D | Source reduction $\to$, $\to^*$, and $\mathrm{Demand}_x$ | `Step`, `Steps`, `EvalCtx.Demanded` | [SmallStep.lean](Strictness/Operational/SmallStep.lean) |
| Section 2; Appendix D | $\mathrm{ErrorFocus}$, $\mathrm{Terminal}$, and infinite reduction $\Uparrow$ | `ErrorFocused`, `SmallStepTerminal`, `InfiniteSteps` | [Observations.lean](Strictness/Operational/Observations.lean), [Progress.lean](Strictness/Operational/Progress.lean), [SmallStep.lean](Strictness/Operational/SmallStep.lean) |
| Section 3 | Attributes $\{?,S,L,\top\}$ and operations $\le,+,\sqcap,\sqcup,*$ | `Usage`, `Usage.Le`, `Usage.add`, `Usage.meet`, `Usage.join`, `Usage.scale` | [Usage.lean](Strictness/Language/Usage.lean) |
| Sections 3, 4.1 | Annotated types, erasure $\lfloor\tau\rfloor$, and outer reannotation $\sigma^u$ | `Ty`, `SimpleTy`, `Ty.erase`, `Ty.reannotate` | [Type.lean](Strictness/Language/Type.lean) |
| Section 3 | Type and context operations $+, *, \sqcap$ and $\mathrm{Lazy}$; type raising $\rho \uparrow S$ | `Ty.scale`, `Ty.plus`, `Ty.cap`, `Ty.IsLazy`, `Ty.raiseStrict`, `Env.scale`, `Env.plus`, `Env.cap`, `Env.IsLazy` | [Type.lean](Strictness/Language/Type.lean), [Environment.lean](Strictness/Language/Environment.lean) |
| Section 3 | Subtyping and declarative typing $\Gamma\vdash e:\tau$, including T-Sub | `Ty.Subtype`, `Env.Subtype`, `Typing` | [Type.lean](Strictness/Language/Type.lean), [Environment.lean](Strictness/Language/Environment.lean), [Typing.lean](Strictness/Language/Typing.lean) |
| Section 3.5; Figure 6 | Constraint-generating typing rules (including context/result subsumption) | `RawInference.CoreBoundary.Rule`, `RawInference.CoreBoundary.Finish`, `RawInference.CoreBoundary.Derives` | [CoreBoundary.lean](Strictness/Inference/CoreBoundary.lean) |
| Section 4.1; Lemma D.4 | Simple typing $\Gamma\vdash_{\mathrm{st}}M:A$ | `Term.HasType` | [SimpleTyping.lean](Strictness/Language/SimpleTyping.lean) |
| Section 4.1 | $\mathcal U_A$, $\mathcal O_A$, and the auxiliary numeral set | `AllTerms`, `DivergentTerms`, `NumeralTerms`, `SmallStep.DivergentTerms`, `SmallStep.NumeralTerms` | [Interpretation.lean](Strictness/Semantics/Interpretation.lean), [SmallStep.lean](Strictness/Semantics/SmallStep.lean) |
| Section 4.1; Figure 5 | Pair and function constructions $\mathcal P_{A,B}$, $\mathcal F_{A,B}$ (see representation notes) | `PairTerms`, `FunctionTerms`, `StrictFunctionTerms` | [Interpretation.lean](Strictness/Semantics/Interpretation.lean) |
| Section 4.1; Figure 5 | Type interpretations $V(\tau)$ and $D(\tau)$ | `LogicalModel.acceptable`, `LogicalModel.divergentSide`, `V`, `D`, `SmallStep.V`, `SmallStep.D` | [LogicalRelation.lean](Strictness/Semantics/LogicalRelation.lean), [Interpretation.lean](Strictness/Semantics/Interpretation.lean), [SmallStep.lean](Strictness/Semantics/SmallStep.lean) |
| Section 4.1 | Closing-substitution conditions $\eta\models_V\Gamma$, $\eta\models_D\Gamma$ | `Valid`, `SatisfiesD` | [SemanticEnvironment.lean](Strictness/Semantics/SemanticEnvironment.lean) |
| Section 4.2; Lemma 4.5 | Finite unfoldings $M_n$; generalized unfolding families used in the proof | `Term.fixApprox`, `UnfoldFamily`, `UnfoldValueFamily`, `Cofinal` | [FixApproximation.lean](Strictness/Semantics/FixApproximation.lean), [FiniteUnfolding.lean](Strictness/Semantics/FiniteUnfolding.lean), [UnfoldingAdmissibility.lean](Strictness/Semantics/UnfoldingAdmissibility.lean) |
| Appendix D | Finite-observation equivalence $M\simeq_A N$ | `RawEq`, `SemEq` | [SemanticEquivalence.lean](Strictness/Semantics/SemanticEquivalence.lean) |

## Main results

| Paper reference | Statement | Lean declarations | Module |
|---|---|---|---|
| Section 3.5; Figure 6 | Correspondence of declarative and constraint-generating typing | `RawInference.CoreBoundary.typing_correspondence` | [Correspondence.lean](Strictness/Inference/Correspondence.lean) |
| Theorem 4.1 (1) | Observational soundness: $u=S$ | `strict_smallStep_terminal_iff_demands` | [Observational.lean](Strictness/Soundness/Observational.lean) |
| Theorem 4.1 (2) | Observational soundness: $u=L$ | `lazy_smallStep` | [FiniteObservations.lean](Strictness/Soundness/FiniteObservations.lean) |
| Theorem 4.1 (3) | Observational soundness: $u=\top$ | `top_open_smallStep` | [Observational.lean](Strictness/Soundness/Observational.lean) |
| Lemma 4.2 | Reformulation of Theorem 4.1 by substitution observations | `strict_semantic`, `lazy_no_error`, `top_semantic` | [Semantic.lean](Strictness/Soundness/Semantic.lean) |
| Lemma 4.3 | Subtyping and composition: subtyping | `semantic_subtype` | [SemanticSubtype.lean](Strictness/Semantics/SemanticSubtype.lean) |
| Lemma 4.3 | Subtyping and composition: $+$ and $\sqcap$ | `semantic_plus_V`, `semantic_plus_D`, `semantic_cap` | [SemanticPlus.lean](Strictness/Semantics/SemanticPlus.lean), [SemanticPlusD.lean](Strictness/Semantics/SemanticPlusD.lean), [SemanticCap.lean](Strictness/Semantics/SemanticCap.lean) |
| Lemma 4.4 | Structural scaling: $u=?$ | `LogicalModel.acceptable_unknown_scale`, `LogicalModel.divergentSide_unknown_scale` | [LogicalRelation.lean](Strictness/Semantics/LogicalRelation.lean) |
| Lemma 4.4 | Structural scaling: $u=S$ | `LogicalModel.acceptable_strict_scale`, `LogicalModel.divergentSide_strict_scale` | [LogicalRelation.lean](Strictness/Semantics/LogicalRelation.lean) |
| Lemma 4.4 | Structural scaling: $u=L$ | `LogicalModel.acceptable_lazy_scale`, `LogicalModel.divergentSide_lazy_scale` | [LogicalRelation.lean](Strictness/Semantics/LogicalRelation.lean) |
| Lemma 4.4 | Structural scaling: $u=\top$ | `LogicalModel.acceptable_top_scale`, `LogicalModel.divergentSide_top_scale` | [LogicalRelation.lean](Strictness/Semantics/LogicalRelation.lean) |
| Lemma 4.5 | Admissibility of the interpretations (finite-unfolding sequence) | `fixApprox_mem_V_of_cofinal`, `fixApprox_mem_D_of_cofinal` | [FixAdmissibility.lean](Strictness/Semantics/FixAdmissibility.lean) |
| Lemma 4.6 | Fundamental Lemma | `fundamental` | [Fundamental.lean](Strictness/Soundness/Fundamental.lean) |

## Appendix results

| Paper reference | Statement | Lean declarations | Module |
|---|---|---|---|
| Lemma D.1 | Context transport | `valid_of_env_subtype`, `satisfiesD_of_env_subtype`, `valid_plus_split_of_semantic`, `satisfiesD_plus_split_of_semantic`, `valid_cap_split`, `satisfiesD_cap_split` | [EnvironmentLemmas.lean](Strictness/Semantics/EnvironmentLemmas.lean), [SemanticPlusEnv.lean](Strictness/Semantics/SemanticPlusEnv.lean), [SemanticCap.lean](Strictness/Semantics/SemanticCap.lean) |
| Lemma D.2 | Raising $\rho\uparrow S$ and recursive contexts | `V_raiseStrict`, `valid_of_fix_context`, `fix_context_eq_of_not_strict` | [FixTypeOperations.lean](Strictness/Semantics/FixTypeOperations.lean), [FixEnvironment.lean](Strictness/Semantics/FixEnvironment.lean) |
| Lemma D.3 | Projection | `V_proj_left`, `V_proj_right`, `D_proj_left`, `D_proj_right` | [SemanticPairProjection.lean](Strictness/Semantics/SemanticPairProjection.lean) |
| Lemma D.4 | Erasure and closing substitution | `typing_erasure`, `Term.hasType_apply`, `Valid.simpleValid_erased` | [Typing.lean](Strictness/Language/Typing.lean), [SimpleSubstitution.lean](Strictness/Language/SimpleSubstitution.lean), [SemanticSubstitution.lean](Strictness/Semantics/SemanticSubstitution.lean) |
| Lemma D.5 | Semantic compatibility under $\simeq_A$ | `semantic_equiv_VD`, `semEq_beta`, `semEq_let` | [SemanticEquivalence.lean](Strictness/Semantics/SemanticEquivalence.lean) |
| Lemma D.6 | Semantic test terms: $\Omega$, $\sigma^S$, $\sigma^L$, $\sigma^\top$ | `omega_mem_D_reannotate_strict`, `V_reannotate_lazy_eq_allTerms`, `V_reannotate_top_eq_allTerms`, `D_reannotate_top_eq_allTerms` | [SemanticLemmas.lean](Strictness/Semantics/SemanticLemmas.lean) |
| Lemma D.7 | Closing substitutions and reduction | `steps_apply_closed`, `steps_eval`, `steps_evalErr`, `steps_demanded_err_evalErr`, `steps_int_eval_of_closed_images`, `steps_errorFocused_evalErr_of_closed_images` | [SmallStepSubstitution.lean](Strictness/Operational/SmallStepSubstitution.lean), [OperationalBase.lean](Strictness/Compatibility/OperationalBase.lean), [Observations.lean](Strictness/Operational/Observations.lean) |
| Lemma D.8 | Open simple-type preservation and progress | `steps_hasType_open`, `typed_progress_open`, `typed_open_int_terminal_forms`, `demanded_smallStep_terminal` | [Preservation.lean](Strictness/Operational/Preservation.lean), [Progress.lean](Strictness/Operational/Progress.lean) |
| Lemma D.9 | Infinite reduction from persistent progress | `infiniteSteps_of_reachable_can_step`, `goodDivergingInt_infiniteSteps` | [Properties.lean](Strictness/Operational/Properties.lean) |

## Supporting Lean results

| Related paper content | Supporting result | Lean declarations | Module |
|---|---|---|---|
| Section 3.5 | Typing correspondence with certified constraint form | `RawInference.CoreBoundary.typing_correspondence_dualDefinite` | [Correspondence.lean](Strictness/Inference/Correspondence.lean) |
| Section 3.5 | Variable-left and dual-definite generated constraints | `RawInference.CoreBoundary.Derives.constraints_variableDefinite`, `RawInference.CoreBoundary.Derives.constraints_dualDefinite` | [CoreBoundaryConstraints.lean](Strictness/Inference/CoreBoundaryConstraints.lean) |
| Section 4 | Basic properties of $V$, $D$, and $\mathcal O_A$ | `D_subset_V`, `V_subset_allTerms`, `D_empty_iff_lazy`, `divergentTerms_subset_V`, `divergentTerms_subset_D_of_not_lazy` | [SemanticBasic.lean](Strictness/Semantics/SemanticBasic.lean), [SemanticLemmas.lean](Strictness/Semantics/SemanticLemmas.lean) |
| Lemma 4.5 | Finite observations of generalized unfolding families | `unfoldFamily_eval`, `unfoldFamily_evalErr` | [FiniteUnfolding.lean](Strictness/Semantics/FiniteUnfolding.lean) |
| Lemma 4.5 | Admissibility for generalized unfolding families | `semantic_unfold_admissible` | [FixAdmissibility.lean](Strictness/Semantics/FixAdmissibility.lean) |

## Representation notes

### Variables, contexts, and typing

Terms use de Bruijn indices and contexts are lists of annotated types.
The declarative judgment, including the separate T-Sub rule, is `Typing`;
its fundamental lemma is `fundamental`. The constraint-generating judgment
is `RawInference.CoreBoundary.Derives`. The names `Rule` and `Finish` describe
its implementation structure, not additional paper judgments.

### Evaluation and type interpretations

The proof uses the separate big-step judgments `Eval` and `EvalErr` for
finite value and error observations. The paper's operational definitions
are related to these by `eval_iff_steps_value`, `evalErr_iff_steps_error`,
and `diverges_iff_infiniteSteps` in
[Compatibility/Operational.lean](Strictness/Compatibility/Operational.lean).
The divergence equivalence assumes a closed, simply typed term.

The unqualified `V` and `D` are the internal big-step interpretations.
`SmallStep.V` and `SmallStep.D` use source reductions.
`SmallStep.V_eq` and `SmallStep.D_eq` in
[Compatibility/Semantics.lean](Strictness/Compatibility/Semantics.lean)
prove equality of the interpretations. The numeral set is an auxiliary
component of the Lean logical model; the paper uses the corresponding
integer and evaluation notation directly.

### Function constructions

The paper's $\mathcal F_{A,B}(X,Y)$ is presentation notation.
Its two occurrences in the $V$-arrow intersection are stored together by
`FunctionTerms`. For the $D$ interpretation of an $S$-annotated arrow,
`StrictFunctionTerms` additionally retains membership in the $V$-arrow set.
The paper omits this redundant condition: its implication from the other
function obligations follows from `D_subset_V`.

### Closing substitutions and semantic typing

`Valid Γ ρ` expresses the $V$ conditions together with closure of the
substitution; `SatisfiesD Γ ρ` supplies the existential $D$ witness.
Thus the paper's $\eta\models_D\Gamma$ corresponds to their conjunction,
not to `SatisfiesD` alone. The theorem `fundamental` states both semantic
typing conclusions explicitly for every substitution rather than using
a separate notation for $\Gamma\models e:\tau$.

### Divergence and finite unfoldings

In the paper, $\Omega$ abbreviates $\mu z.z$. Lean retains a separate
`.omega` constructor for finite approximations. The representation bridge
in [Compatibility/Omega](Strictness/Compatibility/Omega) relates this marker
to the source loop `.fix (.var 0)`, including retained subterms.
In particular, `fixApprox_source_semantic_VD` and
`fixApprox_source_smallStep_VD` in
[Approximation.lean](Strictness/Compatibility/Omega/Approximation.lean)
preserve semantic membership when the marker is expanded in approximation
sequences. `UnfoldFamily`, `UnfoldValueFamily`, and cofinality support the
generalized proof of Lemma 4.5; the finite-sequence corollaries are the
principal entries in the table.

### Demand and irreducibility

`EvalCtx.Demanded` represents the paper's $\mathrm{Demand}_x$ for the
distinguished variable, represented by index zero. `SmallStepTerminal`
means absence of an outgoing source step, matching the paper's
$\mathrm{Terminal}$ predicate. In Theorem 4.1 (1), the equivalence is about
a reached state; it does not assert that evaluation reaches such a state.
