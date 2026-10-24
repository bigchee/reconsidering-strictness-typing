# Reconsidering Strictness Typing

This repository contains the Lean 4 formalization accompanying the manuscript
"Reconsidering Strictness Typing".

The formalization covers a four-annotation strictness type system for a
call-by-name language with functions, lazy pairs, integer arithmetic,
conditionals, let expressions, and recursion. The annotations are `?`, `S`,
`L`, and `⊤`.

It mechanizes the declarative typing system, its correspondence with
constraint-generating rules, and semantic and observational soundness,
including recursion. The [paper correspondence guide](PAPER_CORRESPONDENCE.md) maps the paper’s
definitions and results to Lean declarations and documents representation
differences.

The development uses **Lean 4.28.0**. Its main namespace is `Strictness`.

## Build and check

From the project root, run:

```bash
lake build Strictness
lake build Strictness.Checks
```

The main import `Strictness` includes the ordinary development. Checks are
separate and do not occur in its import closure. To print axiom dependencies
again after a cached build, run:

```bash
lake env lean Strictness/Checks/Axioms.lean
lake env lean Strictness/Checks/Compatibility.lean
```

The audited results depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms. No `sorryAx` or additional axioms
occur in the reported dependencies. The audit commands print dependencies;
they do not themselves enforce an axiom allowlist.

## Reading the development

| Directory | Contents and entry points |
|---|---|
| [Language](Strictness/Language) | Syntax, annotations, types, declarative typing and substitution |
| [Operational](Strictness/Operational) | Big-step and small-step evaluation, preservation, progress and closure-machine infrastructure |
| [Semantics](Strictness/Semantics) | Type interpretations, their properties, finite approximations and admissibility |
| [Soundness](Strictness/Soundness) | Typing-rule cases, the fundamental lemma and observational soundness |
| [Inference](Strictness/Inference) | Constraint generation, allocation and correspondence with declarative typing |
| [Compatibility](Strictness/Compatibility) | Correspondence of evaluation styles and representations of divergence |
| [Checks](Strictness/Checks) | Axiom reports and concrete typing/evaluation checks |

For soundness, start with [Fundamental.lean](Strictness/Soundness/Fundamental.lean) and [Observational.lean](Strictness/Soundness/Observational.lean).
For constraint generation, start with [Correspondence.lean](Strictness/Inference/Correspondence.lean).
The construction and machine subdirectories hold supporting proofs; their
module headers explain the role of each component.

## Correspondence with the paper

The [complete correspondence table](PAPER_CORRESPONDENCE.md) lists the
paper's definitions, semantic lemmas, fundamental lemma, operational
consequences and constraint-generation results, with Lean declarations and
source links. Representation notes identify the implementation of the
paper's semantic typing and irreducibility notation.

## Representation choices

Terms use De Bruijn indices. Pairs retain their components and lambdas retain
their bodies without evaluation. Arithmetic operators have total integer
interpretations and evaluate both operands from left to right. An exposed
`E[err]` is a terminal error observation of source reduction.

Internally, the soundness proof uses big-step value and error observations.
[Operational correspondence](Strictness/Compatibility/Operational.lean) identifies these with finite and infinite source reductions;
[semantic correspondence](Strictness/Compatibility/Semantics.lean) identifies the resulting type interpretations.

Finite approximations use an auxiliary `.omega` marker.
[The representation bridge](Strictness/Compatibility/Omega/Approximation.lean) justifies replacing it by the source loop `.fix (.var 0)`, including in
retained subterms and approximation sequences. Details and theorem entry
points are documented in the compatibility modules.
