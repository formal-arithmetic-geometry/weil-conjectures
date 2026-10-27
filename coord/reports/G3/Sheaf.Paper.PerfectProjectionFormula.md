## What changed

Proved `AlgebraicGeometry.Scheme.PerfectProjection.baseChange_compatibility`.
The proof identifies composition of the ordinary quotient pullback maps by their
normalized adjuncts. The adjuncts are canonical constant-section maps, whose
composition is fixed by sheafification. The existing normalized compositor and
exact-derived single-functor formula give the derived quotient square. Postcomposing
the general projection base-change theorem and using exchange, tensor, and coefficient
naturality gives the forward reduction square. A private categorical calculation keeps
this assembly independent of the concrete derived constructions. The existing inverse-square lemma
then gives the inverse square without assuming exchange invertible.

The item adds four proved private mathematical helpers and private proof imports of
`ProEtaleCanonicalDerivedPullbackNormalization` and
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor`.
The public composition theorem supplies the ordinary compositor; no private witness
structure or new choice of derived composition is introduced. Scoped opacity settings
keep the chosen module operations folded during the new proofs. A matching local
section around the existing totalization proof prevents expansion of its module
pullback, direct image, adjunction, and derived-factor constructions. Explicit
category arguments keep its generic transport and total-isomorphism applications compact.
Unused and unreachable tactic linting are disabled in this file. Flexible tactic
linting is disabled locally on the proved theorem declarations to avoid scanning
their large representative tactic states. The let-to-have cleanup is disabled
to preserve the local operation abbreviations; Lean still elaborates and kernel-checks
each proof.

A private bounded metaprogram proves the final definitional conversion by structural
heterogeneous congruence and proof irrelevance. This avoids unfolding the localization
inside `Functor.map` while comparing equivalent sheafification proof arguments.
Its recursion decreases an explicit depth bound, and both proof and congruence
results are cached. It unfolds only a fixed list of this item's abbreviations.
The generated conversion proof is kernel-checked; no checking option is disabled.
Its syntax and elaborator registration are local. The implementation uses private
meta imports of `Mathlib.Lean.Meta.CongrTheorems`, `Mathlib.Tactic.Set`, and
`Mathlib.Util.TermReduce`; none is a public import.
The node's sixth proof step and dependencies now describe this argument. Existing
public signatures, definitions, and public imports are unchanged. The proof-context
change record is `coord/changes/G3-perfect-projection-quotient-composition-context.md`.

## Proved and sorry left

Closed one of the item's two original holes:
`AlgebraicGeometry.Scheme.PerfectProjection.baseChange_compatibility`.
Added zero holes and zero unfinished split-offs.

The sole retained original hole is
`AlgebraicGeometry.Scheme.PerfectProjection.perfect_projection_formula`, attached to
`lemma-weil-pbc-perfect-projection-formula`. It still states the full thick-locus,
finite-free, and locally perfect assertions. No definition contains `sorry`.

## No longer needed

The base-change argument does not need
`lem-weil-pbc-strict-perfect-ringed-pullback-model` or its module
`Sheaf.Paper.StrictPerfectRingedPullbackModel`. Its dependency is removed from the
item's node: both lower quotient reduction maps are already covered by
`reductionMap_isIso`, so no new strict-perfect model for a pulled-back coefficient
is required. No Lean file is withdrawn. Removed five unused private imports:
`Sheaf.Paper.RingedProjectionRestriction`, `Sheaf.Paper.ProjectionMateExact`,
`Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`,
`Sheaf.Paper.ProjectionFormulaTotalization`, and
`Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`.
The unfinished local-perfectness argument retains the first two nodes in the DAG.
The totalization calculation uses `tensorAdjunctionTotal_isIso` from
`ProjectionFormulaArrows`, so it also removes the unused direct dependency
`lemma-weil-pbc-projection-formula-totalization`.

## Where the brief, the DAG or earlier work was wrong

The planned base-change step did not state the needed compatibility of the uniquely
normalized quotient pullback maps with the specified canonical derived compositor.
The delivery proves this compatibility from normalized ordinary adjunctions and
constant-section maps, instead of postulating an additional coherence statement.
The planned strict-perfect pullback-model step is unnecessary for the inverse square.

For the retained theorem, the same-universe `RingedTensorCorner` exactness interface
cannot be applied directly to the original pro-etale sites, whose object and morphism
universes differ. No statement or universe was changed to bypass that mismatch.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
