## What changed

Filled the seven original holes in Sheaf.Paper.CompletedStrictOpenExchange. Exactness
is lifted pointwise to strict towers, and the fixed ordinary inverse exchange supplies
their natural isomorphism. The normalized derived exchange follows from the existing
resolving-class descent and uniqueness theorem, applied to the actual pullback pairs.
All existing declaration signatures are preserved.

Repaired the implementation of CbcStrictExchangeNormalization: its body now specializes
CategoryTheory.DerivedPairExchangeNormalization, the same representative equation
written for abstract functors and supplied universal counits. The new module contains
only this predicate; the existing descent proof remains in the assigned module.
This avoids the concrete normalization conversions that exceeded the single-file limit.
The definition change record gives both bodies verbatim and lists all 19 downstream
modules. The record is `coord/changes/H4-completed-strict-normalization-interface.md`. Targets using the definition are submitted for renewed statement review.

Private generic helpers construct a functorial flat-term K-flat tower replacement
and identify evaluation of a mapped diagram complex with mapping its evaluation.
Sheaf.Paper.CompletedOpenKFlat proves completed-coefficient open extension preserves
K-flat complexes with flat terms, using the ringed slice and ringed-topos results.

The three-module prototype compiled: CompletedOpenKFlat in 0.4 seconds,
DerivedPairExchangeNormalization in 3.0 seconds, and the assigned module in 26.9 seconds.
The final packet removes all profiling and diagnostic heartbeat settings. The separate
meaning check states the old representative equation verbatim and proves equivalence
by Iff.rfl; this compiled in 46.9 seconds. The unchanged direct consumer, CompletedRingStrictFiniteExchange, compiled against
the new interface in 13.3 seconds; no forced adaptation is needed.
Delivery performs the final clean compilation and preflight before pushing.

## Proved and sorry left

Closed seven original holes, by declaration name:

- AlgebraicGeometry.Scheme.cbcStrictOpenModule_additive
- AlgebraicGeometry.Scheme.cbcStrictOpenModule_limits
- AlgebraicGeometry.Scheme.cbcStrictOpenModule_colimits
- AlgebraicGeometry.Scheme.cbcStrictInverseLevel_naturality
- AlgebraicGeometry.Scheme.cbcStrictInverseComponent_naturality
- AlgebraicGeometry.Scheme.cbcStrictInverseModule_isIso
- AlgebraicGeometry.Scheme.cbcStrictExchange_existsUnique

Added holes: zero. No sorry remains in any of the three delivered Lean modules.
AlgebraicGeometry.Scheme.cbcOpenShriek_kFlat_of_flatTerms and every private helper
are proved. CategoryTheory.DerivedPairExchangeNormalization is a literal predicate
with no chosen data or proof hole. Seven holes closed, zero split off. Imported
existing theorems retain their existing proof status.

## No longer needed

Removed the original direct proof imports:

- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
- Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
- Sheaf.SixFunctors.OpenTensorNormalization

The proof reuses the ordinary exchange and generic normalized derived descent. It
needs no direct reconstruction of module adjunctions or their conjugation. No module
or declaration is withdrawn; these imports may remain transitive dependencies or
serve other modules. The original node had no proof_deps or proof steps to prune.
The unit route is retained. No source-library declaration or public import is changed.

## Where the brief, the DAG or earlier work was wrong

The assigned node had empty proof and proof_deps arrays; its Lean docstring supplied
the intended argument. The delivered node records the proof used.

The existing diagram K-flat replacement theorem identifies the coefficient and site
universe parameters. Its proved functorial-resolution and diagram-transposition
constructions suffice at the independent universes here, so the private resolution
uses those constructions directly.

The retained attempt had not validated the final exchange proof. Direct specialization
of the fully expanded normalization caused a kernel timeout. Factoring the equation
as a generic predicate repairs this definition interface without changing the equation,
its resolving class, comparison factors or counits. No statement is disputed or weakened.
No proof is moved into a separate module to evade the compile limit.

## New nodes

lem-cbc-completed-open-kflat attaches the proved theorem
AlgebraicGeometry.Scheme.cbcOpenShriek_kFlat_of_flatTerms in
Sheaf.Paper.CompletedOpenKFlat. This is the open-preservation step of the argument.
It requires no boundedness, nonemptiness or quasi-compactness assumption, so covers
zero and unbounded complexes, empty opens and non-quasi-compact opens.

def-cbc-derived-pair-exchange-normalization attaches
CategoryTheory.DerivedPairExchangeNormalization. It records the literal generic
representative equation, without choosing any functor or replacement and without
asserting existence for an arbitrary resolving predicate. Specialization is checked
against the old equation by definitional reflexivity. Both nodes record their sources
and the required three kinds of Mathlib search.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
