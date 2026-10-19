## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.finiteCoefficientDescentTwoColimit`
with an assembly of the existing lisse, shifted-Hom, object-descent, rational Tor-amplitude,
and canonical cocone theorems. Every original public declaration, signature and definition
body is retained. Added only private, proved helpers for the comparison of constructibility
predicates, inverse tensor comparisons and the zero-shift Hom conversions.

The constructibility comparison works on the same finite stratification. Local constant
models imply local finite presentation by the existing local-model theorem. Conversely,
`finite_lf` and `algcl_lf` from `CondensedConstructibleSerre` give local finite freeness on
Noetherian strata. A finite free module is the inverse image of the same finite free
condensed module on the point; inverse image preserves the regular module and finite sums.
The canonical invertible coefficient comparisons transport these descriptions. Applying the
result to every cohomology module yields equality of the bounded predicates. Empty schemes,
empty strata, zero-rank modules and the zero complex require no excluded cases.

Added proof imports for the existing descent declarations, local models, local triviality,
Tor bounds, Noetherianity, the shared proof API, sheaf tensor instances, additive functors,
and derived natural-isomorphism inversion.
`import all CondensedConstructibleSerre` reuses its proved private transport and local-free
helpers without changing that module. Updated the original node's proof route, and attached
the existing `constructibleCocone_isFilteredTwoColimit` declaration to its existing node.
The theorem docstring now describes this implemented route.
No new mathematical statement or new node was introduced.

Change record: `coord/changes/G7-finite-descent-local-elaboration.md` documents the
new local irreducibility attributes, private scoped opens and declaration-local
heartbeat option flagged conservatively by the static interface checker. All
transitive importers are listed there; none needs adaptation.

Validation: `lcompile.py` compiled the complete module without errors or warnings in
26.6 seconds. The three original public definition bodies and the theorem statement were
compared verbatim with the current sources and are unchanged. A current-source recompile also passed without diagnostics in 30.0 seconds.
A resumed current-source dry run passed compilation and preflight.
The final documentation and dependency-record corrections are checked again before pushing. No single-file time limit was raised. A local heartbeat
allowance covers elaboration of the four-clause theorem and its derived interfaces.

## Proved and sorry left

Original holes: 1, `AlgebraicGeometry.ProEtale.finiteCoefficientDescentTwoColimit`
(node `sk-thm-sfb-qlbar-two-colimit`). Its replacement proof contains no `sorry`.
Holes added: 0. Split off: 0. No `sorry` remains in any delivered Lean file.
The imported declarations remain the project's existing obligations; this does not claim
that their transitive axioms have all been eliminated.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Sheaf.CategoryTheory.FlatScalarTowerCoherence`
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`
- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`
- `Mathlib.CategoryTheory.Limits.Types.Filtered`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`
- `Sheaf.Paper.CoefficientHeart`
- `WeilConjectures.CategoryTheory.FilteredTwoColimit`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`

These imports are unnecessary in this file: the existing canonical cocone theorem supplies
the ordinary-category two-colimit; the shared descent interfaces supply its applications.
The finite-field and scalar-comparison definitions needed by signatures are already available
from the retained public imports. This does not assert that these modules are globally
unreachable: existing imported proofs can still use them.

The following original direct proof dependencies are no longer used here:
- `def-sfb-constructible-cocone`
- `def-sfb-constructible-extend-comp-iso`
- `def-sfb-constructible-extend-subfield`
- `def-sfb-constructible-extend-to-qlbar`
- `def-sfb-dcons-qlbar`
- `def-sfb-dcons-subfield`
- `def-sfb-derived-extend-subfield`
- `def-sfb-derived-extend-to-qlbar`
- `def-weil-closed-immersion`
- `def-weil-finite-subextension-directed-set`
- `def-weil-proper-morphism`
- `def-weil-quasi-separated-morphism`
- `lem-sfb-extend-subfield-constructible`
- `lem-sfb-extend-to-qlbar-constructible`
- `lem-sfb-flat-scalar-tower-coherence`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `lem-weil-pbc-filtered-colimit-sets-elementwise`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `sk-def-sfb-dc-setting`
- `sk-def-sfb-filtered-two-colimit`
- `sk-lem-coefficient-heart`

Their roles are supplied by the existing cocone theorem or by the direct Noetherian
local-triviality and Tor-amplitude comparisons. Statement dependencies are retained.
Removed obsolete maintainer `tool_uses` entries, preserving the order of those retained:
- `def-weil-closed-immersion`
- `def-weil-finite-subextension-directed-set`
- `def-weil-proper-morphism`
- `def-weil-quasi-separated-morphism`
- `lem-weil-pbc-conjugate-iso-unit-equation`
- `lem-weil-pbc-filtered-colimit-sets-elementwise`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `sk-def-sfb-dc-setting`

No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan's coefficient-heart invocation does not itself supply the equality between
the constant-model and ambient local-finite-presentation predicates in the Lean conclusion.
The proof now derives that equality using existing local-triviality and local-model APIs.
It is applied only on Noetherian strata: local finite presentation does not imply constant
finite models on arbitrary schemes, as the local-model module itself records.

The existing canonical cocone theorem was already proved in the source library, but its
specific existing DAG node had no `lean` attachment. Attached it instead of reconstructing
its object, surjectivity and injectivity arguments. No target statement, intermediate
statement, definition, universe or hypothesis was changed.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
