## What changed

`Sheaf.Paper.FiniteQuotientFiniteModuleCohomology` now proves its published statement
unchanged from the coefficient-filtration distinguished triangle and a finite-coefficient
heart closure theorem. The Lean proof maps the long exact homology short complex through
exact slice restriction, deduces middle-term vanishing from zero outer terms, proves
isomorphism invariance of the exact displayed local-model predicate, applies the existing
`DerivedCategory.homologyProperty` weak Serre API, and transports both conclusions through
the middle-vertex isomorphism.

Added two proof-only imports for the new intermediate statements and a proof-only import
of `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`. The public import and theorem
signature stay unchanged. A declaration-scoped unused-variable linter option preserves the
published named chart-map binder `g`; the final code compiles without warnings.

The two remaining obligations are genuine separate steps of the source argument:
constructing the coefficient-layer triangle and controlling only its outer homology;
and transporting the already available pro-etale weak Serre theorem to the specific
etale-sieve/actual-coefficient heart predicate. Neither assumes or restates the desired
cohomology assertion for the successor reduction.

## Proved and sorry left

Closed the original syntactic hole of
`AlgebraicGeometry.Scheme.finiteQuotient_finiteModule_cohomology_succ` by the complete
exactness and weak Serre assembly described above. There are zero sorries in the assigned
module. Added two named theorem holes, each in its own new module:

- `AlgebraicGeometry.Scheme.finiteQuotient_cohomology_filtration_triangle`, node
  `lem-weil-pbc-finite-quotient-cohomology-filtration-triangle`;
- `AlgebraicGeometry.Scheme.finiteCoefficient_etaleLocal_weakSerre`, node
  `lem-weil-pbc-finite-coefficient-etale-local-weak-serre`.

This is a decomposition: one original hole closed and two lower holes added, net minus one
hole closed. It is not a sorry-free proof of the coefficient-filtration theorem.

The empty chart, zero coefficient ring, `n = 0`, and singleton interval `a = b` all fit the
new statements: zero models handle empty charts and the zero ring; the first coefficient
sequence still exists for `n = 0`; the outer-term interval argument uses no strict inequality
between `a` and `b`. The heart predicate is a weak Serre property, not closure under arbitrary
subobjects. Small finite representatives remove the module universe lift.

## No longer needed

No existing public import was removed and no module was withdrawn. The provisional
conjunct-only split was replaced before any push; no such files are part of this delivery.

The assigned proof no longer directly uses the original ten proof dependencies: their
remaining roles occur below the triangle and heart nodes. In particular:

- `prop-weil-pbc-site-comparison-finite-level` and `thm-weil-pbc-site-comparison` are not
  needed on this route. Existing `proEtale_fp_localModels_serre` and
  `coefficientFpLocalSystem_etaleCover` give weak Serre closure followed by etale chart
  descent, so no bounded-below comparison full-faithfulness or extension-class lifting is
  needed here. This is local pruning of those dependency edges; other consumers keep
  their modules.
- `lem-constructible-constant-exact` is replaced by the already proved exact constant
  realization at independent universes in `def-sfb-site-derived-constant-module-functor`,
  which matches the actual ringed module encoding.
- `lem-weil-pbc-locally-constant-derived-serre` is used through the already proved
  `lem-sfb-proetale-fp-local-models-serre`, which supplies the correct pro-etale encoding.
- K-flat resolution, site derived tensor descent, actual adic coefficient data, exact
  restriction and weakly etale localization remain needed by the two new source steps.

No unit-level statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original documentation labels `lemma-bounded` as Tag 094I. In this Stacks snapshot,
`lemma-bounded` is 0942, whereas 094I is `lemma-locally-constant-bounded`. The new source
citations distinguish these and retain 094H for the tensor local-constancy lemma. The
existing theorem docstring and statement were preserved.

A split into the two conclusions alone would only repackage the original obligation;
that provisional version was replaced with the coefficient-triangle and generic heart
steps, with real Lean exactness and homology-property glue between them.

The source's derived comparison route is unnecessary for the heart closure once the
already available finite-presentation pro-etale Serre and etale-chart theorems are used.
The remaining work is the normalized coefficient/slice encoding transport and the
flat K-flat coefficient-layer construction. No shared definition or statement was changed.

## New nodes

`lem-weil-pbc-finite-quotient-cohomology-filtration-triangle` records the coefficient-layer
short exact sequence, its actual derived triangle and controlled outer homology. It makes
no claim about the middle homology; exactness and the weak Serre argument are discharged
in the assigned module.

`lem-weil-pbc-finite-coefficient-etale-local-weak-serre` is a generic theorem about ordinary
module sheaves for any finite coefficient ring and any scheme chart. It has no completed
object, quotient tower, perfect complex, interval or successor conclusion. Its proof route
uses the existing pro-etale finite-presentation Serre theorem and etale-chart theorem.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
