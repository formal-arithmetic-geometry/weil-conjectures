## What changed

Proved both original theorems in
`lean/Sheaf/AlgebraicGeometry/BoundedBelowProEtaleComparison.lean`, preserving every
published signature, definition, and public import. The bounded-below derived unit follows
from the existing generic injective-acyclicity criterion, the underived comparison unit,
and comparison-direct-image acyclicity. Its full faithfulness and the canonical
unit--Leray global-sections comparison then follow.

The affine theorem now imports the declared continuity input
`Sheaf.AlgebraicGeometry.ProEtaleAffineContinuity`. Naturality of the derived evaluation
unit and the resolution map identifies its canonical arrow with the resolution cocone's
arrow. Cancellation proves the quasi-isomorphism. A proved private lemma establishes that
filtered colimits of arbitrary left-module complexes commute with homology; transport
across the quasi-isomorphism proves the specified homology cocone is colimit.

Updated the node's proof, proof_deps and proof_origin to record this route, and removed
obsolete tool_uses entries. Added two private, completely proved helpers. No new modules,
new nodes, statement changes, definition changes, or forced adaptations.

Validation: the complete delivered Lean module compiled cleanly through lcompile.py
in 14.5 seconds, with exit code 0 and no warnings. Every original public import is
preserved. The delivery dry run additionally checks exported signatures and axioms.

## Proved and sorry left

Original holes: 2. Closed:

- `AlgebraicGeometry.ProEtale.boundedBelowComparison`
  (node `sk-prop-sf-comparison`).
- `AlgebraicGeometry.ProEtale.affineBoundedBelowComparison`
  (node `sk-prop-sf-comparison`).

Holes added: 0. Holes left in the delivered module: 0. Split-offs: 0.
This is a proof from the existing stated dependencies, including the still-open
`AlgebraicGeometry.ProEtale.proEtaleAffineContinuity`; it does not claim to close that
imported theorem or its transitive proof obligations.

## No longer needed

Removed these proof-only imports:

- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`
- `Mathlib.Algebra.Category.ModuleCat.AB`

The following old direct proof dependencies are no longer separately used:
`lem-sc-bounded-below-injective-resolution`,
`lem-weil-pbc-exact-functor-bounded-below`,
`lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-termwise-adjunction-homotopy`,
`lemma-weil-pbc-leray-acyclicity`,
`lem-weil-pbc-leray-acyclicity-quasi-iso`, and
`def-weil-sheaf-of-modules-category`.
The already-proved generic derived-unit criterion packages the resolution and acyclic
complex argument. Bounded-below injectivity of the given J gives K-injectivity directly
using Mathlib. The canonical Leray comparison and remaining categorical declarations are
already available through the preserved public interface. Some removed direct imports
remain transitive dependencies; no claim is made that every listed module leaves the
whole targets' import closure. A source import-closure comparison found no modules removed
from the item's transitive closure; these are direct-import and DAG-edge prunings only.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The declared affine-continuity input had a Lean declaration but was not imported by the
item. Its published arrow ends in derived evaluation, while the item's arrow ends in the
section complex of a chosen injective resolution. Applying it directly therefore requires
the naturality and cocone compatibility proved here. There is no need for a new statement
of affine continuity or a new unresolved intermediate theorem.

The recorded bounded-below ringed-site resolution theorem is expressed using
SheafOfModules over a commutative ring sheaf. The generic source-library derived-unit
criterion instead applies directly to the fixed-coefficient sheaf categories for arbitrary
possibly noncommutative rings, exactly as the unchanged item requires.

The unit metadata still records the older snapshot in sec-smooth-purity, with no realized
steps, whereas the node and current main-20261015 source are in sec-proetale-coefficients.
This inherited metadata was not changed. The proof retains the current source's
injective-resolution/acyclicity comparison and affine-continuity route.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
