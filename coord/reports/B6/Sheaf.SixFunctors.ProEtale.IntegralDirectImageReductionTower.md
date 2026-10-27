## What changed

Proved `AlgebraicGeometry.ProEtale.integral_direct_image_reduction_tower`, preserving
its statement and all public imports. The level comparison is the conjugate scalar
restriction/direct-image isomorphism followed by restriction of the inverse of the
specified finite projection. Iterated adjunction mates prove its augmentation identity.
Mates preserve the consecutive restriction square, and the existing generic
`IntegralPresentation.adjointTransitionComparison` supplies the transition identity.

Added the proved module
`Sheaf.SixFunctors.ProEtale.IntegralRestrictionPullbackTowerSquare`. It specializes the
existing derived restriction tower square to the specified quotient maps. The proof
first transports the generic square along an explicit factorization of the
point coefficient maps. It identifies the ordinary compositor with the canonical
compositor by equality symmetry, then normalizes the derived natural isomorphisms
before evaluating at the complex. Substitution of the compositor equalities is done
in the abstract component lemma, avoiding rewriting a large concrete derived square.
The scalar map has an explicit composition identity. Derived-category data is passed
directly to the inverse-compositor helper, using the existing integral and finite
module-category instances. All new private instance registrations end before the
public theorem statements; the coherence proof uses its bundle instances locally.

Private categorical helpers and a named bundled quotient map avoid rebuilding large
local scalar comparison terms. Two proved commutativity aliases are used as local
instances for the symmetric sheaf braiding. A typed view of a bundled scalar map and
its proved monoid-hom instance keep generic coefficient maps well typed under strict
transparency. These aliases change no mathematical data.
Proof imports of `DerivedCompletion`, `ScalarSixDerivedPullbackNormalization` and
`IntegralReductionTransitionComparison` use `import all` to access the existing data
aliases and already-proved private coherence helpers. No imported module is modified. Both DAG nodes record the
actual proof route.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.ProEtale.integral_direct_image_reduction_tower`.
Also proved the new theorem
`AlgebraicGeometry.ProEtale.integral_restriction_pullback_tower_square`
(node `lem-sfb-integral-restriction-pullback-tower-square`).
All categorical helpers are proved.

Original holes closed: 1 of 1. Holes added: 0. Sorries left in the delivered files: none.
Both modules compiled through the prescribed `lcompile.py` workflow with
`respectTransparency` and `respectTransparency.types` explicitly true. The main module's
profiled compile took 45.1 seconds. Diagnostic settings were removed; the delivery
command checks the clean packet, its axioms and the complete preflight before pushing.

## No longer needed

Removed direct proof imports and the corresponding non-unit proof dependency edges:

- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
  (`lem-weil-pbc-standard-quotients-perfect`): invertibility is already assumed by hproj;
  no perfectness argument is required in this conditional coherence theorem.
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`
  (`lem-pd-module-ringed-topos-derived-comparison`): the proof stays in the specified
  internal module categories and needs no comparison with section-action presentations.
- `Sheaf.Paper.CompletedDirectImageLimits`
  (`prop-weil-pbc-direct-image-limits`): the mate and transition equations prove coherence
  directly; no transport of `towerProjection_properties` is needed.

This removes these edges only; no source-library declarations or modules are withdrawn.
The integral coefficient-limit import and dependency are retained because
`det-prop-sfb-qlbar-colimit-x-integral-limit` realizes the first step of the coefficient
comparison unit. The unit route is preserved; the finite tower coherence argument takes
no derived limit. `sk-thm-sf-pf-adic` has empty realized statement and step lists.

## Where the brief, the DAG or earlier work was wrong

The old proof plan treated this conditional compatibility statement as requiring a second
finite-projection theorem in section-action categories. Its hypotheses already supply the
specified internal projection isomorphisms. Iterated mates identify their units, and
pasting of exact restriction squares supplies their transition compatibility. The
existing scalar-six normalization module already contains the generic restriction square.
Its concrete specialization uses the quotient factorization and the canonical ordinary
compositor identity.

No existing statement, definition, target signature, or module held by another group
changes. The proof includes n=0, zero complexes, empty schemes, and unbounded K; it adds
no flatness, boundedness, nonzero, or completeness hypothesis. All isomorphisms use the
specified natural transformations and their uniquely determined inverses.

## New nodes

`lem-sfb-integral-restriction-pullback-tower-square` is a proved specialization of exact
pullback coherence with the consecutive scalar restriction compositor. It has no
invertibility hypotheses, finite projection map, or comparison of integral levels. Its
proof transports `scalarSixDerivedRestrictionTowerSquare` along an explicit coefficient
factorization, identifies the ordinary compositor by equality symmetry, and uses exact
derived localization of inverse natural isomorphisms before evaluating at the object.
Its source, proof, Lean attachment, edge cases, and three kinds of Mathlib search are
recorded. No change record is needed:
no existing statement or definition is changed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
