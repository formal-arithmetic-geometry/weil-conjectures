## What changed

Proved `AlgebraicGeometry.Scheme.absoluteFrobenius_coefficient_naturality` in
`Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality`, preserving its complete
signature and the definition of `coefficientFrobeniusTrivialization`.

The proof works directly for every exponent. Fibre-product projection uniqueness identifies
the site isomorphisms chosen for the two coefficient rings. Taking adjuncts and using the
section-unit equations proves the ordinary restriction-of-scalars square. The existing
`CategoryTheory.Functor.mapDerivedCategorySquareIso_hom_app_id` descends that square to
the derived categories. A fully proved generic mate calculation then transposes it through
the scalar-extension adjunction and cancels the comparison isomorphism.

Added the proof-only import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars`.
All three helpers are private and fully proved. Updated the theorem's proof docstring and
its existing node's proof, proof dependencies, proof origin and obsolete tool approvals.
No public definition, statement, visibility or existing public import changed.

The generic ring-sheaf comparison and its section normalization are used from
`lem-weil-pbc-ring-sheaf-change-adjunction`; the specified scalar mate and adjunction are
used from `def-sp-constant-scalar-pullback-comparison` and `def-weil-pbc-four-corners`.
These are generic infrastructure for the same coefficient compatibility, not replacements
for any statement or step realized by the coefficient unit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.absoluteFrobenius_coefficient_naturality`
(node `lem-trf-absolute-frobenius-coefficient-naturality`).

Added zero holes and zero split statements. No `sorry` remains in the delivered module.
The required remote single-file compile passed cleanly in 18.3 seconds, with no warnings.
The proof-only import passes the import-direction check.
The proof uses the existing normalized Frobenius-trivialization theorem; proving that
dependency is outside this item. This is a proof from existing declarations, not a
repackaging of the item as an intermediate assumption.

## No longer needed

No existing imports were removed. The following planned direct proof dependencies are
pruned from this node, together with their obsolete top-level `tool_uses` entries:

- `det-prop-scalar-six-pullback`, module `Sheaf.SixFunctors.ScalarSixPullback`:
  its transported condensed comparison and composition law are unnecessary because the
  actual comparison in the statement is already defined as the scalar-adjunction mate.
- `lem-pur-derived-change-of-rings`, module
  `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: this proof requires neither
  a chosen K-flat resolution nor a tensor computation. It uses the already supplied
  scalar adjunction. This prunes a direct proof dependency, not that adjunction's own
  construction dependencies.
- `lem-weil-pbc-finite-discrete-condensed-ring-constant`, module
  `Sheaf.Paper.FiniteDiscreteCondensedRing`, and
  `lem-weil-pbc-finite-discrete-scheme-ring-constant`, module
  `Sheaf.Paper.FiniteDiscreteSchemeRing`: no coefficient encoding is transported in the
  new proof; all functors and maps are already in the statement's constant-ring model.

The one-step calculation, addition-law pasting and induction are unnecessary. Both
`lem-trf-absolute-frobenius-site` and `lem-pur-frobenius-trivialization-pullback` remain
needed for the actual normalized trivializations. No globally unreachable module is
claimed here: other statements may still use every pruned direct dependency.

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan is valid, but longer than the route exposed by the
published interfaces. The module's scalar comparison is already the inverse mate of
exact restriction, so its compatibility can be proved on restrictions and transposed.
The existing normalization specifies every iterate directly, making a separate base case,
one-step case and induction redundant.

The choices of site isomorphism for the two rings must be identified explicitly; this
is proved from both projections and proof irrelevance for the characteristic witnesses.
No statement correction, definition repair, forced adaptation or new node is needed.
The argument covers zero exponents, empty schemes, zero rings, identity coefficient maps
and non-flat finite coefficient maps without extra assumptions.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
