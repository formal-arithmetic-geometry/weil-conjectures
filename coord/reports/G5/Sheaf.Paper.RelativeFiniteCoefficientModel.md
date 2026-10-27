## What changed

Replaced the existential proof hole in
`AlgebraicGeometry.Scheme.exists_relative_finite_coefficient_model` with an explicit
construction and a proof using a single lower slice comparison and proved scalar transport. The original signature,
public imports, and docstring are preserved.

`RelativeFiniteCoefficientTransport` constructs the coefficient isomorphism using
constant-sheaf adjunctions, precomposes module sheaves with `AsSmall.down`, and
restricts their scalar action along the actual coefficient isomorphism. It proves
that this functor is an additive equivalence and constructs its derived functor and
homology comparison. All these constructions and proofs have zero holes. In
particular, the chosen complex L is the image of the actual pulled-back complex;
no object is chosen from an unproved existence theorem.

The item proves the covering-sieve equivalence: pull a final-object cover back to
an arbitrary object, transport it along AsSmall.down, and conversely pull the cover
of AsSmall.up of the final object along AsSmall.up. Finite modules are finitely
generated; finite generation over the finite coefficient ring gives finite
underlying sets. Isomorphism invariance and exact-functor homology then give both
cohomological lissity equivalences. Exactness of inverse image and of the constructed
transport gives the zero-cohomology implication.

The scalar argument is implemented separately. `RelativeFiniteScalarRestriction`
uses naturality of the inverse-image constant-section map and the constant-sheaf
site comparison to equate the coefficient maps, then constructs identity linear maps on their ordinary module sections. `RelativeFiniteScalarTransport` derives that exact restriction square,
constructs the small scalar-extension adjunction from K-flat resolutions and its
recorded left-derived universal property, and uses uniqueness of left adjoints.
Native pullback/scalar compatibility follows from the existing ring-sheaf change
adjunction. Both scalar modules have complete proofs.

The remaining lower obligation compares constant modules on one individual slice.
It neither asserts the original existential statement, nor assumes or concludes a
cohomological lissity predicate, nor mentions scalar extension. It is valid for
arbitrary commutative coefficient rings, including the zero ring, and arbitrary
module objects. No other existing Lean module or DAG node is changed.

Validation: all five modules compiled in import order through `lcompile.py --all`:
transport 8.1 s, slice statement 7.7 s, ordinary scalar comparison 16.7 s, derived
scalar comparison 15.0 s, and the item 12.3 s. Removed two redundant private proof
imports afterward; the required delivery check recompiles the final packet.

## Proved and sorry left

The original theorem `AlgebraicGeometry.Scheme.exists_relative_finite_coefficient_model`
now has a complete Lean proof using the named slice theorem and the proved scalar
comparison. This is a decomposition: one original hole replaced by one strictly
smaller ordinary slice hole, not an axiom-free proof of the item. The construction,
covering-sieve glue, exact homology transport, ordinary scalar square and derived
scalar transport add no holes.

Every remaining hole in this delivery is the entire proof of one public theorem:

- `AlgebraicGeometry.Scheme.relativeFiniteConstantSliceComparison`, node
  `lem-weil-pbc-relative-finite-constant-slice-comparison`.

Its docstring gives the source and the complete intended argument. It compares
local module isomorphisms on corresponding slices, retaining the same coefficient
module. The item module has zero remaining holes; the packet has one. The direct
hole count closes one and adds one, with no direct net decrease. The project's
ledger determines the net against its pinned import-closure baseline.

## No longer needed

No original imports are removed and no module is withdrawn. No global pruning is
claimed. Removed the unused private import of
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso`
from the new transport module; the homology comparison API is already public through
the required imports. Removed the redundant private import of
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` from the new derived scalar
module; `BoundedConstructibleTower` publicly imports it.

The item's former direct proof dependency
`lem-sfb-proetale-fp-local-models-comparison`
(`Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison`) is not
used: its coefficient type is in the scheme universe and its output uses ULift and
the old constant RingCat presentation. The explicit transport here handles the
actual coefficients of the item directly.

The former direct proof dependency
`lem-weil-pbc-constant-coefficient-local-models-comparison`
(`Sheaf.Paper.ConstantCoefficientLocalModelsComparison`) is not used: this delivery
keeps the actual commutative constant coefficient ring throughout, so it needs no
comparison with the old constant RingCat local-model predicate.

`lem-weil-pbc-ring-sheaf-change-adjunction` remains used by the proved scalar
comparison. `lem-sfb-adic-finite-reduction-data` remains needed for the actual
small-site extension. They have not been pruned.

## Where the brief, the DAG or earlier work was wrong

The listed finitely presented comparison is not directly applicable to this
coefficient universe or to the relative inverse-image coefficient action. Its
existence does not itself give the slice comparison in the statement of the item.
The revised DAG records precisely the smaller comparisons that are still needed.

The original node's proof plan also described the scalar transport in words; the
listed ring-sheaf change adjunction gives native pullback/scalar compatibility, but
does not identify the constructed small-site functor with the scalar-extension
route. This delivery proves that functor isomorphism by first proving the ordinary
restriction square, then deriving its left-adjoint comparison.

The small-case checks use no geometric points or faithful constant-sheaf functor:
empty schemes/slices, zero rings, zero modules and the identity coefficient map
all retain the same universal-property and equivalence arguments.

## New nodes

`lem-weil-pbc-relative-finite-coefficient-transport` records the explicit coefficient
transport, its additive equivalence, its derived functor and homology comparison.
Its module is `Sheaf.Paper.RelativeFiniteCoefficientTransport`; its proofs use the
existing Mathlib module equivalence and adopted exact-functor homology APIs.

`lem-weil-pbc-relative-finite-constant-slice-comparison` records the comparison of
constant module models on one slice with the same coefficient module. Its module
is `Sheaf.Paper.RelativeFiniteConstantSliceComparison`. Sources: Stacks Tags 03CY
and 03A0, via module sheafification and the induced equivalence on slices.

`lem-weil-pbc-relative-finite-scalar-transport` records the natural isomorphism of
native and small-site derived scalar-extension routes. Its module is
`Sheaf.Paper.RelativeFiniteScalarTransport`. Sources: Stacks Tags 03D8, 06YY and
0D6D, using scalar restriction and uniqueness of left adjoints.

`lem-weil-pbc-relative-finite-scalar-restriction` records the proved square of ordinary
restriction-of-scalars functors, with explicit naturality of the constructed
coefficient isomorphism. Its module is `Sheaf.Paper.RelativeFiniteScalarRestriction`.
Sources: Stacks Tags 03CY, 03D8 and 03A0. It adds no hole.

The Mathlib searches found sheaf and module equivalence APIs, but no theorem giving
these project-specific coefficient comparisons. No change record is needed because
no existing statement, definition, or interface was changed.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
