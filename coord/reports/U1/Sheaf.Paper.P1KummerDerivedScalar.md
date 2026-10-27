## What changed

Proved the public p1KummerDerivedScalar theorem from normalized endpoint existence,
endpoint composition and preservation of the fixed Kummer specification, followed by a
proved categorical conjugation/naturality argument. Its public signature is unchanged.
The endpoint record fixes ordinary insertions on generators and derived isomorphisms as
adjunction transposes, so its witnesses are determined up to the equality used downstream.

Factored p1KummerDerivedInsertion through the identical generic exact-degree-zero adjoint
insertion formula. The new ExactDegreeZeroAdjoint API proves composition and invertibility
from the universal property. No arbitrary object is selected
from an unproved existence theorem. See coord/changes/p1-kummer-exact-adjoint-interface.md.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Etale.p1KummerDerivedScalar
(node lem-sp-p1-kummer-derived-scalar) by a complete proof from the endpoint results
and the separately stated Chern preservation theorem. Its signature is unchanged.

Proved AlgebraicGeometry.Etale.p1KummerScalarEndpointExistence,
AlgebraicGeometry.Etale.p1KummerScalarEndpointComposition and all retained declarations of
Sheaf.CategoryTheory.ExactDegreeZeroAdjoint. The endpoint construction and its
composition laws introduce no holes.

Added one hole: AlgebraicGeometry.Etale.p1KummerChernScalar, node
lem-sp-p1-kummer-chern-scalar. Its proof is exactly `by sorry`, with the full Ext,
integral-generator and root-map argument documented in its docstring and node.
This is strictly the preservation part of the argument: it assumes already fixed
normalized endpoints, constructs none, and states no composition or transitivity law.
The parent proof combines endpoint existence, endpoint composition, preservation and
a proved categorical conjugation argument. This is a decomposition: one original hole
closed and one new hole added, net zero, with two substantive endpoint lemmas proved.
The item's own module has zero holes; the packet has one. No definition has a hole.
The complete import-order build and the unchanged VectorTraceScalarDescent consumer
compiled successfully; the final import cleanup is checked by the delivery build.

The scratchpad Chern proof drafts established the generic Ext square and its forgetful
realization, and separately checked the realization conversion. The remaining concrete
Ext-square/endpoint conversion repeatedly exceeded the single-file compile limit.
Those drafts are retained only in scratchpad. Existing imported theorem holes remain
as upstream obligations; the packet introduces only the named Chern hole above.

## No longer needed

Removed direct imports WeilConjectures.AlgebraicGeometry.DerivedCategories,
Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine,
Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction,
Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel,
Sheaf.SixFunctors.RingedDerivedMonoidalComparisons and
Sheaf.Algebra.Homology.KFlatIndependentCoefficients from the item.
The published endpoint comparison already names the actual left-adjoint composition
comparison; its functoriality is proved directly, without a ringed-topos tensor model.
The endpoint-existence proof reuses the supported coefficient comparison, rather than
reconstructing K-flat degree-zero scalar extension. Existing statement dependencies
remain intact. No source-library declaration is removed; no whole module is withdrawn.

The unused generic Ext-square draft and its private transpose-shift helper are also
removed from the new API; they are not dependencies of any retained complete proof.

The parent proof no longer uses these direct planned proof dependencies:
lem-asd-finite-etale-twist-line, def-pc-kflat-complex,
lem-pur-derived-change-of-rings and lem-sfb-ringed-derived-monoidal-comparisons.
They are replaced by endpoint existence, endpoint composition and scalar Chern preservation;
none is removed from any other declaration's dependencies.

The obsolete parent tool_uses entries for finite twist flatness, derived-change-of-rings
construction and ringed derived monoidal comparisons are withdrawn. They are no longer
direct proof steps in this theorem. This does not claim they are globally unused.

The generic insertion API needs no shift-adjunction import; that proof-only import
is local to the endpoint-composition module.

The endpoint-composition proof also removes direct proof imports of
Sheaf.AlgebraicGeometry.SupportedKummerScalarMaps and
Sheaf.SixFunctors.GeoCartierCoeffExtension: its only constant-sheaf helper is proved
locally by the constants adjunction. The composition node no longer uses
lem-asd-supported-kummer-scalar-maps. The endpoint-existence proof still needs it.

## Where the brief, the DAG or earlier work was wrong

The planned tensor-model proof is unnecessary for the scalar-transitivity equality:
the actual normalized endpoint records and adjunction composition suffice. The source
statements and target meanings are preserved. The empty Cartier divisor allows the
existing supported residue comparison to supply ambient Tate-line universal data over
any scheme; no new geometric hypothesis is introduced.

The dispatcher reference clock in .budget was reset to 2026-10-23T15:23:35Z while the
claim and earlier work date from 2026-10-23T12:41:41Z. No attempt identifiers were supplied
in the retained sandbox. Neither budget file nor launcher tool was changed.

## New nodes

- def-sp-exact-degree-zero-adjoint-interface: the constructed generic adjunction
  insertion, with proved composition and invertibility formulas, and
  general-site scalar specializations. All declarations are proved.
- lem-sp-p1-kummer-scalar-endpoint-existence: ordinary insertion construction and
  its derived universal property, reusing supported Kummer coefficient data on the
  empty Cartier divisor; cancellation gives arbitrary finite coefficient maps.
- lem-sp-p1-kummer-scalar-endpoint-composition: equality on ordinary generators,
  exact-single/adjunction composition, and compatibility of mates with shifts.
- lem-sp-p1-kummer-chern-scalar: the Ext square followed by forgetting module
  scalars identifies the fixed abelian Kummer class after scalar transport. This is
  the one remaining split-off obligation, rather than a proved declaration.

Definition change record: coord/changes/p1-kummer-exact-adjoint-interface.md.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
