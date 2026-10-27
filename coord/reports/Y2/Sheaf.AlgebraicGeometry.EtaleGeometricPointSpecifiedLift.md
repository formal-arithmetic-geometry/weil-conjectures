## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.exists_etale_geometricPoint_specified_lift`
with its original statement. Added private proof imports of
`Mathlib.AlgebraicGeometry.PullbackCarrier` and
`Mathlib.CategoryTheory.Limits.Types.Pullbacks`.

Two proved private helpers establish equivalence of the common-field relation on
point representatives and identify a field-valued scheme map's class with the
residue-field class of its image point. The proof evaluates the representing
pullback on a common field, applies
`Scheme.exists_fac_of_etale_of_isSepClosed` at that image point, and checks both
the specified class and the exact composite over the original field. The item's
DAG proof records these details. No public signature or definition changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.AlgebraicSpace.exists_etale_geometricPoint_specified_lift`
(node `lem-sfb-etale-geometric-point-specified-lift`).

Holes added: zero. Sorries left in the item: zero. No split-off statements.

## No longer needed

None. Both original proof dependencies remain used. No original imports, nodes,
or modules were removed or withdrawn. The proof does not need an atlas, a
separate algebraic-space fibre-product point theorem, or any new intermediate
statement with `sorry`.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is valid. Equality in the implemented `Quot` first gives
the equivalence closure of the common-field relation, so the proof explicitly
verifies transitivity via a residue field of a scheme pullback point. The
Mathlib prescribed-point lifting lemma works directly for one etale morphism;
there is no need to package the projection as a singleton covering family.

The original statement is unchanged, including all universe parameters. Empty
source spaces give no supplied point `u`; for an identity or a disjoint union of
etale points the construction selects the component specified by `u`. The proof
uses neither quasi-compactness nor any finiteness of the morphism beyond etaleness.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
