## What changed

Proved `WeilConjectures.integralLineTensor_complete` with its signature unchanged.
The proof chooses an auxiliary finite field of characteristic different from l,
uses `sfDerivedComplete_iff_legacy` to pass to unrestricted completeness, applies
the existing `CompletedLineTensor.complete` at exponent one, and converts back.
The degree-one signed power is definitionally L, so the derived functor is exactly
the one in the requested conclusion. The sandbox module compiled with lcompile.py.
Public imports and all other public interfaces are preserved.

The item's DAG proof now records this route. Added a declaration-level DAG attachment
for the already existing `CompletedLineTensor.complete`, without changing that module.
This avoids a cycle through the much larger coherence node, whose plan already uses
this item. The new node is not a new Lean statement or a transferred proof hole.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`WeilConjectures.integralLineTensor_complete`
(node `lem-weil-integral-line-tensor-completeness`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered Lean file.
The proof relies on the pre-existing sorry in
`WeilConjectures.CompletedLineTensor.complete`; this is an existing library
statement used as permitted by the stage-3 brief, not a claim of a closed axiom
closure. Its existing hole is now also described by
`lem-pur-signed-line-legacy-completeness`.

## No longer needed

Removed the following direct proof imports:
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.SfIntegralConstructible`

The old direct proof dependencies
`def-coefficient-twists-detailed`, `def-weil-integral-derived-reduction`,
`def-weil-derived-complete`, `def-weil-derived-complete-integral-detailed`,
`lem-pur-kflat-change-of-rings`, `lem-weil-pbc-site-derived-tensor-descent`, and
`lem-sf-exact-functor-derived-triangulated` are replaced by the two declared
interfaces used in the proof. The coefficient and completeness definitions remain
statement dependencies; K-flat descent and exactness remain mathematics needed
below the existing signed-line theorem. No module is withdrawn or asserted to
leave the whole targets' closure.

## Where the brief, the DAG or earlier work was wrong

The plan overlooked the already stated more general signed-line completeness
clause. Rebuilding that argument here would duplicate it. Import-direction checking
confirms that `CompletedLineTensorCoherence` does not import this item. Its broad
DAG node does, however, depend on this item, so pointing the new proof at that
whole node would create a circular DAG. The separate attachment records exactly
the existing independent declaration being used. The module held by P3 is untouched.
The unit's realized route is unchanged. Exponent one, arbitrary unbounded K,
and schemes of unrestricted residue characteristic are all covered; the auxiliary
finite field is only a presentation of completeness.

## New nodes

`lem-pur-signed-line-legacy-completeness` records the pre-existing theorem
`WeilConjectures.CompletedLineTensor.complete`, including its independently sized
universes, every integer exponent, source, and full docstring proof plan. It adds
no Lean declaration and no sorry. Searches with LeanSearch, LeanFinder, Loogle,
and Mathlib grep found no Mathlib theorem for these project predicates.
No change record is required: no declaration signature, definition, public import,
or existing attribute changes.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
