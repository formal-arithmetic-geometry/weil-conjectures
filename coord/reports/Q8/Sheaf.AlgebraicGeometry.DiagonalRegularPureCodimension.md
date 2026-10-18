## What changed

Proved `AlgebraicGeometry.diagonal_isRegularImmersionOfPureCodimension` without changing
its signature or definitions. Reused the proved source-library diagonal regularity instance.
Localized its affine regular generators to the stalk, proved that their germs lie in the
maximal ideal, and identified the generated ideal with the kernel of the stalk map.
Mathlib's regular-sequence quotient dimension formula then proves the dimension clause.
Reindexed the resulting list by `Fin d` for the final regularity clause.
Updated the node proof to this implementation. The unit's chart/coordinate-difference route
is preserved inside the source-library diagonal instance.

The module compiled cleanly through `lcompile.py` in 4 seconds. Searches used LeanFinder
(the exact regular-sequence dimension formula), Loogle (regular-sequence interfaces),
and grep (the dimension formula and the source-library diagonal/stalk arguments).
No change record or consumer adaptation is needed: the public interface is unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.diagonal_isRegularImmersionOfPureCodimension`
(node `lem-pur-diagonal-regular-immersion`). Added 0 holes. No `sorry` remains in the delivery.
This is a proof, not a decomposition.

The argument uses only finite type over an arbitrary field to obtain Noetherian stalks;
it introduces no perfect-field or smooth-base assumption. Empty schemes are covered by the
pointwise quantifiers. The prescribed positive-codimension hypothesis is unchanged.

## No longer needed

Removed the direct proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`: the proof needs no declaration
from this module directly. It may remain transitively imported by the source library.

The separate dependency `sbc-thm-etale-local-normal-form`, module
`Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`, is unnecessary for this proof: the proved
source-library diagonal theorem already implements the unit's normal-form argument with
standard smooth affine charts. Removed that direct DAG proof edge; no claim is made that
the normal-form module becomes globally unreachable. No other declared proof dependency
is unused, and no other module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The existing source-library `IsRegularImmersion.ringKrullDim_stalk_add` cannot be applied
as stated here: its signature assumes a perfect field and smooth ambient structure map,
which are unavailable and unnecessary. Its proof supplies the appropriate localization
argument, which works with the available locally Noetherian ambient scheme. There was no
need to change that source theorem or any statement in this delivery.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
