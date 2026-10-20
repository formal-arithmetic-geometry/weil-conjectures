## What changed

Repair the returned retirement against the current consumers. Withdraw
`Sheaf.AlgebraicGeometry.DeterminantDualPairing` via `deleted.txt` and attach
`lem-sc-exterior-dual-pairing-construction` to the existing proved upstream
`AlgebraicGeometry.exterior_dual_pairing_exists`.

All three consumers now privately import the upstream construction. Preserve
B8's official local-bijectivity import and current exteriorSheafPowerIso API.
The determinant-isomorphism consumer applies local perfection directly to the
upstream pairing, proves it invertible, then composes comparison isomorphisms.
Both Koszul consumers transport the upstream pairing by the current source
comparison and its contravariant dual; compose local section bijections to
retain the original stalk-surjectivity arguments. Preserve K4's upstream
restriction import and comparison rewrites, which landed during this repair.
The Yoneda consumer uses explicit functor-composition rewrites in its final
surjectivity proof to avoid an elaboration failure in the former simplification.

Statements, attributes, public imports, options and docstrings are unchanged.
The four DAG copies preserve current metadata and record the actual proof.
Validation: all three files compile cleanly with `lcompile.py --all`; the
two changed Koszul files took 8.0 and 10.7 seconds, and the unchanged compiled
determinant-isomorphism file was reused (its preceding compile took 3.2 seconds).
Change record: `coord/changes/retire-determinant-dual-pairing.md`.

## Proved and sorry left

Actual initial hole count: zero. Holes closed: zero of zero. Holes added: zero.
No holes are split off or left in any delivered module. The upstream pairing
construction is already proved. The following consumer theorems remain fully
proved with the repaired transport:

- `AlgebraicGeometry.exteriorSheaf_dual_iso`;
- `AlgebraicGeometry.koszulRegularImmersion_self_ext_dual_exterior_conormal`;
- `AlgebraicGeometry.koszulRegularImmersion_self_ext_yoneda_surjection`.

This repairs a duplicate retirement rather than claiming newly closed holes.

## No longer needed

Retire `Sheaf.AlgebraicGeometry.DeterminantDualPairing`. Its three private
consumer imports are replaced by the existing upstream construction module.
Its own public imports of `Modules.ExteriorSheaf`, `Modules.Dual` and
`Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, and private imports of
`DeterminantDualAlternatingFamily` and `ExteriorSheafComparison`, disappear
with the duplicate. Those supporting modules remain needed elsewhere;
no global pruning of them is claimed.

The construction node no longer needs `lem-sc-exterior-sheaf-comparison`:
the upstream proof constructs the pairing directly on exteriorPower.
The consumers retain the current `lem-sc-exterior-sheaf-power-comparison`.
Their inverse-wedge formula and conjugation/cancellation steps are unnecessary
because upstream construction and local perfection now share one API.
The earlier retained packet's additional private import of
`Sheaf.AlgebraicGeometry.ExteriorSheafComparison` is unnecessary in all three
consumers and is removed. The two Koszul consumers keep the distinct current
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison` restriction API.
All parent edges to the construction node stay and reach its upstream theorem.
No mathematical node or unit step is withdrawn; no new node is introduced.

## Where the brief, the DAG or earlier work was wrong

The returned packet predated B8's retirement of the local pairing theorem.
Its old local theorem import and exteriorSheaf arguments would overwrite the
current upstream API adaptation. This repair starts from the current files,
uses the official construction and local theorem together, then transports
the result. It also incorporates K4's newer restriction retirement rather
than restoring the retired Sheaf restriction module. All four node copies
preserve current review metadata instead of reverting it to the old packet.

The generic proving brief describes holes, but this listed retirement has
zero. The changed construction-node Lean attachment expresses the same
pairing on the canonically isomorphic exterior sheaves. No target statement,
chapter, or unit route changes. Earlier msearch searches found the ring-level
pairing API; the project sources supply the exact proved upstream pairing,
local-bijectivity theorem and canonical comparisons used in the repair.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
