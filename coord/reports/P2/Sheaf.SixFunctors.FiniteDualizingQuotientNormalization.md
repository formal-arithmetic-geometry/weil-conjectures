## What changed

Proved `WeilConjectures.finiteDualizing_quotient_normalization` without changing its
statement. The compact-support equation pastes the existing open scalar cocycle
with the direct-image coefficient-chain equation. The two unit equations identify
the representative-normalized scalar unit with the exact degree-zero adjunction
transpose of the ordinary restriction unit, then use its identity and composition
laws. The proved generic comparison is exported in the new module
Sheaf.CategoryTheory.NormalizedScalarUnitAdjunction; its node records the
localization/cochain/exact-single calculation. Its ordinary-etale specialization
is proved in Sheaf.SixFunctors.EtaleScalarUnitInsertion. The specialization is
checked separately because the combined file exceeded the 60-second limit even
after replacing implicit unit conversions and the fixed-site insertion wrapper
with explicit isomorphisms and the generic insertion. The scalar-unit composition calculation is proved in
Sheaf.SixFunctors.EtaleScalarUnitComposition so each part meets the same limit.
The remaining helpers are private
and proved. No existing statement or definition changes.

The generic exact-adjunction insertion uses the derived data of the etale interface
itself. The single/unit isomorphisms are explicit in the comparison and are transported
through the scalar compositor by naturality. This avoids the large implicit
derived-object conversions of a direct equality. The generic calculation is
compiled separately and has no postponed proof.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.finiteDualizing_quotient_normalization` (one of one).
No holes added or split off; no `sorry` remains in the four delivered modules.
Also proved SheafExactDegreeZero.normalizedUnit_singleAdjunction and
AlgebraicGeometry.Etale.scalarUnit_eq_adjointInsertion, and
AlgebraicGeometry.Etale.normalizedScalarUnit_comp.
The proof uses existing library declarations, with their existing proof status.

## No longer needed

The original module had only its statement import, which is retained. The planned
`lem-fix-compact-support-coefficient-change`
(`Sheaf.Paper.EtaleCompactSupportCoefficientChange`) is not needed by this proof: its
compact-support equation follows directly from the open scalar cocycle and the
direct-image coefficient cocycle, with no compact-support invertibility,
finite Tor-amplitude or boundedness assertion. This is pruning of this node's
proof dependency, not withdrawal of a module used by other parents. The direct proof-dependency entry for
def-weil-pbc-witness-compatibility was redundant: the scalar functors and
compositors are already statement dependencies of the imported interfaces.
The broad witness compatibility predicate is unused. That node and its module
remain needed transitively; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original theorem docstring carried its parent's blueprint id. It now names
`lem-coef-dualizing-quotient-normalization`, its actual node. The original proof
plan did not name the exact degree-zero identity/composition interface needed to
identify the scalar unit maps. The updated proof record names the declarations
actually used; the theorem and definitions are unchanged.


## New nodes

lem-coef-normalized-scalar-unit-single: the generic representative-normalized
unit is the exact-single adjunction insertion of the ordinary lax unit, after
the canonical single/unit transports. It is proved completely in
lean/Sheaf/CategoryTheory/NormalizedScalarUnitAdjunction.lean. Its hypotheses
make both adjunctions and the representative normalization explicit; it asserts
neither compact-support coherence nor the finite quotient identity/composition
equations. No change record is needed because existing interfaces are unchanged.


lem-coef-etale-scalar-unit-insertion: specializes the generic comparison to the
published ordinary and derived etale scalar adjunctions and the existing unitIso
normalization. It is proved without holes in
lean/Sheaf/SixFunctors/EtaleScalarUnitInsertion.lean and supplies the common unit
identification used in both original unit equations.


lem-coef-etale-scalar-unit-composition: the regular scalar unit cocycle for
arbitrary composable coefficient maps and any scheme, proved in
lean/Sheaf/SixFunctors/EtaleScalarUnitComposition.lean. The original finite-quotient
cocycle is its specialization along finiteDualizingQuotient_comp. The proof uses
the sectionwise ordinary unit equation, exact insertion composition, and the
naturality of the fixed scalar compositor under the single/unit isomorphisms.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.NormalizedScalarUnitAdjunction": "3f1997f07cec921425ad7a00c13bc4fa250b338d", "Sheaf.SixFunctors.EtaleScalarUnitComposition": "940be04c8f69eddebcac2fd3ddaeec17f86e9f7a", "Sheaf.SixFunctors.EtaleScalarUnitInsertion": "d50fea5f513e1644db01335ca1486c483b6cbd37", "Sheaf.SixFunctors.FiniteDualizingQuotientNormalization": "de85b584859e0466dcea7e704f833c9d28fa5320"}, "results": {"Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization": {"hash": "67ac51c63df58fad88a4d883161231de215ed32a", "status": "OK"}}, "seconds": 77, "time": "2026-10-28T10:35:51+0800", "transitive": 0, "version": 1}
```

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
