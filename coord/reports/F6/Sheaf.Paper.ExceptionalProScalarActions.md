## What changed

Filled `AlgebraicGeometry.exceptionalProScalarActions` without changing its signature
or imports. All added declarations are private, proved helpers in the item module.
The ordinary multiplication and adjunction arguments generalize the existing private
proofs in `Sheaf.Paper.EtaleCompactSupportScalarAction` from etale sites to arbitrary
sites. They therefore also cover mixed etale/pro-etale site comparisons.

The construction multiplies actual quotient-ring sheaf sections, verifies compatibility
with restrictions and successor transitions, and localizes the resulting natural
endomorphism. Its representative equation is proved. The geometric inverse-image
normalization proves preservation of this action. Localization and adjunctions then
prove preservation by open extension and proper direct image. A uniqueness argument
identifies the recorded etale actions in `G` with canonical multiplication, allowing
composition with the two site comparisons to prove the transported-right equation.
The DAG proof now records these four parts and their actual dependencies.

Validation: the complete item compiled through `lcompile.py` with exit code 0,
no warnings, and a 24.2-second compile time (below the 60-second limit).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exceptionalProScalarActions`
(`lem-sf-exceptional-pro-origin-scalar-actions`).

Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0. No decomposition.
All private helper theorems are proved, and all definitions are explicit constructions.

## No longer needed

No imports removed and no modules withdrawn. The public interface import is still
required by the unchanged statement. The old direct proof dependency
`lem-sf-exact-functor-derived-triangulated` is unnecessary: this proof uses the
specified factorization and the localization universal property directly, and
requires no new triangulated structure. Its Mathlib module remains available
transitively and may still be needed elsewhere. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous one-step plan omitted the uniqueness argument needed to identify the
arbitrary normalized etale action packages in `G` with the constructed actions. It
also did not point to the already proved private construction in
`Sheaf.Paper.EtaleCompactSupportScalarAction`. Generalizing that construction and
proving uniqueness closes the item outright, with no further split statements.

No statement, target, public definition, or existing dependency interface changed.
The argument works for every commutative ring and every coefficient element as
stated, including zero, units, and the zero ring; it uses no nonzero-divisor,
completeness, point, or boundedness assumption.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalProScalarActions": "a7d862e2593cb5d2cd4764af290b6e4b42661ef4"}, "results": {"Sheaf.Paper.ExceptionalProOriginExactLinear": {"hash": "278e72932fdf88276bc498145e0fd01605a002c7", "status": "OK"}}, "seconds": 97, "time": "2026-10-28T03:27:21+0800", "transitive": 0, "version": 1}
```

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
