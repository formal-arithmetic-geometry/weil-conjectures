## What changed

Replaced the proof of `AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isProper` with a direct construction from the existing curve estimate theorems in `WeilConjectures.AlgebraicGeometry.Curve.Estimate`, and the existing cohomological-dimension theorem. Removed the prior proof-only imports that were unnecessary.

## Proved and sorry left

The target theorem is proved. No `sorry` remains in the delivered module.

## No longer needed

Removed proof-only imports of `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension`, `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion`, `WeilConjectures.AlgebraicGeometry.Curve.Brauer`, `WeilConjectures.AlgebraicGeometry.Curve.Kummer`, and `WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`; their results are subsumed by the existing `Estimate` and `CohomologicalDimension` declarations.

## Where the brief, the DAG or earlier work was wrong

The DAG plan was unnecessarily low-level for this module: the source library already exposes the three degree estimates and the high-degree vanishing theorem needed to assemble the target directly.

## Second reading by E2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body differ.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. The target theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`.
3. No statement was split off and no new node was added. The direct proof uses existing declarations from `Estimate` and `CohomologicalDimension`; their statements are unchanged and the hypotheses match the target exactly.
4. The direct route is shorter and preserves the unit's target statement. The five old proof-only imports are unnecessary and were removed.
5. The DAG node's Lean declaration and statement match the module. The old conceptual dependency list is retained because the Estimate declarations are existing library results without separate DAG nodes.

Changed after review: no Lean theorem statements or definitions. Confirmed the proof of all four conjuncts, including conversion of `2 < q` to the required `3 ≤ q` and derivation of `n ≠ 0` from `hn`.
