## What changed

Filled both proof holes in Sheaf.Paper.KummerBarResolution. The internal-Hom
comparison is constructed by uniqueness of right adjoints after identifying the
actual relative tensor coequalizers and transporting along symmetry. Its
normalization is proved on the quotient maps, and this same normalization proves
uniqueness. The proved private tensor helpers adapt the existing argument in
Sheaf.WeilSheaf.NativeHomPrecompositionQuasiIso, without importing that module.
Added only the proof import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose.
The bar additivity proof is componentwise B.bar.maps_additive.

All existing public signatures, definition bodies and public imports are retained.
The node proof plan records the implemented argument. No definition repair or
consumer adaptation is needed for the current restored source.

## Proved and sorry left

Closed 2 of 2 existing holes:

- AlgebraicGeometry.ProEtale.CondensedRing.kummerInternalHomComparison_existsUnique
  (def-sfb-kummer-bar-resolution).
- AlgebraicGeometry.ProEtale.CondensedRing.kummerExplicitBar_additive
  (def-sfb-kummer-bar-resolution).

Added zero holes; zero holes remain in the delivered module. No split-off lemmas.
All private helpers are proved. This is a proof of both existing theorems, with
unchanged statements, rather than a decomposition.

Validation: lcompile.py accepted the complete proof in 24.4 seconds. The final
packet removes the remaining unused-section-instance warning with an explicit
omit. Delivery preflight checks the final source and its generated axiom probe.

## No longer needed

None. Every existing public import supports retained statements or definitions.
No declared dependency is pruned and no module is withdrawn. The generic
coequalizer proof is reused locally; importing the larger native-Hom module is
unnecessary and would add unrelated proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The node was a definition node with an empty proof plan although its presentation
law and additivity theorem still had holes. The plan now records their proofs.
The rework row records a quarantine caused by a transitive projective-line import;
the current item source is restored and compiles against the baseline. Its Lean
attachment and all original dependencies are preserved.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
