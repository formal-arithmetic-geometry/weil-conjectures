## What changed

Proved `AlgebraicGeometry.affine_perfect_koszul_principal_unit_perfect` in
`Sheaf.Paper.AffinePerfectKoszulPrincipalUnitPerfect`, with its signature unchanged.
Added the proof-only import `Mathlib.LinearAlgebra.ExteriorPower.Basis` and three
proved private helpers. The argument adapts the existing proved finite-basis and
boundedness helpers of `Sheaf.AlgebraicGeometry.AffineKoszulGeometricProperties`
to the deleted shifted complex; that module itself is not imported.

A wedge basis indexed by `Set.powersetCard (Fin r) q` identifies each exterior
power with a finite free module. `tildeFinsupp` and `SheafOfModules.mapFreeIso`
transport this identification through associated sheaves and restriction.
An empty wedge-basis index type proves vanishing for `r < q`. The shifted
chain term in degree `q` is the exterior power of degree `q + 1`; extending to
integer cochain degrees and applying the two additive functors gives a
strictly perfect model with bounds `-r` and `0`. For every point, choose the
whole scheme and use `mapDerivedCategoryFactors.app` to identify the model
with the restricted derived object. This implements the existing node's route;
no DAG or interface changes are needed.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.affine_perfect_koszul_principal_unit_perfect`
(node `lem-sc-affine-perfect-koszul-principal-unit-perfect`).

The private helpers `koszul_term_free`, `koszul_term_zero`, and
`shifted_koszul_strictly_perfect` are proved. There are no sorries left in
the item and no holes added elsewhere: 1 closed, 0 added.

The file compiles without warnings using the prescribed `lcompile.py`.
The finite-basis construction allows empty bases and the zero ring. For `r = 0`
every shifted term is zero. Perfectness does not require the positivity of the
exponent, but the existing `he : 1 ≤ e` hypothesis and all other binders remain
unchanged.

## No longer needed

None of the original imports, nodes, or modules are removed. Both public
imports remain necessary for the statement. The temporary proof-only import
`Mathlib.Algebra.Homology.Embedding.CochainComplex` was removed after checking
that the remaining imports supply the extension lemmas. No geometric support,
contracting-homotopy, or augmentation-isomorphism result is imported: the proof
only uses the finite-free perfectness route already stated in the node.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The brief's predicted long argument was already
available almost verbatim for the ordinary Koszul complex in the library.
Adapting the term degree from `q` to `q + 1` suffices for the shifted complex.
The existing node's finite-free, boundedness, and perfectness argument is kept,
and the unit record has no realized step that this proof bypasses.

## Second reading by D3

1. Compared the delivered module with the repository version. The theorem signature is byte-for-byte unchanged; the only interface-level difference is the proof-only `Mathlib.LinearAlgebra.ExteriorPower.Basis` import, and no declarations or definitions used by other modules were altered. Verdict: pass.

2. Compiled the module with `lcompile.py` successfully and checked `#print axioms` for the target. It reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. Verdict: pass.

3. The three private helper theorems are proved directly and introduce no split-off statements or DAG nodes. The target statement remains exactly the existing node statement, with no added hypotheses or weakened conclusion. Edge cases including an empty finite basis and `r = 0` are covered by the finite-basis and zero-object arguments. Verdict: pass.

4. The proof follows the node route through finite free terms, vanishing outside the bounded range, and strict perfectness on the affine scheme. The proof-only import is used for the exterior-power basis; the temporary cochain embedding import from the worker's exploratory version is absent. No old proof dependency or module can be removed. Verdict: pass.

5. The DAG node's statement, proof dependencies, and proof origin agree with the proof and no node changes are required. The unit route is preserved: the shifted Koszul complex is shown bounded with finite free terms and then perfect by the affine strict model. Verdict: pass.

Changed after review: appended this second-reading record only; no Lean code or DAG files required repair.
