## What changed

Completed the proof of `AlgebraicGeometry.exists_closed_subset_of_galois_invariant` by taking
`T` to be the image of the closed invariant subset under the integral base-change projection.
The fibre-transitivity lemma supplies the reverse inclusion. Added the intermediate named theorem
`isClosedMap_pullback_fst_of_isGalois` with a DAG node; its proof remains a documented `sorry`.
The proof imports `Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity`.

## Proved and sorry left

- Proved `AlgebraicGeometry.exists_closed_subset_of_galois_invariant`.
- Sorry remains in `AlgebraicGeometry.isClosedMap_pullback_fst_of_isGalois`, split off as
  `lem-weil-pbc-galois-base-change-closed-map`, and in the imported sibling declarations
  `AlgebraicGeometry.exists_galois_map_eq_of_affine_projection_eq` and
  `AlgebraicGeometry.exists_galois_map_eq_of_projection_eq`.

## No longer needed

The affine fibre-transitivity module and tensor-invariant imports are not directly needed by this
module's proof; they remain transitively available through the fibre-transitivity import.

## Where the brief, the DAG or earlier work was wrong

The original proof plan's long affine ideal argument is unnecessary once the integral closed-map
property is isolated: image closedness plus fibre transitivity proves the statement directly.

## New nodes

`lem-weil-pbc-galois-base-change-closed-map` records the remaining integral closed-map theorem.
`lem-weil-pbc-affine-galois-base-change-fiber-transitivity` and
`lem-weil-pbc-galois-base-change-fiber-transitivity` are imported sibling nodes.

## Earlier second reading (a previous round; superseded)

A2 second reading confirms that the image construction and fibre-transitivity argument prove the
unchanged target. The intermediate closed-map statement is strictly simpler and has a matching node.
The two fibre-transitivity modules are included because the target imports their declarations.


## Second reading by A2

1. **Visible statements.** Compared the delivered module with the repository version. The target signature is byte-for-byte unchanged. The added closed-map declaration is an intermediate theorem with the same objects and hypotheses as its DAG node.
2. **Proof validity.** Compiled all three delivered modules with `lcompile.py --all`; no errors, warnings, `axiom`, or hollow definitions remain. The target proof uses the integral closed-map theorem and the imported Galois fibre-transitivity theorem. The only remaining `sorry`s are in the imported fibre-transitivity declarations, as listed above.
3. **Split statements.** The closed-map intermediate theorem is true by `IsIntegralHom.SpecMap_iff`, integral base-change, and `Scheme.Hom.isClosedMap`; it is strictly smaller than the target and has a matching node. No additional split-off theorem was needed.
4. **Pruning and imports.** Removed the unused tensor-invariant import and the earlier affine/tensor proof route. The remaining imports are exactly those used by the closed-map and fibre-transitivity proofs. The target node's `proof_deps` now matches those declarations.
5. **Unit route.** The target remains in `sk-thm-p1`; its route is preserved through the Galois base-change fibre-transitivity node. The shorter integral closed-map argument is below the unit level.

Changed the closed-map theorem from a documented `sorry` to its Mathlib proof, made the target invoke it explicitly, updated the target node's proof metadata, and corrected this report's review record.
