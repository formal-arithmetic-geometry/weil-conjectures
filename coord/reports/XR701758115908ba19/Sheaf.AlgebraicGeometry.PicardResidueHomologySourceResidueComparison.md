## What changed

Repaired the landed module by removing its import and use of the withdrawn
`PicardResidueHomologyGeometricNaturalityFixedPerIndex` module. Restored the
self-contained coefficient pullback construction and the original chosen-map
proof route from the preceding compiling revision. Public statements,
docstrings, and hypotheses are unchanged.

## Proved and sorry left

`picard_residue_homology_source_residue_comparison` remains proved.
`picard_residue_homology_chosen_geometric_maps` retains its existing `sorry`;
this repair only restores the compiling proof scaffold and does not claim to
prove the unfinished coherent comparison argument. No new declarations or
sorries were added.

## No longer needed

The withdrawn geometric-naturality import and dependency are no longer used.
The restored route uses its original coefficient-map helpers and imports:
`AffineKFlatResiduePullbackModel`, `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`,
`WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat`,
`LocalizedStrictPerfectResidueHomology`, `RelativeMVMaps`, and
`Picard.CanonicalSinglePullbackComparison`.

## Where the brief, the DAG or earlier work was wrong

The landed proof referenced `picard_residue_homology_geometric_naturality_fixed_positive_per_index`,
but the imported module is withdrawn and contains no declarations. This caused
the reported unknown-identifier and malformed `rcases` errors. The DAG proof
route is restored to match the compiling module.

## Second reading by XR701758115908ba19

1. **Compiler failures and touched files.** Compared the sandbox module and both scoped DAG nodes with `/home/ubuntu/weil-conjectures-sheaf-XR701758115908ba19`. The withdrawn geometric-naturality identifier and its import are absent; the original coefficient-map scaffold is restored. The touched Lean file compiles with `python3 /home/ubuntu/weil-launcher/lcompile.py` in 22.6 seconds.

2. **Statements, targets, and mathematics.** The theorem statements, hypotheses, conclusions, source-residue statement, chosen-map statement, proof dependencies, unit route, and target names are byte-for-byte preserved against the repository. The only Lean change is removal of an unused import; the restored helpers and proof scaffold match the compiling source route.

3. **Proof integrity.** The source-residue comparison remains proved. The chosen-geometric-maps theorem retains its pre-existing named `sorry`, which the report declares; no new `sorry`, axiom, unsafe, opaque, implemented_by, or extern workaround was added. The remaining hole is not hidden in a definition.

4. **DAG and pruning.** The scoped DAG statements and dependencies agree with the repaired Lean file; no unneeded dependency or unit route was changed. The attempted withdrawn naturali​​ty dependency is not present in the sandbox repair.

5. **Delivery checks.** `deliver3.py ... --no-push` returned `OK (dry run)` and reported commit `53a190d4e6`; its only note concerns a `reviewed_proof` field not owned by this delivery. No importer or preflight failure remains.

I changed only this independent-reading report and the required `.check` marker; no source proof or declaration was modified during review.
