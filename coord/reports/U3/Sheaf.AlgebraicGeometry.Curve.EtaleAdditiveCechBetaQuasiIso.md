## What changed

The original statement and all its hypotheses stay unchanged. The proof now constructs the lifted coefficient map into the resolution-zero row of the transposed bicomplex, proves that its vertical differential vanishes, constructs its total augmentation as a chain map, applies `HomologicalComplex₂.quasiIso_of_column_augmentation`, and composes with the signed total transpose. The sign on the (n,0) summand is explicitly +1, so the resulting map has precisely `additiveCechBeta` coordinates.

Added `EtaleAdditiveCechCoefficientMap` with the actual product maps (no existence witness or hollow data), and `EtaleAdditiveCechCoefficientColumns` with the fixed single-column quasi-isomorphism obligation. Their imports are public because the supporting statements use their definitions; the target's new imports are proof-only. The natural-number symmetry is a private, fully proved local helper.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.Modules.exists_additiveCech_beta_quasiIso`, by a complete Lean proof from two new smaller obligations and the existing first-quadrant criterion. Also proved `AlgebraicGeometry.Scheme.Modules.additiveCechCoefficientMap_vertical` directly from `I.ι_f_zero_comp_complex_d`.

Added exactly two named holes:

- `AlgebraicGeometry.Scheme.Modules.additiveCechCoefficientMap_comm`, node `lem-pbc-additive-cech-coefficient-horizontal`: only horizontal differential compatibility; no quasi-isomorphism, affineness, or totalization.
- `AlgebraicGeometry.Scheme.Modules.additiveCechCoefficientMap_column_quasiIso`, node `lem-pbc-additive-cech-coefficient-columns`: only a fixed single-column augmentation; no total chain map or total quasi-isomorphism.

There is no sorry left in the item's module and none in any definition. This is a decomposition (one original hole closed, two holes added), not a net reduction in holes. The full sandbox compiles; the delivery dry run checks its declarations and axioms.

## No longer needed

No original import was removed: the public normalization import is needed for the original statement. The target's direct proof dependency on `lem-sc-etale-affine-open-cech-resolution-columns` / `Sheaf.AlgebraicGeometry.EtaleAffineOpenCechResolutionColumns` is pruned. Its abstract homology isomorphism is unnecessary for this route, which uses the fixed augmented-column maps instead.

The original `lem-sc-etale-tensor-unit-sections-natural`, `new-etale-affine-tensor-cech-vanishing`, and `lem-weil-pbc-cech-vanishing-criterion` remain in the new column obligation's proof plan; they are not claimed pruned. `lem-sc-first-quadrant-column-augmentation` remains used, as a generic homological tool. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned affine-open column theorem gives only a nonempty abstract degree-zero homology isomorphism and positive zero homology; it does not assert compatibility with the prescribed unit coefficient coordinates. Thus it cannot alone discharge the first-quadrant criterion's fixed augmented-column hypothesis. The new column statement fills precisely this missing interface, while the other new statement isolates the coordinate restriction identity. The totalization and signed-transpose argument is proved here rather than hidden in either new statement.

Read Stacks Tags 03P2, 01EQ and 0133. Checked empty index families, degree zero, empty intersections and repeated opens: the constructions have no cover hypothesis and preserve these cases. The natural-number total symmetry is copied as a local proved helper from `FirstQuadrantTotalComparisonFinite`; its existing helper is private. No definition or existing signature was changed and no forced adaptation is needed.

Searches: LeanFinder returned general quasi-isomorphism results but no fixed comparison; Loogle returned totalFlipIso and its inclusion equations; LeanSearch returned an Internal Server Error, recorded as unavailable. The search-wrapper grep returned no fixed coordinate declaration, and local rg found the existing module-sheaf comparison and abstract etale columns, whose signatures were read and differ as above.

## New nodes

`lem-pbc-additive-cech-coefficient-horizontal` is in `dag/nodes/sec-proper-base-change/lem-pbc-additive-cech-coefficient-horizontal.json`, realized in `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechCoefficientMap`. It states only horizontal compatibility of the actual product coordinate maps. The same module contains the real coefficient constructions and the proved vertical annihilation lemma.

`lem-pbc-additive-cech-coefficient-columns` is in `dag/nodes/sec-proper-base-change/lem-pbc-additive-cech-coefficient-columns.json`, realized in `Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechCoefficientColumns`. It states the quasi-isomorphism of the explicitly augmented vertical column. Its proof in words gives the positive affine vanishing, degree-zero kernel and exact product argument. Neither new statement repackages the target's conclusion.

No change record is needed: all existing statements, definitions and visibility are unchanged.

## Second reading by U3

1. Compared the target module with the repository using diff and compared the
   theorem signature byte for byte. The existing docstring, signature, definitions
   and visibility are unchanged. The existing node changes only proof,
   proof_deps and proof_origin. The two supporting modules and nodes are new.
   Verdict: no accidental interface change and no change record required.
2. Read every construction and proof. The coefficient map is an explicit product
   of actual additive maps, and the total chain map is constructed explicitly;
   no arbitrary witness of an unproved existence theorem is chosen as data.
   The vertical equation evaluates the resolution's augmentation identity.
   The total differential calculation uses both signs at (0,n), and the
   transpose calculation proves its sign at (n,0) is +1. The only local holes
   are the two named, documented obligations reported above. All three modules
   compile without errors or warnings. A scratch copy
   with #print axioms for all six public declarations shows only propext,
   Classical.choice and Quot.sound for the coefficient constructions and
   vertical theorem; the two obligations and the target additionally use
   sorryAx, as expected. The scratch copy was removed. Verdict: a genuine
   reduction conditional on those obligations, not an unconditional target proof.
3. Read both new statements and their docstring proofs, and checked their DAG
   signatures against the Lean text. Horizontal compatibility is ordinary
   naturality, without affineness; the column assertion is affine acyclicity
   plus the canonical degree-zero augmentation. Both are strictly smaller than
   the target: neither constructs a map into the total nor proves its total
   quasi-isomorphism. Degree zero, nonadjacent differentials, an empty index
   family, empty intersections and repeated opens cause no exception.
   Independently searched LeanFinder for induced Cech chain maps, Loogle for
   fromSingle₀Equiv, and grep for restrictFunctorΓ and rightDerivedZeroIsoSelf;
   also read the upstream Cech projection lemmas, module-sheaf beta comparison,
   and etale affine-column comparison. No existing declaration states either
   fixed coefficient obligation. Verified Stacks 03P2, 01EQ and 0133 directly.
   Verdict: true, necessary smaller obligations; neither admits an immediate
   application of an existing theorem to close it.
4. Reviewed the proof downward from the target. The first-quadrant criterion is
   used directly, and the total transpose is proved rather than split off.
   All added target imports are proof-only; supporting public imports supply
   their statement and definition types. No original import is removed.
   For completeness, all four old direct proof dependencies absent from the
   target's new proof_deps are: lem-sc-etale-affine-open-cech-resolution-columns,
   lem-sc-etale-tensor-unit-sections-natural,
   new-etale-affine-tensor-cech-vanishing, and
   lem-weil-pbc-cech-vanishing-criterion. The last three are retained in the
   new column obligation's plan, so only the first is pruned from that route.
   Read sk-thm-p1.json realized: this target and these auxiliary dependencies
   realize no unit statement or step that this reduction bypasses.
   Verdict: the unit route is preserved; this is a decomposition with holes
   closed minus holes added equal to -1, not a net proof advance or a claim of
   whole-library pruning.
5. Checked the three node records against their Lean declarations. The target
   steps correspond to the actual coefficient chain map, total augmentation
   criterion and signed transpose. The new nodes have their source, complete
   proof plans, searches, creation/blueprint records and exact Lean signatures.
   Verdict: nodes agree with Lean and retain the necessary acyclicity plan.

Second reading changed only this report: made the complete list of replaced
direct proof dependencies explicit and recorded the independent review. No
Lean proof or statement repair was necessary; both split obligations remain.
