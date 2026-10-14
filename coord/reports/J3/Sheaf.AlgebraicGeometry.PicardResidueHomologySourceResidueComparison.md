## What changed

Replaced the remaining proof hole in
`Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison` by reuse of
`picard_residue_homology_geometric_naturality_fixed_positive_per_index` and
`perfect_affine_map_representative`. The existing per-index theorem supplies one
source equivalence for the whole family and compatible target equivalences and
derived arrows. The representative theorem supplies actual chain maps. Applying
the per-index equation to those representatives proves the required square.

The case `n = 0` composes the already proved source residue comparison and source
fibre comparison; all target data and equations are eliminated with `Fin.elim0`.
Both public theorem signatures, their visibility and all public imports stay
unchanged. Removed the unused private coefficient-map construction and its two
projection helpers. Updated the chosen-geometric-maps node's proof and proof
edges to the route actually used.

This is reuse of an existing, corrected stronger comparison statement, not a new
split. It does not finish the geometric comparison theory underneath that
statement. The module compiles through `lcompile.py`; the delivery dry run runs
its axiom and dependency checks.

## Proved and sorry left

Closed the module's one original hole:
`AlgebraicGeometry.Scheme.picard_residue_homology_chosen_geometric_maps`
(node `lem-sc-picard-residue-homology-chosen-geometric-maps`).

`AlgebraicGeometry.Scheme.picard_residue_homology_source_residue_comparison`
was already proved and its proof is unchanged. No `sorry` remains in the item's
module. No new theorem, new hole or split-off module is added.

The proof intentionally uses the existing open theorem
`AlgebraicGeometry.Scheme.picard_residue_homology_geometric_naturality_fixed_positive_per_index`
(node `new-picard-residue-homology-geometric-naturality-fixed-per-index`).
Its remaining work is the coherent derived residue/base-change/cohomology
comparison and its naturality. Its interface was corrected on 2026-10-14 to
choose compatible comparisons together, and the present proof uses exactly
those corrected quantifiers. The new import adds that existing hole to this
item's import closure while removing the upper direct hole; this is not a claim
of a net hole decrease in the target closure or an axiom-free full comparison.

## No longer needed

Removed these seven direct proof imports:

- `Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel`
- `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`
- `WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat`
- `Sheaf.AlgebraicGeometry.LocalizedStrictPerfectResidueHomology`
- `Sheaf.AlgebraicGeometry.RelativeMVMaps`
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison`
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`

The source-residue theorem still uses the source-model and quotient-model
modules, so their underlying algebraic comparison results remain needed through
those imports. The chosen-geometric theorem no longer directly needs
`lem-sc-localized-strict-perfect-residue-homology`,
`new-picard-residue-quotient-model-homology`,
`lem-sc-affine-residue-cycle-homology-map`,
`def-pc-derived-direct-image` or `lem-pc-module-pullback-adjunction` as proof
edges; the direct-image and quotient notions still occur in its statement.

Relative to this module's previous import closure, these Sheaf modules are
absent after the change:

- `Sheaf.AlgebraicGeometry.LocalizedResidueHomology`
- `Sheaf.AlgebraicGeometry.LocalizedStrictPerfectResidueHomology`
- `Sheaf.AlgebraicGeometry.OpenModuleStalkFreeProjective`
- `Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor`
- `Sheaf.AlgebraicGeometry.RelativeMVMaps`
- `Sheaf.AlgebraicGeometry.ResiduePullbackGlobalSections`
- `Sheaf.Topology.PointModuleEvaluationEquivalence`

The closure also drops the direct reach to
`Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts`. These modules remain
reachable through other target branches in the repository snapshot; no global
module withdrawal is claimed. The old geometric-naturality wrapper modules
`PicardResidueHomologyGeometricNaturalityFixed`,
`PicardResidueHomologyGeometricNaturality` and the geometric-comparison source
wrapper are not imported: only the per-index theorem is reused.

## Where the brief, the DAG or earlier work was wrong

The unfinished proof reconstructed the coefficient arrows but then left the
entire coherent comparison square open. An existing library statement already
provides stronger naturality for every chain representative, with the shared
source comparison required here. Reconstructing the coefficient arrows again
is unnecessary for this theorem. The direct route uses that statement and then
chooses chain representatives; it preserves the unit's mathematical route and
all the original hypotheses, including the empty family.

Searches were run with `msearch.py`: LeanFinder for naturality of derived fibre
homology under proper flat base change (eight generic pullback/section naturality
hits); Loogle for `DerivedCategory.Q.map, CochainComplex` (identifier unavailable
in that search service); and grep for homology-map naturality and derived
quotient maps (generic localization and homology results). Repository `rg`
located the exact corrected per-index statement. Reading its full signature
confirmed that its conclusions supply every input to the representative step.
No claim that the searches prove the geometric comparison is made.

## Second reading by J3

1. **Interfaces and accidental changes.** Compared the delivered module and node with the repository versions. Both public theorem signatures are byte-for-byte unchanged; only proof bodies, proof imports, and the node's proof route/dependencies changed. No target or definition was changed.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds with no errors. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. The proof uses the existing per-index naturality theorem and affine representative theorem, and the zero-index case is eliminated by `Fin.elim0`.

3. **Statements and dependencies.** No new statement or split-off node was added. The existing chosen-geometric-maps statement is unchanged and the updated node proof steps and `proof_deps` match the Lean proof. The open per-index theorem is used as an existing dependency rather than restated.

4. **Pruning and route.** Removed the private coefficient-arrow construction and its unused imports. The positive-family route preserves the unit's common-source comparison and chosen-representative route; the empty-family branch retains the source residue/fibre comparisons and adds no hypothesis.

5. **Search and mathematical review.** Repository search found no existing theorem duplicating the chosen statement. The reused per-index theorem has the required common source equivalence and representative naturality, so specializing it to the chosen maps proves exactly the displayed square. No new holes were introduced.

Changed during second reading: added this section and corrected the direct proof import list to include `TensorPullbackAdjunction` (seven imports removed). No Lean code or node statement required repair.
