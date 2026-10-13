## What changed

Replaced the sorry in `AlgebraicGeometry.affine_chart_canonical_hom_naturality` with
an unchanged-signature proof from normalized section models and a tensor-coordinate
recovery criterion. The proof obtains the limit and stage Hom equivalences, calculates
the conjugated scalar extension on every unit tensor using
`colimitScalarExtensionComp_one_tmul` and `ModuleCat.ExtendScalars.map_tmul`, and applies
the criterion with the models' sectionwise formulas and ring compatibility.

Added proof-only imports of `Sheaf.AlgebraicGeometry.AffineChartNormalizedSectionModels`
and `Sheaf.AlgebraicGeometry.AffineChartTensorRecovery`. Each new module has its own
node, source and complete proof in words. The first isolates object reconstruction and
full faithfulness; it makes no assertion about scalar extension of morphisms. The
second is an independent conditional tensor-coordinate criterion and constructs no
Hom equivalences or inverse-limit objects. Neither restates the original theorem.
The existing node now follows this proof.

The scalar-extension calculation uses explicit congruence and transitivity rather than
rewriting inside the dependent geometric types. No existing signature, visibility,
definition, or public import was changed. No other module was adapted.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.affine_chart_canonical_hom_naturality`
(node `lem-pc-affine-chart-canonical-hom-naturality`). Its proof is complete from the two
named lower statements. The four existing scalar-extension definitions and lemmas remain
proved and unchanged.

Also fully proved `AlgebraicGeometry.affine_chart_tensor_coordinate_recovery`
(`lem-pc-affine-chart-tensor-coordinate-recovery`) and its private supporting lemmas.
The proof uses two tensor inductions, square-unit coherence, and affine pullback
Hom extensionality. It introduces no sorry and needs only the three standard axioms.

The sole added hole is `AlgebraicGeometry.affine_chart_normalized_section_models`
(`lem-pc-affine-chart-normalized-section-models`).

This is a decomposition: one original upper hole closed and one strictly smaller
construction hole added; the generic naturality argument is fully proved.
The item's module contains no remaining sorry. No definition contains a sorry.

The new statements were checked on zero modules, zero rings and empty affine charts.
Their arguments use tensor generation, affine reconstruction and universal properties;
none requires a nonzero scalar, a nonempty chart or finite presentation. Equivalent
preorder indices are included: the starting representative need only be equivalent to
j, so reconstruction uses an isomorphism rather than assuming equality of indices.

## No longer needed

None of the original public imports can be removed: they occur in definitions or the
unchanged theorem statement. The original proof dependencies
`def-pc-chart-ordinary-map-recovery`, `def-pc-fibre-product`,
`new-affine-chart-upper-tail-limit-data` and `pqf-def-coherent` remain needed in the
statements or in the new lower arguments. They are not globally pruned. The two new
proof imports are both used. No module is claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The old proof plan describes affine reconstruction and pullback coherence in prose,
but its cited definition nodes do not supply the needed normalized section interfaces.
The two new statements expose those distinct steps, and the second is now proved. In particular, the construction
of section/Hom models is separated from the tensor-generator calculation that proves
naturality. The latter is fully formalized, including the scalar law for unit tensors,
the inverse comparison on generators, tensor induction for arbitrary target tensors,
and the affine source generator argument; no arbitrary family of comparison isomorphisms is assumed coherent.

Read the Stacks source at Tags 01ZR and 01I6 (affine reconstruction, fully faithfulness,
and scalar-extension pullback), and 0095/0096 (inverse-image functoriality underlying the
pullback comparisons). Searches via LeanFinder, Loogle, grep, the source modules
`PullbackTilde`, `PullbackUnit`, `FaithfullyFlatDescent`, and `AffineHom`, and the whole blueprint did not find an
exact existing upper-tail comparison or tensor-coordinate criterion. LeanSearch returned
Internal Server Error and is recorded as unavailable, not as an absence result.

## New nodes

`lem-pc-affine-chart-normalized-section-models`, in
`Sheaf.AlgebraicGeometry.AffineChartNormalizedSectionModels`, isolates the actual starting
chart reconstruction, limit/stage ring maps, normalized semilinear section equivalences
and the resulting fully faithful Hom equivalences. Its same ring-map compatibility is
needed for the scalar calculation, but it states no recovery of morphisms.

`lem-pc-affine-chart-tensor-coordinate-recovery`, in
`Sheaf.AlgebraicGeometry.AffineChartTensorRecovery`, isolates recovery for given coordinate
models and given maps satisfying an equality on source unit tensors. It is independent
of directed systems and colimits and does not assert existence of the models.

Both inherit the original node's chapter, unit and nearest blueprint ancestor. No unit
statement or realized proof step is bypassed, and the updated dependency route has no
cycles. No change record is needed because all existing interfaces are unchanged.

`Modules.AffineHom` cannot be imported here: its broad cohomology imports reach the
original item and would close an import cycle. The actual proof instead restricts to
the affine spectrum and uses `hom_ext_of_isQuasicoherent_Spec` from
`Modules.FaithfullyFlatDescent`, whose import direction was checked. This does not alter
any existing module. The geometric square calculation is first proved with abstract
scheme maps, then specialized to charts in the same module, so tensor induction does
not repeatedly reduce concrete chart constructions.

## Second reading by R2

1. I compared the delivered modules with the repository versions. Existing declarations and target signatures are unchanged; the two added modules contain the reported new declarations only. The import adjustment in `AffineChartTensorRecovery` makes `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` public for its exposed `IsQuasicoherent` hypotheses and keeps `Mathlib.AlgebraicGeometry.Modules.Tilde` proof-only.

2. I compiled the normalized section models successfully and compiled the tensor recovery module successfully in isolation. The full sandbox compilation reached the tensor module but hit the local 60-second timeout on one run; a subsequent isolated compile completed in 59.1 seconds. No compiler errors or warnings were emitted in successful runs. The normalized section-model theorem remains the sole named sorry, with its node and proof docstring; the target theorem and tensor recovery theorem contain no sorry, axiom, unsafe, opaque, extern, or implemented_by declarations.

3. The tensor-coordinate recovery statement is a strict lower-level criterion: it assumes concrete normalized models and proves only `chartOrdinaryMapRecovery`; it does not restate the target or construct Hom equivalences. The normalized section-model statement separately supplies those models and their properties. I checked the zero-module, zero-ring, empty-chart, and equivalent-index edge cases described in the report; no extra hypotheses or weakened conclusions were introduced.

4. The target proof follows the reported route through normalized section models, canonical scalar-extension tensor normalization, and tensor-coordinate recovery. The unit route is retained. No old proof dependency is removed; both proof-only imports are used. The only change made in this second reading is the import visibility refinement above.

5. The DAG nodes agree with the Lean declarations and proof dependencies. The new node records include source, proof steps, searches, blueprint, module, declaration, and the split status. The target node records the updated lower-level route and retains its original statement and chapter/unit.

The delivery is ready for the stage-3 dry run; the local compile-time variance is recorded as a tooling limitation rather than a proof or statement change.
