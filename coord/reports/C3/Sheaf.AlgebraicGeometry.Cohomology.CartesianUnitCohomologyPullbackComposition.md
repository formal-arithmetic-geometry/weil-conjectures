## What changed

Replaced the entire proof of `cartesian_unit_cohomology_pullback_comp`, without changing
its signature. The proof combines coefficient naturality, cohomology-map composition,
`structuralUnitCoefficient_comp`, `inverseImageCohomology_comp`, and the first cartesian
projection identity. Added the two helper modules as proof-only imports. No existing
interfaces or definitions change. The local canonical-instance registrations and the
file-local transparency option are recorded in
`coord/changes/cartesian-unit-cohomology-local-elaboration.md`, as required by the
delivery checker for added elaboration commands. The coefficient helper is proved by applying the
composite abelian adjunction, its mate identity, the module unit adjunction identity,
and extensionality on opens. The generic inverse-image cohomology step is split off. Its planned Ext composition
comparison is now explicitly imported as a proof-only dependency.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.Modules.cartesian_unit_cohomology_pullback_comp`
(node `lem-pbc-cartesian-unit-cohomology-pullback-comp`). Added and proved
`AlgebraicGeometry.Scheme.Modules.structuralUnitCoefficient_comp`
(node `lem-pbc-structural-unit-coefficient-composition`). The only new hole is
`AlgebraicGeometry.Scheme.Modules.inverseImageCohomology_comp`
(node `lem-pbc-inverse-image-cohomology-composition`). This is a decomposition:
one original hole closed and one strictly smaller, coefficient-free hole added.
The item itself contains no sorry. Its transitive proof still depends on the
new named hole; it is not claimed axiom-free. No data is chosen from an unproved theorem.

## No longer needed

No existing DAG proof dependency is globally pruned. The direct proof-only import
`Sheaf.AlgebraicGeometry.Cohomology.InverseImageCoefficientComposition` is replaced by
helper imports that publicly supply its definitions, so its module remains needed.
The old direct proof dependency `lem-pc-coefficient-unit-composition` is no longer
used as a theorem by the item; its module remains needed through the helpers.
The theorem `coefficientUnit_comp` is not needed by the actual coefficient proof;
only that module's constructions `coefficientUnit` and `invImageComp` are used.
Removed the earlier attempt's sandbox copies of `UnitCohomologyPullbackLinear` and
`InverseImageCoefficientComposition`, the unused `CartesianUnitCohomologyPullbackCompositionMapComp`
module, and the restatement `cartesian_unit_cohomology_pullback_comp_core`.
No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier core theorem repeated the original statement and was not a reduction;
its proof by rfl did not prove the requested equality. Both artifacts were discarded.
The coefficient identity can be stated as a sheaf-morphism equality without any
cartesian square, affine base, cohomology degree or cohomology class, and has now
been proved. The second step is isolated for arbitrary abelian sheaves with no
structural coefficients. Edge cases (identity morphisms, empty schemes, zero rings,
zero sheaves and degree zero) require no extra hypotheses. Mathlib searches found
individual adjunction and Ext APIs; LeanSearch was unavailable. Existing docstrings
and theorem signatures are preserved.

## New nodes

`lem-pbc-structural-unit-coefficient-composition`: the coefficient-only portion of
step 1, in `StructuralUnitCoefficientComposition.lean`, fully proved.

`lem-pbc-inverse-image-cohomology-composition`: the coefficient-free portion of step 2,
in `InverseImageCohomologyComposition.lean`, with the complete adjunction/Ext proof
in its docstring and node. It is strictly part of the argument and does not restate
the cartesian theorem. The record
`coord/changes/cartesian-unit-cohomology-local-elaboration.md` documents the module-local
elaboration commands; all existing signatures and downstream meanings are unchanged.


## Second reading by C3

1. **Interfaces: PASS.** Compared the delivered item with the repository using
   `diff -u` and checked the existing theorem signature byte for byte. The only
   existing declaration has exactly its original parameters, hypotheses and
   conclusion; its docstring is unchanged. No definitions or challenge statements
   change. The item adds only proof imports and module-local elaboration settings,
   already covered by the change record. Both new modules have their own statements.
2. **Proofs and axioms: PASS as a decomposition.** All three files compiled locally
   through `lcompile.py --all`. A scratch copy importing the three modules checked
   `#print axioms` for every delivered declaration. `structuralUnitCoefficient_comp`
   uses only `propext`, `Classical.choice`, and `Quot.sound`. The item and
   `inverseImageCohomology_comp` additionally use `sorryAx`, as reported. The only
   textual sorry is the entire proof of that public named theorem. No forbidden
   declaration, holed definition, or choice from an unproved existence theorem occurs.
3. **Split statement: PASS.** Read the definitions of `constIso`, `invImageComp`,
   and `Sheaf.H.mapFunctor`, and the generic Ext composition comparison. The sole
   hole is the inverse-image portion of the argument for any abelian sheaf, with
   no module coefficient or cartesian-square conditions; it does not restate the
   item. Its docstring and node give the constant-comparison coherence identity
   and the Ext associativity argument. For identity arrows, the adjunction
   comparisons give the identity law; zero sheaves give zero classes; empty
   schemes introduce no extra hypothesis; in degree zero the assertion is
   composition of section pullback. Read [Stacks 01F7](https://stacks.math.columbia.edu/tag/01F7)
   as the source for the functorial cohomology maps. Independent searches used
   LeanFinder's query “Successive exact inverse image actions on sheaf cohomology
   agree with the composite inverse image under the canonical adjunction comparison”,
   Loogle, and `rg` with `mapFunctor`, `constant`, `pullback`, and `comp`. Found generic
   adjunction APIs and the existing Ext comparison, but no direct matching theorem.
   The existing structure-sheaf pointwise and étale composition theorems specialize
   to different coefficients or sites; their proofs confirm the same constant
   coherence argument, and do not supply this arbitrary-sheaf statement directly.
4. **Route and pruning: PASS.** Followed the proof from its unfolded linear maps
   through coefficient naturality, `H.map_comp_apply`, the proved coefficient
   identity, the remaining inverse-image step, and the first projection identity.
   The coefficient proof applies the composite adjunction directly and ends by
   extensionality on opens; it need not invoke `coefficientUnit_comp`. The old
   direct dependency is explicitly identified above, while its definitions keep
   the module reachable. Public imports supply names in signatures, and the
   helper/Ext proof imports are private imports. Checked `dag/units/sk-thm-p1.json`
   and its `realized` statement and step nodes: none is bypassed or changed.
5. **Nodes: PASS after repair.** The original node differs only in `proof`,
   `proof_deps`, and `proof_origin`; the Lean statement remains unchanged. For all
   three nodes the union of step `uses` equals `proof_deps`, and the Lean statement
   records match the actual signatures (the original record normalizes whitespace).
   Both new nodes are absent from the repository and carry source, searches,
   creation, blueprint ancestry, chapter, unit, and Lean records. Their dependencies
   refer to the constructions used; the open inverse-image proof also names the
   existing generic Ext comparison.

Second-reading change: added the missing proof-only import
`Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison` to
`InverseImageCohomologyComposition.lean`, aligning its planned proof with its DAG
proof dependency. Clarified the removed direct DAG dependency in this report.
No theorem body or signature required repair. One original hole is closed and one
strictly smaller hole is added: net zero holes, with no globally pruned module.
