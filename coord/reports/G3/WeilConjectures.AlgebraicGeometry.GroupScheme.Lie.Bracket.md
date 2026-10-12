## What changed

Proved `AlgebraicGeometry.GrpObj.toMixed_bijective` by extracting the constant and mixed
coefficients for injectivity, and reconstructing a point from its mixed-coefficient derivation
for surjectivity. The new proof-only import is
`Sheaf.AlgebraicGeometry.GroupScheme.MixedCoefficientDerivation`. Its single theorem
`AlgebraicGeometry.GrpObj.exists_mixedCoefficientDerivation` is fully proved: the two axis
conditions kill the pure coefficients, coefficient extraction verifies additivity, the Leibniz
law and restriction compatibility, and the morphism-over-S condition proves base annihilation.
The derivation is specified on every section; the proof chooses no arbitrary construction data.

The input snapshot also already contained complete proofs of `commutator_mem_mixedPoints`,
`infPointsMap_infBracket`, and `infBracket_mem_range_infPointsMap`, and the proved private
helper `mixedEquiv_infBracket`. These proofs are retained. The current checkout comparison
shows these three declarations as closed holes as well; they are inherited work, not new proofs
by this worker. All existing declaration signatures and definitions are unchanged.

Both delivered modules compile with lcompile.py, with no compiler warnings. The construction
works for arbitrary schemes, including the empty scheme and nonreduced bases; it adds no
field, smoothness, affineness, or characteristic assumptions.

## Proved and sorry left

Newly closed: `AlgebraicGeometry.GrpObj.toMixed_bijective`
(node `lem-ag-mixed-point-bijection`). Newly proved helper:
`AlgebraicGeometry.GrpObj.exists_mixedCoefficientDerivation`
(node `lem-ag-mixed-coefficient-derivation`). No holes added; this is a proof, not a decomposition.

Retained complete proofs, also closing holes against the current checkout:
`AlgebraicGeometry.GrpObj.commutator_mem_mixedPoints`,
`AlgebraicGeometry.GrpObj.infPointsMap_infBracket`, and
`AlgebraicGeometry.GrpObj.infBracket_mem_range_infPointsMap`.

The five remaining sorry expressions are unchanged: `add_lie`, `lie_add`, `lie_self`, and
`leibniz_lie` in `AlgebraicGeometry.GrpObj.instLieRingLie`
(`instance instance : LieRing (Lie G)`), and `lie_smul` in
`AlgebraicGeometry.GrpObj.instLieAlgebraLie`
(`instance instance : LieAlgebra Γ(S, ⊤) (Lie G)`). Their existing blueprint location is
`sk-d-tangent`, under `def-wf-lie-algebra-derivation`. No sorry remains in the new helper module.

## No longer needed

None of the item's original imports can be removed: its Lie structures need
Mathlib.Algebra.Lie.Basic, its definitions need InfPointsEquiv, and the rescaling proof needs
the presheaf-differential import. No existing node or module is pruned.

The new coefficient lemma requires only Lie.InfPoints, not Lie.InfPointsEquiv or Bracket.
The matrix-specific lemmas MatrixSubgroupLieBracket and MixedCommutatorTangent are unnecessary
for this general-base bijection and are not imported. They are not globally declared pruned,
since other consumers may still need them.

## Where the brief, the DAG or earlier work was wrong

The available matrix lemmas require hypotheses absent from this module and cannot prove its
general-base Lie-ring laws by specialization. The source bijection did not have a direct node;
the two new nodes record its actual proof and the coefficient lemma it uses. The unit route is
unchanged. LeanSearch was attempted but returned an Internal Server Error; LeanFinder and
source searches were available and found no exact scheme-level coefficient theorem.

Scalar compatibility was explored in scratchpad/Scale.lean. The point-scaling argument compiled
in isolation, but its integration exceeded the 60-second file limit. It is not delivered or
counted as a closed hole, and the original scalar instance remains unchanged.

## New nodes

`lem-ag-mixed-coefficient-derivation` records the fully proved relative presheaf derivation
obtained from the mixed coefficient of a point trivial on both axes. Its module is
Sheaf.AlgebraicGeometry.GroupScheme.MixedCoefficientDerivation, with no sorry and no import
cycle. Its argument explicitly verifies all presheaf-derivation fields.

`lem-ag-mixed-point-bijection` records the existing declaration toMixed_bijective and its
new coefficient-extraction proof. It depends on the first node for surjectivity and constructs
the inverse with the already proved pointOfDerivation API. Both nodes belong to sk-d-tangent
in sec-algebraic-groups-lie-algebras. No interface change record is needed.

## Second reading by G3

1. Compared the delivered Bracket module with the repository version. Existing declaration signatures and definitions are unchanged; the only added import is the proof-only `MixedCoefficientDerivation` import, and the two new declarations are recorded in the new DAG nodes.
2. Compiled both delivered modules with `lcompile.py`; compilation succeeds with no warnings. The helper contains no `sorry`; the five remaining `sorry`s are the named Lie ring and Lie algebra laws listed above. No forbidden declarations or hollow definitions were found.
3. Checked the new statements and DAG records. The mixed-coefficient derivation statement matches the theorem's type and its coefficient construction determines the derivation; the bijection statement is unchanged and the proof uses the helper exactly for surjectivity. Searches and repository scans found no existing duplicate theorem.
4. Reviewed the proof route and imports. The helper is imported privately for proof use, and the unit route through `toMixed_bijective` and the mixed-coefficient construction is preserved. No unused imports or prunable proof dependencies were found.
5. Checked the node metadata, proof steps, dependencies, source notes, and realized unit `sk-d-tangent`; they agree with the Lean declarations and proofs.

No changes were required during second reading.
