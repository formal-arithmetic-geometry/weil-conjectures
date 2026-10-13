## What changed

Replaced the earlier cyclic induction proof by a stalk flat-counit decomposition.
The sole existing signature and both public imports of
`Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi` remain unchanged.
The proof obtains flat scalar-extension coordinates, proves K-flatness using
`CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat`, applies
`ModuleCat.scalarExtensionCounit_isIso_of_kFlat`, transports its homology map
through the coordinate square, and applies
`Scheme.Modules.epi_of_surjective_stalk`. All imports added to the item are
proof-only. No existing definition, interface, or other group's module changed.
The item's node now records precisely this route.

Added one new module, `Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel`,
for the remaining geometric computation. Its theorem asserts existence of a
bounded-above termwise flat complex and cohomology coordinates identifying the
canonical map with a universal scalar-extension counit. It does not assert an
epimorphism or an isomorphism of that counit. Its docstring and node describe the
affine calculation, separated Cech calculation, qcqs Mayer--Vietoris construction,
and localization. This calculation is strictly the geometric part of the proof;
the algebraic invertibility and global epimorphism argument are proved in Lean.
Witnesses are destructured in the theorem proof, never chosen in a definition.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.standard_flat_single_baseChange_homology_epi`
(node `lem-pc-standard-flat-single-base-change-epi`). No sorry remains in the item.

Added one hole:
`AlgebraicGeometry.exists_standardSingle_stalk_flat_counit_model`
(node `lem-pc-standard-single-stalk-flat-counit-model`), in
`Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel`.
Its proof is exactly `:= by sorry`.

This is a decomposition: one hole closed and one added, net zero before pruning.
The existing algebraic K-flat and universal-counit lemmas are used as proved
library declarations; no claim is made that all their dependencies are closed.
The rejected auxiliary degreewise-epimorphism declaration from the earlier attempt
is absent. No new axiom or hollow definition is introduced.

## No longer needed

Removed the earlier sandbox proof imports:

- `Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction`
- `Sheaf.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison`
- `Sheaf.AlgebraicGeometry.RelativeFlatModuleStalk`
- `Sheaf.AlgebraicGeometry.PullbackStalkTensorFlat`
- `Sheaf.Algebra.Homology.FlatBaseDerivedTensorComparison`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`

The item no longer directly needs its old proof-dependency nodes
`lem-pc-counit-stalk-condition-from-localized-comparison`,
`lem-pc-flat-base-derived-tensor-comparison`,
`lem-pc-pullback-stalk-tensor-flat`, `lem-pc-relative-flat-module-stalk`,
`lem-pc-rf-single-complex-qcqs-induction`,
`lem-weil-pbc-quasi-coherent-module-kernel`, and
`lem-weil-pbc-quasi-coherent-module-cokernel-closure`.
`def-pc-standard-single-base-change-map` remains a statement dependency/public
import but is not an additional proof import.
`Sheaf.Algebra.Homology.BoundedFlatKFlat` remains required.
No claim is made that the listed modules are globally unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong

The previous proof compiled against cached imports but failed the source cycle
check. The cycle begins with `SingleComplexQcqsInduction`, passes through
`SingleComplexOpenUnion`, the relative Mayer--Vietoris boundary constructions,
`DerivedBaseChangeMayerVietorisMaps` and `AffineGlobalHomBaseChangeMap`, then through
compact-generation/affine direct-image and proper-flat model modules, and returns
through `StandardFlatSingleBaseChange` to this item. The gate correctly rejects
that route; it is not a broken compiler. The separated canonical module theorem
cannot replace it because this item's hypothesis is only quasi-separatedness.

The earlier split-off degreewise-epimorphism lemma duplicated the QCQS induction
conclusion and was correctly removed. The new split instead states the geometric
flat-complex computation, with a canonical counit square and no assumed
invertibility. It leaves a real algebraic and stalk-detection argument in the item.
No upstream file was edited to break the cycle. The unit
`dag/units/sk-thm-picard-coherence.json` has empty realized statement/step lists;
its statement and route are unchanged.

Edge cases checked on the new statement: the zero module uses the zero complex;
empty A contributes no a; empty Y has zero direct image; negative degrees use
the same counit square. Arbitrary g is allowed because the complex is flat over
the old base, rather than requiring g to be flat. For a nonseparated qcqs source,
intersections are treated as quasi-compact separated opens of an affine chart,
not incorrectly assumed affine. There is no finite-presentation or properness
hypothesis hidden in the model statement.

## New nodes

`lem-pc-standard-single-stalk-flat-counit-model` records the bounded-above flat
stalk coordinates and counit equality. The source is Stacks Tags 0A1D and 0DJ9;
the worker expands their affine and Mayer--Vietoris calculations. The node includes
a self-contained statement, the verbatim Lean signature, four proof steps,
statement/proof dependencies, blueprint provenance, and searches of four kinds
(LeanSearch was unavailable; the other services/source search found no exact model).
There is no change record because no existing statement or definition changes.

## Second reading by T4

1. **Interface unchanged.** Compared both delivered versions against the repository with `diff`; the existing theorem signature and its public imports are byte-for-byte unchanged. The new module is an explicitly recorded split-off theorem, and its node matches the Lean declaration.

2. **Compilation and axioms.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The item contains no remaining `sorry`; the only new `sorry` is the named theorem `exists_standardSingle_stalk_flat_counit_model`, with its node and source/docstring. No forbidden declarations or hollow definitions were introduced. The final proof uses the stalk criterion, bounded-flat K-flatness, and the scalar-extension counit isomorphism.

3. **Statement review.** The split-off theorem is strictly a coordinate existence statement: it supplies a bounded-above termwise-flat complex, a universal derived scalar-extension pair, two cohomology isomorphisms, and the canonical commuting equality. It asserts neither epimorphism nor invertibility of the comparison, so it is not a restatement of the item. Its edge cases and absence of extra flatness or separatedness hypotheses are documented in the theorem docstring and node.

4. **Pruning and route.** The proof follows the unit route through the affine calculation and qcqs Mayer--Vietoris construction, then uses the existing algebraic K-flat and counit lemmas. The former cyclic induction imports are removed and listed under `## No longer needed`; the remaining proof-only imports are used by the elaborated proof. The unit record and existing item statement are unchanged.

5. **DAG agreement.** The item node's proof and `proof_deps` match the proof's model, K-flatness, counit, and stalk-epimorphism steps. The new node has source, statement, proof steps, dependencies, searches, Lean record, chapter, and unit fields. No existing declaration is weakened or altered.

Changed after this reading: added this review record only; no Lean proof or statement changes were needed.
