## What changed

The proof of `AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_naturality` in
`Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality` is replaced by a complete Lean
reduction following its original Ext route. Its signature and public imports are unchanged.
Three new modules are imported privately for proofs:
`ScalarCohomologyExtCoefficientNaturality`, `ScalarExtCupInverseImage`, and
`ScalarPullbackTensorCoefficient`, all under `Sheaf.AlgebraicGeometry`.

The proof applies the comparison equivalence's injectivity, uses coefficient naturality,
unfolds cup and pullback, cancels the equivalences, transports composition through exact
inverse image, combines degree-zero coefficient classes, and substitutes the tensor
coefficient square. It then postcomposes the inverse-image pairing identity with the target
tensor coefficient, using Yoneda associativity to finish. The DAG records this argument.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_naturality`
(node `lem-sc-scalar-cup-pullback-naturality`). This is a decomposition, not a complete
sorry-free proof of its mathematical dependencies.

Added three strictly smaller obligations, each in its own module with a source and proof
in words:

- `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtEquiv_map`
  (`lem-sc-scalar-cohomology-ext-coefficient-naturality`): a single coefficient map,
  with neither cup nor scheme pullback.
- `AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage`
  (`lem-sc-scalar-ext-cup-inverse-image`): the Yoneda pairing on arbitrary scalar sheaves,
  independent of O-module cohomology comparisons and normalized module tensor pullback.
- `AlgebraicGeometry.Scheme.Modules.scalarPullbackCoefficient_tensor`
  (`lem-sc-scalar-pullback-tensor-coefficient`): a square of sheaf morphisms,
  containing neither Ext classes nor cohomology degrees.

No sorry remains in the item. Three public named theorem sorries are added; no definition,
private declaration, axiom, or arbitrary choice of new data is introduced. Existing
operations and their existing proof dependencies are used unchanged. The decomposition
closes one upper hole and adds three lower holes, so its immediate hole-count delta is -2.

Edge cases: the coefficient comparison has no positive-degree restriction; the tensor
square uses no nonzero sections, nonempty schemes, quasi-coherence, or invertibility of
coefficient maps. The pairing identity admits arbitrary degrees and zero coefficients.
In degree zero these reduce to the same pure-tensor/unit formulas. The unit's realized
statement and steps are unchanged.

## No longer needed

No existing import or planned dependency module is pruned. The only original public import,
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, is needed for the signature
and definitions. Both original proof dependencies remain needed: the operations module
and `lem-weil-pbc-module-pullback-tensor` / `Sheaf.AlgebraicGeometry.ModulePullbackTensor`.
The latter is used through the coefficient-square obligation rather than as an immediate
proof dependency of the item's node. There are no unused new proof imports.

## Where the brief, the DAG or earlier work was wrong

The original two proof steps named only operation definitions and the module tensor-pullback
comparison; they did not supply declarations for inverse-image Ext pairing transport,
the scalar coefficient square, or comparison naturality. The delivery exposes those three
missing parts without changing any definition or statement. Existing generic Ext composition
lemmas provide the combining algebra, but do not themselves state these compatibilities.
LeanSearch returned an internal server error; LeanFinder, Loogle, and local library searches
were used. No exact alternative was found. The cited local Stacks TeX files are absent on
this machine; the official tag pages were read directly, including Tags 01DZ, 01F7, 01FD,
07MB, 0FKV, and 01CD. The new proof texts specialize their arguments to the library's
actual scalar definitions; they do not claim these exact Lean formulas occur verbatim
in the sources.

## New nodes

`lem-sc-scalar-cohomology-ext-coefficient-naturality` is stated in
`lean/Sheaf/AlgebraicGeometry/ScalarCohomologyExtCoefficientNaturality.lean`.
It is the missing naturality of the injective-resolution comparison for one coefficient map.

`lem-sc-scalar-ext-cup-inverse-image` is stated in
`lean/Sheaf/AlgebraicGeometry/ScalarExtCupInverseImage.lean`.
It isolates the exact inverse-image Yoneda tensor pairing, with arbitrary scalar sheaf
coefficient maps and the actual adjunction-derived oplax comparison.

`lem-sc-scalar-pullback-tensor-coefficient` is stated in
`lean/Sheaf/AlgebraicGeometry/ScalarPullbackTensorCoefficient.lean`.
It isolates the sectionwise normalized coefficient square required by the original plan.

No change record is required: no existing signature, definition, visibility, public import,
or exported elaboration attribute changes. All changes to the original module are in its
proof and proof-only imports.

## Second reading by M1

1. **Unchanged interface — pass.** Diffed the original module against the repository.
   The only changes are three plain proof imports, whitespace, and the proof body of
   `scalarCup_pullback_naturality`. Its entire declaration signature through `:=` is
   byte-identical. The original docstring, public import, definitions, visibility,
   and target statements are unchanged. The other three modules are new; no existing
   declaration is adapted and no change record is needed.

2. **Kernel proof and holes — pass as a decomposition.** Compiled all four modules
   in import order through `lcompile.py --all`: no errors or warnings (3.0, 7.0,
   7.1, and 25.7 seconds). Read the complete reduction: comparison injectivity,
   coefficient naturality, exact-functor composition, the coefficient square, and
   postcomposition of the inverse-image pairing identity give the original equality.
   Scratch-copy `#print axioms` for the original and all three new declarations
   reports only propext, Classical.choice, Quot.sound, and sorryAx, as expected
   from the remaining imported holes. The three reported new theorems are the only explicit sorries. There is no new
   definition or data choice, nor an axiom, unsafe/opaque declaration, extern,
   implemented_by, or skipped kernel check. The existing chosen moduleExtEquiv,
   scalarPullbackCoefficient, and module tensor comparison are specified by their
   cocycle/section formulas, rather than arbitrary witnesses of mere existence.

3. **Split statements — pass.** Read the actual definitions in
   `FieldLinearModuleCohomologyOperations` and the section normalization in
   `ModulePullbackTensor`. Coefficient naturality uses the specified evaluation-at-1
   cocycle comparison. The tensor square is an equality of sheaf morphisms and follows
   by adjunction, the specified pullback-unit section formula, and pure-tensor
   extensionality before sheafification. The inverse-image theorem concerns only the
   scalar Ext pairing and arbitrary postcomposition maps: exact tensor transport,
   the oplax comparison, its unit coherence, and Ext natural-transformation
   naturality give the identity. Its unit is the same constant-sheaf comparison as
   `scalarInverseUnitIso`. These are strict parts of the original argument, not a
   renamed copy of the original conclusion. Each has its own module, node, source,
   and full proof in words. Checked degree zero (ordinary tensor-map formulas),
   zero coefficient maps/modules (zero composites), and empty schemes (unique maps);
   none needs quasi-coherence or positive degrees. Reopened the official Stacks
   pages for Tags 01F7, 07MB, 0FKV, and 01CD; these support the resolution/tensor
   arguments, not verbatim copies of the Lean formulas.

   Independently searched with different wording using msearch LeanFinder
   (exact monoidal transport of Ext pairing; evaluation-at-one derived comparison;
   tensor pullback unit pure-tensor sections), Loogle (`Ext.mapExactFunctor`),
   and grep; also searched both local Lean roots. The generic
   `mapExactFunctor_comp_mk₀_natTransApp` and the upstream resolution comparison
   provide ingredients, not the three exact statements. The proved
   `exists_ext_rightDerived_cocycle_comparison` in
   `Sheaf.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison` gives a natural
   represented comparison, but identifying it with this module's chosen O-module
   cocycle comparison still needs an argument. No split statement closes by a
   direct application found in this reading; none was changed merely to ease proof.

4. **Route and pruning — pass.** Each of the three new plain imports is used by
   name in the proof. The sole public import supplies its signature and operations.
   No original module is pruned: the old tensor-pullback dependency remains needed
   by the coefficient-square node, although it is no longer an immediate
   proof_deps entry of the item. The report already distinguishes these two levels.
   Read `dag/units/sk-prop-av-cube.json`: its realized statement and step lists
   remain unchanged, and this reduction stays on the original scalar Ext route.

5. **DAG agreement — pass.** Checked every new Lean statement against its node,
   and the item's three proof steps against its proof body. The union of each
   step's uses equals proof_deps; proof_origin records this M1 reduction. The new
   nodes carry source, searches, status, creation, blueprint provenance, chapter,
   unit, and complete Lean records. They cite the operation definitions and, for
   the coefficient square, the normalized module tensor-pullback theorem actually
   required. No unrelated node field or unit record changes.

Second reading changes: appended this independent review and search findings;
no Lean or DAG repair was needed. The delivery closes
`scalarCup_pullback_naturality` and adds the three named holes listed above:
one closed, three added, net -2, a decomposition rather than a dependency-free proof.
