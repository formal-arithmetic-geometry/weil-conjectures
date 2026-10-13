## What changed

Replaced the original hole in `AlgebraicGeometry.derivedPullbackComposition_tensor_kFlat`
with a categorical proof from the existing direct tensorator normalization and one new
successive-route normalization lemma. The theorem's signature is unchanged.

Added `Sheaf.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization`, containing
`AlgebraicGeometry.derivedPullback_tensor_successive_normalization`. Its hypothesis pins a
chain isomorphism on every total-complex summand; its conclusion calculates only the successive
route after the composite-arrow counits and localization tensor map. It does not compare that
route with the direct derived tensorator.

The original theorem extracts the direct chain isomorphism and its normalization from the
chosen tensorator. It proves invertibility of the final maps using the existing K-flat helpers,
evaluates the selected composition lift's counit factorization, uses naturality along the source
localization tensor map, and cancels the common invertible postcomposition. Added proof imports
of the normalization module, `CanonicalPullbackTensorComparison` with `import all`
(to reuse its existing private proved K-flat helpers and its proof dependencies). No definition or existing public interface changes.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.derivedPullbackComposition_tensor_kFlat`
(node `lem-sc-derived-pullback-composition-tensor-kflat`) by a complete Lean reduction.

Added one hole: `AlgebraicGeometry.derivedPullback_tensor_successive_normalization`
(node `lem-sc-derived-pullback-tensor-successive-normalization`). It is exactly the
ordinary chain tensor/composition calculation and normalization of the successive route.
The new theorem has its source and full proof in words in its docstring and DAG node.

This is a decomposition: one original hole closed, one strictly partial argument left as a
new hole; net hole decrease is zero. The importing theorem contains no `sorry`.

## No longer needed

No existing library node, module, or import is pruned. Three old immediate proof dependencies
are now used through the new normalization node rather than directly by the item's proof:
`lem-pc-kflat-tensor-product`, `lem-pc-module-pullback-adjunction`, and
`lem-weil-pbc-module-pullback-tensor`. They remain needed transitively and their modules
are not pruned. The second reader removed the newly added proof imports
`Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` and
`Sheaf.Algebra.Homology.KFlatPullback`, using the private helpers already in
`CanonicalPullbackTensorComparison` instead; this does not prune GlobalHomAdjunctionIso
from the import closure because MixedHomTensorPullbackIso itself uses it.

The prior sandbox's
`derivedPullbackComposition_tensor_kFlat_coordinate` helper and its new coordinate node were
removed: they merely renamed the entire original obligation. They were never part of the
library and their removal is not counted as library pruning.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt was a restatement and the dry run rejected it. An absence of an
exact existing chain-composition lemma does not prevent a delivery. The repaired reduction
separates successive-route normalization from the direct-route equation already supplied by
`IsCanonicalPullbackTensorComparison`; their combination and cancellation are proved in Lean.

The source statements were read at Stacks Tags [079U](https://stacks.math.columbia.edu/tag/079U)
and [0D5S](https://stacks.math.columbia.edu/tag/0D5S); the chain tensor/composition
calculation is the explicit compatibility of their K-flat constructions.

Validation: `deliver3.py K2 Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat
--no-push` printed `OK (dry run)`: both delivered modules compile and pass preflight except
for the second reading, which the script explicitly leaves to the second reader. The axiom
probes passed, and nothing was pushed. The initial search-record defect was repaired with
the LeanSearch attempt (recorded unavailable because its service returned Internal Server
Error). Temporary global elaboration attributes were removed; the proof compiles without
changing those attributes. No second-reader review has been written by this worker.

The new statement was checked on identity arrows, zero complexes, and empty schemes: the same
adjunction-unit, tensor, and normalization identities apply, with no extra assumption or
cancellation of a base-change map. The chain isomorphism is supplied in a proof and pinned by
its summand equations, rather than used to define data from an arbitrary unproved existence
statement. The unit route is preserved (the unit's realized node lists are empty).

## New nodes

`lem-sc-derived-pullback-tensor-successive-normalization` records the successive route's
normalized chain value (parent proof steps 3 and the successive part of step 4). Its theorem
lives in `Sheaf.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization`. It uses the
ordinary module tensor formula, pinned module adjunctions, K-flat preservation, and shared
counit factorization. No change record or forced adaptation is needed.

## Second reading by K2

1. **Interface check — pass.** Read both delivered modules and diffed the existing
   module against the repository. The existing theorem signature is byte for byte
   identical. There are no added hypotheses, altered definitions, visibility changes,
   target edits, or adaptations of another group's module. Restored the existing
   docstring's original wrapping; all new imports are proof-only.
2. **Proof check — pass.** Both modules compiled locally through lcompile.py before
   cleanup, with no errors or warnings; the cleaned-up main proof compiled again
   successfully. A scratch import with explicit #print axioms for both declarations
   printed exactly propext, Classical.choice, Quot.sound and sorryAx. The original theorem contains a complete
   categorical reduction and no direct sorry. The only new hole is the public named
   `AlgebraicGeometry.derivedPullback_tensor_successive_normalization`, with its node,
   source and natural-language proof. No forbidden declaration mechanism or hollow
   definition is introduced. The final dry run checks every declaration's axioms;
   the remaining sorryAx dependency is reported as a decomposition, not an axiom-free
   completion of the target.
3. **Split statement check — pass.** Read the pinned adjunction unit formula in
   TensorPullbackAdjunction, the naturality and pure-tensor formula in
   ModulePullbackTensor, and the canonical comparison's K-flat coordinate equation.
   The hypothesis on phi fixes its components on every total-complex summand;
   pullback preserves the relevant coproducts by its adjunction, so those equations
   determine the chain map. Naturality moves the g counits into the f tensorator;
   the composition counit factorization and the ordinary unit/tensor formula give
   precisely the stated successive normalization. For identity arrows the mate has
   the composite-unit normalization; zero complexes and empty schemes give the same
   equations without nonzero, finite, bounded or geometric assumptions. This lemma
   does not invoke the direct derived tensorator or perform the invertible
   postcomposition cancellation; those parts are proved in the original module.
   It is one strictly partial normalization obligation, not a renamed whole target.
   Independently searched via leanfinder, loogle and grep with different queries,
   and searched repository sources. Mathlib's Adjunction.isMonoidal_comp requires
   specified compatible monoidal structures absent from this tensorPullback interface;
   PullbackTensorComposition and PicardTensorComposition concern the different
   adjoint-defined pullback interface. Neither replaces the chain/localization
   normalization obligation. Closing it requires that calculation, not a short
   application of an existing lemma. Checked Stacks Tags
   [079U](https://stacks.math.columbia.edu/tag/079U) and
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S): their constructions use the same
   termwise K-flat tensor and composition models.
4. **Route and pruning check — pass after cleanup.** Read the original proof plan
   and the unit record sk-thm-picard-duality; its realized statement and step node
   lists are empty and no unit or chapter route is changed. The proof extracts the
   direct normalization from the existing canonical predicate, evaluates
   leftDerived_fac at the total complex, uses naturality, then cancels proved
   invertible maps. Replaced the unnecessary GlobalHomAdjunctionIso import with
   import all CanonicalPullbackTensorComparison and its existing counit_isIso and
   modelMap_isIso helpers. A scratch compile verified that the explicit KFlatPullback
   import is also redundant: import all CanonicalPullbackTensorComparison already
   supplies it. Removed that import. MixedHomTensorPullbackIso supplies the public
   signature and the new module supplies the successive normalization. Listed all three old dependencies transferred to
   the split node under No longer needed; none is pruned transitively.
5. **DAG check — pass after cleanup.** Compared the old and delivered item node:
   only proof, proof_deps and proof_origin change. Every use in its four proof steps
   matches the reduction, and proof_deps is their union. Updated the helper step to
   name CanonicalPullbackTensorComparison and removed the spurious global-Hom
   dependency. The new node's signature matches its Lean declaration, its proof
   dependencies equal the step-use union, and it has the required source, searches,
   split status, creation, blueprint, chapter, unit and Lean records.

Second reading changed: reused the canonical-comparison K-flat helpers, removed
two unnecessary proof imports and a DAG dependency, restored original docstring wrapping,
and completed the dependency-transfer/pruning report. One original hole is closed,
one new normalization hole remains; net decrease is zero.

Validation after second reading: the first dry run printed OK; the minimal-import
scratch proof also compiled without warnings. Explicit axiom probes printed only
propext, Classical.choice, Quot.sound and the expected sorryAx for both declarations.
