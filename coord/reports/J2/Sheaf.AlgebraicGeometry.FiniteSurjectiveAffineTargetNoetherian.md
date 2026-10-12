## What changed

Replaced the sole sorry in `AlgebraicGeometry.isAffine_of_isFinite_surjective_of_isNoetherian`
with a compiling proof following Stacks 01YQ. The zero and extension hypotheses are proved
from the recorded cohomological delta-functor. The positive finite-sum hypothesis is proved
by applying the degree-one cohomology functor to the first-summand retraction. Generic
support and finite-pushforward coherence supply the integral-support sheaf. Devissage
then proves coherent H¹ vanishing, and the finite-type ideal form of Serre's criterion
concludes affineness. The original public signature and public imports are unchanged.

Added `Sheaf.AlgebraicGeometry.FiniteAffinePushforwardIdealDevissage` for the remaining
ideal-product subobject construction and its cohomology vanishing (original steps 5–6).
This theorem has no surjectivity, integral-support, generic-point or compactness hypothesis;
it is strictly one part of the argument, not the original affineness theorem renamed.
Its docstring supplies the complete construction and proof for the next worker.

Updated the existing node's proof route and added the intermediate theorem's node.
Both sandbox modules compile without warnings. The direct source imports for
quasi-coherent kernels and closed-immersion pushforwards provide the ideal-sheaf bridge,
without importing the much larger HilbertPolynomial module.

## Proved and sorry left

Closed: `AlgebraicGeometry.isAffine_of_isFinite_surjective_of_isNoetherian`.

Added and still sorry:
`AlgebraicGeometry.Scheme.Modules.finite_affine_pushforward_ideal_devissage`
(blueprint: `lem-weil-pbc-finite-affine-pushforward-ideal-devissage`).

This is a decomposition: one upper hole closed and one strictly smaller lower hole added,
net zero new direct holes. The main theorem also uses the existing sorry-bearing
`coherent_property_devissage_integral_subschemes`,
`exists_coherent_pushforward_support_eq_range`, and
`isAffine_of_finiteType_ideal_h1_zero`; those declarations are unchanged.
There is no sorry in the delivered main theorem, no new definition, and no arbitrary
existence witness chosen to define data. The existential witnesses are used only inside
this proposition's proof.

## No longer needed

Removed these direct imports from the item's module:

- `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`
- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.AlgebraicGeometry.AffinePushforwardIdealProduct`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.IdealModuleProductStalk`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`

The edge, projection formula, coherent-submodule, and stalk modules remain needed by
the new intermediate node, so their removed direct imports are not global pruning.
The original nodes `pqf-lem-affine-vanishing` and
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` are not direct proof dependencies
of the target or the new intermediate: its plan uses affine-scheme vanishing with the
module/abelian comparison, and quasi-coherent tensor products and images instead.
Their modules can still be transitively imported through existing dependencies, including
the affine projection-formula module; no claim of target-closure or whole-library pruning.
Preliminaries `lem-weil-pbc-finite-iff-integral-lft` and `pqf-lem-locnoeth-lft` move to
the intermediate node. The unit's statement and realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the target statement. The ideal-sections lemma takes
`IdealSheafData`, whereas the devissage hypothesis takes an arbitrary monic inclusion
of a quasi-coherent module into the structure module. Applying it directly requires
an ideal-data comparison. The new intermediate's proof uses tensor and image
quasi-coherence for that general inclusion instead.

The affine-open vanishing result uses openModuleCohomology, while the target's
property uses moduleCohomology. The intermediate's route uses the already proved
module/abelian-cohomology comparison and affine-scheme vanishing to bridge this.
The generic-support hypothesis `IsGenericPoint` is definitionally the closure equality
in devissage, and this application compiles unchanged.

The local literature .tex is absent on this clone. The source argument was checked
at the official Stacks page https://stacks.math.columbia.edu/tag/01YQ; no source file
or project setting was changed.

## New nodes

`lem-weil-pbc-finite-affine-pushforward-ideal-devissage`, in
`dag/nodes/sec-proper-base-change/`, records original steps 5–6: construct J(f_*F),
prove it coherent with full stalk at any point where J has full stalk, and prove its
H¹ vanishes by the ideal projection formula, affine edge map, and affine vanishing.
Edge cases checked: F = 0, empty schemes, and J equal to the unit ideal; each satisfies
the stated conclusion. For J = 0 at a nonzero local ring the full-stalk hypothesis
fails, as it should. There are no change records or changed existing signatures.

## Second reading by J2

1. Compared both delivered modules against the repository (the helper is new).
   The existing theorem signature is byte-for-byte unchanged; all existing public
   imports are unchanged. Only its proof, proof imports, and proof documentation change.
   No existing definitions or statements are changed, and no change record is needed.
2. Compiled both modules locally in import order with lcompile.py. The only direct
   sorry is the named helper listed above. There are no forbidden declarations and no
   definitions introduced. Scratch #print axioms checks found only propext,
   Classical.choice, Quot.sound and sorryAx, as expected from the listed open lemmas.
3. Read the helper's entire statement, docstring and node against Stacks 01YQ,
   https://stacks.math.columbia.edu/tag/01YQ. Its ideal product construction is valid
   on locally Noetherian X without compactness or surjectivity of f. Zero F, empty
   schemes, the unit ideal and the zero ideal satisfy the stated edge-case behavior.
   Independent leanfinder, loogle and grep searches with different queries, and rg
   over both local Lean roots, found no duplicate or shorter combined result.
   The existing projection-formula and stalk results supply proper parts of the
   argument; the new lemma is strictly smaller than the affineness target. Closing
   it requires several substantial categorical comparisons, beyond a quick repair.
4. Read the proof from the target downward. It implements the cohomological
   retraction, coherent devissage and finite-type ideal criterion directly; it does
   not merely rename the target. Public imports serve signatures; added proof-only
   imports are plain imports. All nine removed old direct proof dependencies are:
   def-weil-finite-integral-morphism,
   lem-weil-pbc-finite-iff-integral-lft, pqf-lem-locnoeth-lft,
   lem-weil-pbc-affine-morphism-cohomology-edge,
   lem-weil-pbc-affine-pushforward-ideal-product,
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth,
   lem-weil-pbc-ideal-module-product-stalk,
   lem-weil-pbc-ideal-times-quasi-coherent-affine-sections, pqf-lem-affine-vanishing.
   Seven move to the helper; the last two are unused by both proof routes.
   The unit sk-thm-p1 and every entry of its realized route remain unchanged;
   neither delivered node replaces a unit-level step. No global pruning is claimed.
5. Compared the node route fields to the actual proof and the helper's docstring
   proof. Existing-node changes are confined to proof, proof_deps and proof_origin.
   The new node has its source, full statement, dependency union, search records,
   creation and blueprint provenance, unit/chapter and matching Lean record.
   Verdict: valid decomposition, one upper hole closed and one smaller hole added.

Changed the target's obsolete eight-step proof docstring to match its actual five-step
route, restored spacing before the module documentation, and explicitly enumerated
all removed old direct proof dependencies in this review. No proof or statement repair
was necessary.
