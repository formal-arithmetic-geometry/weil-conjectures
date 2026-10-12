## What changed

Replaced the proof of `AlgebraicGeometry.exists_schemeGlobalSectionsDirectImageIso`
with the generic private `lerayCore` reduction. Its two natural transformations are
right-derived units for the same underived composite. K-injective acyclicity proves
the first is a right-derived functor, and exact scalar restriction proves the
second is one. The universal comparison is invertible, and its factorization
identity is exactly the required unit equation. The underived comparison is
`Iso.refl`, so it acts identically on sections and preserves the scalar action.

Added the module `Sheaf.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic`
with the strictly smaller acyclicity theorem described below, its docstring proof,
and its node. Its public imports provide its signature; its plain imports record
the point construction and successive-direct-image acyclicity used in its proof
plan. The item's import of this helper is plain, since only the proof needs it.
Existing signatures and definition bodies are unchanged.

## Proved and sorry left

Closed one of the item's two original holes:
`AlgebraicGeometry.exists_schemeGlobalSectionsDirectImageIso`
(node `lem-pc-global-hom-adjunction`).

The original hole `AlgebraicGeometry.exists_schemeHomTensorPullbackIso`
(node `lem-pc-global-hom-adjunction`) remains, with its original statement and proof
outline. All already proved declarations remain proved without changed proofs.

Added one named hole:
`AlgebraicGeometry.isIso_directImage_globalSections_unit_on_kInjective`
(node `lem-pc-direct-image-global-sections-kinjective-acyclic`). This only asserts
invertibility of one unit at direct images of K-injectives; it does not restate the
Leray isomorphism, scalar restriction, or its normalization equation.

This is a decomposition: one hole closed, one added, net zero. No definition
contains a new hole or an arbitrary choice of data. The existing Leray choice is
characterized by its underived identity and right-derived unit equation. The
existing tensor choice is characterized by its fixed coordinate predicate.
Compilation and axiom checks permit only `propext`, `Classical.choice`, `Quot.sound`
and `sorryAx` from these and existing named open dependencies.

## No longer needed

Removed the direct imports `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`
and `Sheaf.AlgebraicGeometry.DQCoheratorAdjunction`. The former node
`lem-pc-ringed-spaces-derived-direct-image-composition` is removed from the item's
`proof_deps` and replaced with the new acyclicity node. The latter node
`lem-pc-dq-coherator-adjunction` is still used by the unchanged Hom proof and is
available through `DQCoheratorDerivedGlobalSections`; its node is retained.
No assertion is made that either module is unreachable from all targets.

Removed the undelivered `CanonicalPullbackTensorComparisonOfModel` module, its
import, and its proposed node. They were not old proof dependencies. The original
tensor theorem hole is retained rather than reduced through that unsupported lemma.

## Where the brief, the DAG or earlier work was wrong

The first report omitted the Leray reduction, its additional acyclicity hole and
the removed imports. The acyclicity helper had no node. These omissions are repaired.

The proposed `canonicalPullbackTensorComparison_of_model` has a normalization gap.
`IsDerivedPullbackMonoidalModel` quantifies over a left-derived counit `ε`; the
canonical predicate fixes `SingleComplexBaseChange.counit`. Being a left-derived
counit alone does not make `ε` that fixed counit. For example, transport a model
along the natural automorphism minus the identity: negate its derived counit and
its tensorator hom, leaving the underived model fixed. The model equation still
holds (both sides acquire two minus signs), but the inverse derived tensorator
changes sign. On the identity of a scheme in characteristic different from two,
this cannot give the same fixed canonical tensor comparison. Thus no claim based
on that unnormalized helper is delivered. This issue is reported here without
changing the existing model definition or its users.

## New nodes

`lem-pc-direct-image-global-sections-kinjective-acyclic` supplies the acyclicity part
of the Leray argument. Apply successive-direct-image acyclicity to the map from Y
to its global-sections point, then transport the unit through exact evaluation of
modules on that point. Its Lean signature, docstring proof and node agree.
Identity morphisms reduce to the usual K-injective unit; zero complexes give zero
objects; neither test introduces boundedness or qcqs hypotheses. Searches with
leanfinder, loogle and grep found no matching unbounded theorem. Leansearch was
unavailable. Existing `quasiIso_globalSections_pushforward_injectives` requires
nonnegative termwise injective complexes and does not cover this statement.

Checked the cited [Stacks composition theorem](https://stacks.math.columbia.edu/tag/0D5T),
[derived adjunction](https://stacks.math.columbia.edu/tag/079W), and
[global derived Hom construction](https://stacks.math.columbia.edu/tag/0B6A).
The point-equivalence and unit-transport argument is an inference from these
constructions and the existing successive-direct-image acyclicity node.
No statement or definition change record is needed.

## Second reading by G3

1. Compared the complete diff with the repository version. Existing declaration
   signatures and definition bodies are byte for byte unchanged. Only the Leray
   proof, plain imports and the new private proof helper change in the item. Pass.
2. Compiled the delivered modules in import order with `lcompile.py`. No compiler
   errors or non-sorry warnings. Checked the prohibited declaration forms and
   every remaining hole. Scratch `#print axioms` checks of the changed theorem,
   remaining tensor theorem, Hom theorem, canonical iso definitions and new
   helper show only the permitted axioms and `sorryAx`. Pass with named holes.
3. Reviewed the new acyclicity statement and its zero/identity/unbounded cases,
   docstring argument, source, node and duplicate searches. It is strictly smaller
   than the original Leray existence-and-unit theorem. Removed the unsupported
   monoidal-model comparison rather than delivering it. Pass for the retained node.
4. Reviewed the proof top downward. The generic right-derived uniqueness argument
   is a real reduction and preserves the scalar action and normalization. The
   existing Hom and tensor-Hom arguments are left intact. Removed unused direct
   imports and reported all discarded old proof dependencies. The unit record
   `dag/units/sk-thm-picard-duality.json` has empty realized statement and step
   lists, and this below-unit reduction bypasses none of them. Pass.
5. Updated the item's proof steps, their dependency union and proof origin to
   describe the written Leray reduction. Added all required fields of the new
   node, including the verbatim Lean signature and actual search records. Pass.

Second reading changed: removed the unnormalized tensor-model reduction, restored
its original named hole, added the missing acyclicity node, corrected the helper's
import visibility, updated the item's DAG route, and rewrote the incomplete report.
