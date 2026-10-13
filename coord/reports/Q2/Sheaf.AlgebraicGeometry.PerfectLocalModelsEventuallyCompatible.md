## What changed

Replaced the proof hole in `AlgebraicGeometry.perfect_local_models_eventually_compatible`
with a reduction to geometric gluing, the existing perfectness and isomorphism
detection theorems, and a proved generic adjunction construction. The original theorem's signature and public imports are unchanged.

Added `PerfectLocalModelsStageGluing`, stating the geometric descent/gluing part of
Tag 09RF: a stage object and comparison morphism with local perfectness and local
invertibility witnesses. The main proof separately detects global perfectness and
global invertibility using the existing local detection theorems. Added
`PerfectOpenGluingDataOfGlobalModel`, proving that any global perfect model with a
pullback isomorphism yields the required local adjoint data. The latter uses the
top open twice, restricts one global adjoint map twice, and proves the counit
clauses by naturality and the inverse adjunction Hom equivalence. Exact open
restriction preserves perfectness by identifying it with derived pullback. Its private
helper reuses the existing proof of `perfect_exactOpenRestriction` in
`PerfectRestrictionClassesSmall`, whose helper is private and cannot be imported.

## Proved and sorry left

Closed the original hole: `AlgebraicGeometry.perfect_local_models_eventually_compatible`
(node `lem-pc-perfect-local-models-eventually-compatible`). Its proof obtains the
stage, object and comparison morphism, proves global perfectness and invertibility
from their local witnesses, constructs the adjoint data, and returns that stage.

Proved without a new hole: `AlgebraicGeometry.perfect_open_gluing_data_of_global_model`
(node `lem-pc-perfect-open-gluing-data-global-model`) and its private helper
`perfect_exactOpenRestriction`.

Added one hole: `AlgebraicGeometry.perfect_local_models_stage_gluing`
(node `lem-pc-perfect-local-models-stage-gluing`). It contains the geometric
overlap descent, derived object gluing and comparison-morphism gluing with local
witnesses, but no global perfectness, global invertibility, adjunction or
derived-direct-image maps. This is a decomposition (one hole closed, one added),
not a completed geometric descent proof. There are no sorries in the item's module.
No definition chooses data from this unproved existential theorem.

## No longer needed

Removed direct proof imports from the item's module:
`PerfectDescendMorphisms`, `DerivedPullbackPerfect`, `DerivedAdjoint`,
`DerivedDirectImageOpenRestriction`, and `DerivedPullbackOpenRestrictionUniverses`.
The first, second and fifth remain dependencies of the geometric stage-object node;
the second, third and fifth are used by the generic adjunction construction.

The route no longer needs `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
(node `lem-pc-restrict-derived-direct-image-open`) for the adjoint-data construction:
its maps are restrictions of a single global adjoint, rather than transported local
adjoints. The geometric gluing theorem still uses Tag 08FE internally, through
`DerivedOpenGluing`, so no claim is made that this module leaves the target closure.
The original node's `proof_deps` no longer directly use any of:
`def-pc-perfect-open-gluing-data`,
`lem-pc-derived-pullback-open-restriction-universes`,
`lem-pc-derived-pullback-perfect`, `lem-pc-perfect-descend-morphisms`,
`lem-pc-restrict-derived-direct-image-open`,
`lem-pc-ringed-spaces-derived-adjoint`, or
`lem-pc-ringed-spaces-derived-pullback-composition`.
The definition remains a statement dependency, and the other nodes remain below
the geometric or categorical intermediate nodes. No module is claimed pruned
from the target closure.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt only added a private perfectness-preservation helper,
leaving the original hole open. It did not meet the stage-3 minimum reduction.

The original three-step plan is mathematically coherent, but its adjoint-data
construction can be replaced by restrictions of one global adjoint after the
geometric gluing step. The unit's realized record has no fixed internal nodes
here, so this route changes only the internal argument below the unit level.
The geometric statement is source-backed by Tags 09RE, 09RF and 08DG; empty
schemes, empty or equal opens and non-strict preorders require no extra hypotheses.

## New nodes

`lem-pc-perfect-local-models-stage-gluing` is the geometric intermediate theorem
in `lean/Sheaf/AlgebraicGeometry/PerfectLocalModelsStageGluing.lean`, with the full
source proof in its docstring. It is the sole remaining hole.

`lem-pc-perfect-open-gluing-data-global-model` is the proved generic adjunction
construction in `lean/Sheaf/AlgebraicGeometry/PerfectOpenGluingDataOfGlobalModel.lean`.
It has no colimit or finite-presentation assumptions. Both nodes inherit the
item's chapter and unit; the original node's route now records their use.

## Second reading by Q2

1. Compared the delivered item against the repository with `diff -u`. The existing
   declaration signature is byte for byte unchanged; its public imports and all
   definitions are unchanged. The two other modules are new. No interface change
   record is required. The inherited docstring describes the old proposed proof;
   the actual new route is recorded above and in the node's `proof`.
2. Read the proof bodies, including the private exact-restriction helper. The
   helper uses uniqueness of left derived functors and perfect pullback, and the
   public categorical lemma uses adjunction's inverse Hom equivalence and
   naturality. There are no hollow definitions or forbidden declarations. The
   sole explicit hole is `perfect_local_models_stage_gluing`. Compilation and
   axiom checks are recorded below after verification.
3. Read the new geometric statement against Stacks Tags
   [09RF](https://stacks.math.columbia.edu/tag/09RF),
   [09RE](https://stacks.math.columbia.edu/tag/09RE), and
   [08DG](https://stacks.math.columbia.edu/tag/08DG). On the directed tail, descend
   the specified overlap comparison, glue the objects, and glue the compatible
   comparison maps by Hom Mayer--Vietoris. This gives precisely the local
   witnesses asserted. Empty schemes have vacuous neighbourhood conditions;
   empty, disjoint, or equal cover members require no extra assumption;
   directed tails do not require antisymmetry. The generic adjunction statement
   also works for arbitrary g and equal top opens. Independent leanfinder,
   loogle, and grep searches, plus local searches of PerfectDescent*, found no
   reusable theorem of the same statement. The nearby open-union and full
   descent results depend on this item and would create an import cycle.
   This remains a decomposition of the geometric core and categorical
   construction: it does not complete overlap descent or geometric gluing.
4. Traced the reduction and its imports. The new hole excludes adjunction and
   derived-direct-image maps; the categorical construction is actually proved,
   rather than delegated to a renamed hole. The main proof combines it with
   perfectness and isomorphism detection. The geometric part still carries all
   of the descent/gluing work; the net hole change is zero. The unit
   `dag/units/sk-thm-picard-semicon.json` has empty `realized` lists here; no fixed
   realized unit node or step is bypassed. No target-closure module pruning is
   claimed. Completed the direct old-dependency list in `No longer needed`.
5. Checked all three nodes against the Lean signatures and proof route. New
   nodes have source, docstring proof, creation and blueprint provenance,
   chapter/unit, three successful search kinds, and verbatim Lean signatures.
   The original node changes only stage-3-owned proof fields. Removed the
   geometric node's unused statement dependency on PerfectOpenGluingData.

Changes in this reading: replaced the new geometric module's unnecessary public
import of PerfectOpenGluingData by the three public imports its signature uses;
removed extra blank lines; corrected the geometric node's statement dependencies;
completed the old proof-dependency pruning report. No theorem signature, proof
body, or definition changed.

Independent second-reader search queries:
`leanfinder "descending an overlap isomorphism between perfect complexes over a filtered union of rings"`
returned generic local-cohomology/filtered-colimit declarations and bounded derived
representatives, with no match; `loogle "CategoryTheory.Adjunction.homEquiv_symm_apply"`
returned the expected inverse-Hom formula; `grep "leftDerivedUnique|mapDerivedCategoryNatIso"`
found left-derived uniqueness. Local searches also found
`open_restriction_perfect_local_models`, which recovers ambient models from an
already perfect restriction and does not supply the restriction-perfectness
hypothesis required here. The public derived open-pullback homology theorem
asserts a homology comparison, not a functor isomorphism or perfectness preservation.
The usable functor-level open comparisons in PerfectOfOpenPullbacks and
PerfectRestrictionClassesSmall are private; the helper is therefore justified.

Validation: all three delivered modules compiled locally through `lcompile.py`;
the delivery dry run compiled the repaired set, probed every declaration, and
printed `OK (dry run)` with review class CODEX (new nodes/modules and the reported
geometric hole). A separate scratch `#print axioms` check gave exactly
`[propext, Classical.choice, Quot.sound]` for
`AlgebraicGeometry.perfect_open_gluing_data_of_global_model`, and exactly these
three plus `sorryAx` for the main theorem and the geometric intermediate theorem.
The scratch file was removed. There are no further explicit holes, no added
holes in definitions, and no nonstandard axioms.
