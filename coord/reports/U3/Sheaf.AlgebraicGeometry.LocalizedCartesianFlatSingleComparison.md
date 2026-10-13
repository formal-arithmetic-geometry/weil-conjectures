## What changed

Repair of the failed landing: removed the private duplicate
`AlgebraicGeometry.tensorPullback_iso_equivalence` and the now-unnecessary private
`isoTensorPullback_additive` helper and its local instance attribute. Added the
proof-only import `Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology` and use its
existing public `AlgebraicGeometry.SingleComplexBaseChange.tensorPullbackIsEquivalence`
instance. This instance requires only an isomorphism, with no global derived-category
hypothesis. The import-direction check confirms that it introduces no cycle.
The geometric intermediate and public theorem signatures remain unchanged.


Replaced the sorry in
`AlgebraicGeometry.localized_cartesian_flat_single_comparison` by a proof of its
unchanged signature. Added the standard-localization, canonical-pullback helper
module `Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange` and its node
`lem-pc-standard-flat-single-base-change`. All six additional imports in the
target module are proof-only. The helper's three public imports supply its
statement's derived functors, schemes, and relative-flatness predicate.

The target proves the localization comparison using a common K-injective
resolution, computes derived pullback along a scheme isomorphism by left-derived
uniqueness, and transports the canonical-square comparison through pullback
composition, adjunction, and direct-image composition. No public definition or
existing theorem signature changes. The independent reading corrected the
natural-language flatness explanation, not the proof term or statement.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.localized_cartesian_flat_single_comparison`
(node `lem-pc-localized-cartesian-flat-single-comparison`): its body contains no
sorry, but its axioms still include sorryAx from open dependencies.

Hole added: `AlgebraicGeometry.standard_flat_single_baseChange`
(node `lem-pc-standard-flat-single-base-change`), the single named sorry in this
delivery. It is a strictly smaller geometric comparison in standard localizations
on the canonical pullback. The proof of the target supplies the additional
cartesian-source and independent-localization transports in full.

This is a decomposition: one upper hole closed, one lower hole added; net holes
closed minus added is zero. Neither declaration is claimed axiom-free.

## No longer needed

The duplicated private `tensorPullback_iso_equivalence` proof and the private
`isoTensorPullback_additive` helper are removed. Their result is supplied by the
existing public instance in `IsoPullbackStalkCohomology`. Neither duplicate module
`CartesianTensorDataComparison` nor `LocalizedResidueHomologySheafRestriction` is
imported: their matching helpers are private, and the former would close a cycle.


Old target proof dependencies removed:
- `def-pc-scheme-derived-tensor-structure`
- `lem-pc-relatively-flat-tensor-base-change-iso`

Their geometric role is now confined to the specialized open helper; the target
proof itself uses neither declaration. No import from the repository version of
the target was removed. No whole-library module-pruning count is claimed: the
maintainer's ledger determines reachability. Relative to the earlier attempted
helper proof, the cyclic proof-only imports through `SingleComplexQcqsInduction`
and its cartesian downstream chain were removed. The helper's DAG dependencies
are a future proof plan, not a claim that its sorry body imports or applies them.
The attempted removal of `Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived`
failed compilation at `Functor.isLeftDerivedFunctor_of_inverts`, so it was restored.

## Where the brief, the DAG or earlier work was wrong

The first delivery re-proved tensor pullback equivalence despite an existing
public instance in `IsoPullbackStalkCohomology`; the landing's duplicate-statement
check correctly refused it. The repair reuses that instance and records its node
as a proof dependency. The old second reading predates this repair and has been
removed for a fresh independent reading.


The earlier helper imported a comparison chain returning through this target,
creating an import cycle. It is left as a documented geometric intermediate,
with no cyclic proof imports. Its future implementation must choose a cycle-free
route; the existing qcqs-induction plan cannot simply be imported unchanged.

The earlier report called the new helper node existing, claimed pruning without
reachability evidence, and called the new helper a forced adaptation. The helper
module and node do not exist in this checkout's repository baseline: they are new,
and there are no forced adaptations. The inaccurate proof-import change record was replaced by a precise record of
the added elaboration commands, which the static checker requires even though
no statement, definition, or public import changes.

Relative flatness means the stalk complex is K-flat over the base stalk, not over
the source structure-sheaf stalk. The fibre-product stalk is flat over the tensor
product of the two stalk rings; no flatness of the arbitrary base-change morphism
is required. The helper docstring now gives the precise tensor-unit specialization
of Stacks Tag 0A1D and includes zero-module and empty-scheme cases.

## New nodes

`lem-pc-standard-flat-single-base-change`, in
`dag/nodes/sec-picard-framework/lem-pc-standard-flat-single-base-change.json`,
states the canonical-pullback comparison with standard localizations. Its Lean
signature matches the new module verbatim. It records the source, complete proof
plan, searches, creation metadata, blueprint ancestry, chapter and unit.
The checker-required command-change record is
`coord/changes/localized-cartesian-flat-single-comparison-proof-settings.md`.


## Second reading by U3

1. **Public interface: pass.** Diffed the delivered target module against the
   repository version. The existing public theorem signature is byte-for-byte
   identical, including its universe-polymorphic derived-category instances,
   relative flatness, qcqs assumptions, cartesian square and conclusion. No existing
   public definition or public import changed. The extra commands and private
   helpers are covered by the command-change record. The geometric helper and
   its node are new; there are no forced adaptations.
2. **Proof and axioms: pass as a decomposition.** Compiled both modules in import
   order with lcompile.py, without errors or warnings. Scanned both full files:
   the only sorry is the named standard_flat_single_baseChange theorem; no axiom,
   unsafe, opaque, extern, implemented_by or hollow definition occurs. Compiled
   a scratch copy with #print axioms for the public theorem, the open helper and
   all four private transport helpers. standardQIso, standardDirectImageSingle
   and iso_pullback_computes use only propext, Classical.choice and Quot.sound.
   standardCartesianFlatSingle and both public theorems additionally use sorryAx.
   The scratch copy was removed from the delivered modules. Choices of derived
   functors and adjunctions use their universal properties, not arbitrary data
   from an unproved mere-existence theorem.
3. **Split statement: pass.** Read Stacks Tag 0A1D directly at
   https://stacks.math.columbia.edu/tag/0A1D. The tensor-unit specialization in
   the helper docstring has the correct hypotheses and ordinary pullback of the
   relatively flat single complex. Checked zero modules, empty schemes, identity
   base change, and the absence of an unjustified flatness hypothesis on g or M
   over O_Y. The helper isolates the canonical-square geometric comparison; the
   parent separately proves cartesian-source and independent-localization
   transport, so this is a smaller statement rather than a renamed target.
   Independent Lean Finder and Loogle searches, plus rg of lean/Sheaf and
   lean/WeilConjectures, found no exact shorter replacement. The existing
   flat-module comparison requires IsSeparated; the tensor comparison requires
   additional monoidal machinery and its module's import route returns through
   this item. The open helper cannot be closed in a few minutes from these.
4. **Route and pruning: pass.** Read the proof from the public theorem downward:
   exact derived overEquiv maps the standard cartesian comparison, the common
   K-injective resolution handles arbitrary localizations, and the canonical
   pullback is transported by derived composition, adjunction and exact ordinary
   pullback along sq.isoPullback. The proof reuses the existing public
   tensorPullbackIsEquivalence instance rather than duplicating it. Public imports
   supply statement notions; each added plain import supplies a proof ingredient.
   Transitive proof imports do not export their declarations, so graph reachability
   alone does not justify removing the direct imports (the earlier PointwiseLeftDerived
   removal already failed compilation). The two removed old proof dependencies
   are fully listed under No longer needed. No baseline import or module is
   claimed pruned. Read sk-thm-picard-coherence.json: its realized statement and
   step lists are empty in this baseline, and this delivery changes neither the
   unit nor its noetherian-approximation route.
5. **Nodes: pass with metadata correction.** Both Lean records match their
   declarations verbatim; proof_deps equal the union of the proof steps' uses,
   and all referenced dependency nodes exist. The parent node follows the actual
   proof; the open helper's steps are explicitly a future source-based plan.
   Verified the new node's source, creation, chapter, unit, blueprint ancestry,
   status and searches. Corrected its old grep entry saying the prospective
   ingredients were already used in the proof: the body remains sorry, and the
   current qcqs-induction import path is circular through this parent. Added the
   independent searches to this new node. No Lean proof or signature needed repair.

Second reading changed only new-node search metadata and this review report.
The result remains one upper hole closed, one strictly smaller hole added,
net zero; no axiom-free proof or reachability pruning is claimed.
