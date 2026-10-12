## What changed

Kept the existing theorem `AlgebraicGeometry.etaleSet_eventualLocalStageMatching`
with its signature, docstring, visibility and two public imports byte for byte unchanged.
Its proof obtains eventual compatibility, proves preservation of the covering directly
using `Scheme.coverPreserving_overPullback`, `Sieve.functorPushforward_ofArrows`,
`GrothendieckTopology.pullback_stable` and `Sieve.pullback_ofArrows_of_iso`, and
uses the now-proved preservation of image equations. Added only the proof imports
`EtaleSetEventualLocalStageCompatibility` and `EtaleSetLocalStageImageEquations`.

Replaced the first worker's unpublished `EtaleSetEventualLocalStageCover` module:
its arbitrary-stage compatibility statement was false. The new compatibility module
states only eventual compatibility and drops the unneeded covering hypothesis.
The image-equation module works for an arbitrary category and any cone, with no
limit, directedness, affineness or covering assumptions. Its proof is the adjunction-unit
naturality and composition-unit calculation followed by equality of pullback projections.
Each new statement has its own module and complete docstring proof. No definitions,
instances or existing interfaces were changed; no change record is needed.

## Proved and sorry left

Original holes closed by declaration name:
`AlgebraicGeometry.etaleSet_eventualLocalStageMatching` (one of one original holes).
Its proof still uses the new eventual-compatibility theorem below and is a decomposition,
not a sorry-free proof in the project's axiom criterion.

New declaration proved without a local hole:
`AlgebraicGeometry.etaleSet_localStageImageEquations`
(node `lem-weil-pbc-sets-local-stage-image-equations`).

New holes added, and all holes remaining in the delivered Lean:
`AlgebraicGeometry.etaleSet_eventualLocalStageCompatibility`
(node `lem-weil-pbc-sets-eventual-local-stage-matching-compatibility`). Its body
is exactly `:= by sorry`; no partial proof, definition or private helper contains a hole.

Thus one original hole is closed and one strictly narrower hole is added: the delivery
is a decomposition with local net zero, not a claim of ledger progress. The authoritative
closure and whole-library figures remain those of `tools/sorry_ledger.py` and its pinned
baselines. No modules are claimed pruned. The two initial draft holes were removed;
their unpublished cover node is not delivered, and the compatibility node is corrected.

## No longer needed

No existing public or proof import was removed: both original public imports are needed
by the signature. The unpublished draft import/module `EtaleSetEventualLocalStageCover`
and its draft node `lem-weil-pbc-sets-eventual-local-stage-matching-cover` are removed.

The following old proof dependencies are no longer direct dependencies of the parent
node and were removed from its `proof_deps` (some remain in the new compatibility
node's plan or in the proved image-equation calculation):

- `def-weil-pbc-etale-sheaf-of-sets`
- `lem-weil-pbc-affine-etale-site-colimit`
- `lem-weil-pbc-affine-etale-site-topos`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-inverse-image-algebraic-structures`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-sets-affine-etale-inverse-image-comparison`
- `lem-weil-pbc-sets-etale-inverse-image-composition-units`
- `lem-weil-pbc-site-sheafification-sections-local`

The parent now depends directly on eventual compatibility, the image-equation theorem
and étale base-change continuity, exactly as its Lean proof uses them. No existing
library module is proved unreachable by this delivery, so modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (removed unpublished draft): the first worker asserted compatibility
at *every* refinement satisfying the covering and limit-image equations. Separatedness
at that stage does not detect equality only at the limit.

Counterexample: take I = {0 ≤ 1}, D(0) = Spec(k × k), D(1) = Spec(k), with the map
including the first component. All schemes are affine qcqs and the transition is affine;
the limit is D(1). Take i₀ = j = 0, W the identity object, the constant two-element
étale sheaf, and the covering consisting of two copies of the identity W → W.
Let s₀ be zero on both components and s₁ zero on the first component and one on the
second. Both limit images equal t = zero. For j′ = j and r = identity, the cover and
limit-image hypotheses hold, but compatibility fails on the second component. At stage 1
it holds, showing precisely why the replacement must be existential.

The draft nodes also had placeholder mathematical statements, incomplete one-sentence
proof docstrings and proof dependencies pointing back to their parent. The corrected
nodes are self-contained and acyclic. The draft report called the upper theorem proved
without accounting for two new holes; the final report calls this a decomposition and
records the single remaining hole accurately.

The relevant source was read at [Stacks Tag 0A35](https://stacks.math.columbia.edu/tag/0A35):
its section formula and finite matching argument support eventual equality, not equality
at every stage. The local repository has no fetched Stacks TeX file on this machine.
The citation retains the project's canonical literature path. LeanSearch returned
Internal Server Error; that failure is recorded honestly in `searches.jsonl` and the nodes.
Real Loogle, LeanFinder and Mathlib-source grep searches were run with alternate wording.

## New nodes

`lem-weil-pbc-sets-eventual-local-stage-matching-compatibility` states eventual
compatibility of the finite transported affine family, without a covering assumption.
Its proof plan uses affine overlaps, affine-site section continuity, eventual equality
of representatives in a filtered colimit and one common stage for the finitely many pairs.
It is a strict component of the original conclusion, not a renamed copy of the parent.

`lem-weil-pbc-sets-local-stage-image-equations` states preservation of the equations
under every refinement of any cone. It is proved by the existing unit-compatible
composition theorem and by equality of the canonical pullback maps' projections.
The proof has no new named theorem hidden behind a `sorry`.

No change records or forced adaptations.

## Second reading by V3

1. Compared every delivered module with the repository using `diff`; the only existing
   module changed is the item. Its declaration signature is byte for byte identical.
   No definition, target interface, public import, attribute or visibility changed. PASS.
2. Compiled each module locally in import order using only `lcompile.py`. Checked forbidden
   declarations and all literal holes; the sole hole is the named compatibility theorem.
   Added `#print axioms` to scratch copies for all three delivered declarations. Only
   `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` appear. The image-equation
   theorem uses exactly the three allowed axioms and no `sorryAx`; the compatibility
   theorem and parent additionally use `sorryAx` from the remaining compatibility hole. No
   object is defined by choosing arbitrary data from an unproved existence theorem. PASS.
3. Rejected the false universally quantified draft compatibility statement with the
   explicit two-component counterexample above. Checked the replacement: empty finite
   families are vacuous, diagonal pair overlaps are included, empty overlaps have unique
   sheaf sections, and disappearing components are handled by choosing a later stage.
   The sole split-off statement is true, needed and strictly smaller than the parent;
   its docstring and matching node contain the full natural-language argument. Searched
   Mathlib, upstream and lean/Sheaf with alternate wording. Existing finite section-matching
   lemmas concern objects pulled back from the original base, not arbitrary stage objects;
   they do not directly state this claim. PASS AFTER REPAIR.
4. Proved the covering clause directly by existing site lemmas and closed the image-equation
   hole using existing composition-unit coherence. Kept imports minimal and proof-only
   imports private to the proof. Listed every removed old direct proof dependency above.
   Read `dag/units/sk-thm-iff.json`: this item is not a unit realization; the unit's realized
   statement and proof-step nodes are unchanged. No unit or chapter route is bypassed. PASS.
5. Rewrote the parent's proof steps, `proof_deps` and `proof_origin` to match the final proof.
   Rebuilt both new nodes with self-contained statements, exact Lean signatures, sources,
   detailed steps, genuine three-kind search records, creation/blueprint/lean records and
   the parent's chapter and unit. Eliminated dependencies on the parent and checked the
   new proof-dependency graph is acyclic. PASS AFTER REPAIR.

Changed in this second reading: removed the false compatibility-at-every-stage claim;
replaced it by eventual compatibility; removed the redundant cover split-off and proved
covering preservation directly; proved image-equation preservation; fixed incomplete and
circular nodes; corrected hole accounting and pruning; replaced unrestricted `dsimp` by
`dsimp only` so the main reduction does not unfold the inverse-image construction.
