## What changed

Replaced the single sorry in
`AlgebraicGeometry.Scheme.picardUniversalRankMatch_fixedRank_retrocompact`
with a complete Lean proof from three strictly smaller geometric statements.
The signature and all existing public imports are unchanged. Added proof-only imports:
`Sheaf.AlgebraicGeometry.PicardFiberRankClopen`,
`Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible`,
`Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion`, and
`Sheaf.Topology.ConstructibleIsRetrocompact`.

The main proof names the fixed fibre-rank locus A, the empty-fibre locus B,
and the two ordinary direct-image rank loci C and D. The residue criterion proves
that the required locus equals A intersect (B union (C intersect D)). It then
combines local constructibility by actual union/intersection lemmas. The proved
private helper `locallyConstructible_isRetrocompact` restricts to affine opens,
uses constructible implies retrocompact on each compact affine, transports compactness
through the open embedding, and writes any compact open as a finite union of affine
basis opens. No quasi-separatedness assumption on S is introduced.

The direct-image rank theorem is used twice, for E and its dual; the existing
`Modules.IsFiniteLocallyFree.dual` theorem supplies the latter's instance.
Every new module is a module file with one public named theorem; its sole proof
hole is exactly a terminal `by sorry`. There are no new definitions or data choices.
Updated the item's proof, proof_deps and proof_origin to describe this assembly.

The whole four-module sandbox compiles through lcompile.py. The delivery dry run
also performs the project's declaration/axiom probes and preflight. This report is
for the independent second reader; nothing has been pushed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.picardUniversalRankMatch_fixedRank_retrocompact`
(node `lem-sc-picard-universal-rank-match-fixed-rank-retrocompact`).
The item's module now contains no sorry. Its topological helper is proved outright.

Added three holes, each in a new module and each strictly part of the argument:

- `AlgebraicGeometry.Scheme.picardFiberRank_clopen`
  (node `lem-sc-picard-fiber-rank-clopen`): clopen constant-fibre-rank and empty-fibre loci.
- `AlgebraicGeometry.Scheme.picardFiberDirectImageRank_locallyConstructible`
  (node `lem-sc-picard-fiber-direct-image-rank-constructible`): constructibility of
  one ordinary fibre-direct-image rank level, without a universal condition.
- `AlgebraicGeometry.Scheme.picardUniversalRankMatch_residue_iff`
  (node `lem-sc-picard-universal-rank-match-residue-criterion`): a pointwise equivalence
  under a prescribed fibre rank; no topological conclusion.

This is a decomposition, not an outright geometric proof: one upper hole closed,
three lower holes added, net minus two before any later dependency pruning.
Existing sorries in imported modules are unchanged. The universal point locus is
not merely renamed: the original proof combines a pointwise criterion with two
independent topological statements and a proved affine-cover compactness argument.

## No longer needed

No existing imports were removed, and no existing module is claimed pruned from
the targets' closure. The second reading removed unnecessary imports only from the
new modules: PicardUniversalRankMatch from both fibre-rank modules (replaced by
TensorPullback and LocallyFree), and Topology.Constructible from PicardFiberRankClopen. The former direct uses of
`lem-pc-rf-perfect-base-change`, `lem-sc-perfect-jump-loci`, and
`lem-sc-perfect-finite-free-residue-model` now belong to the new intermediate nodes;
they remain needed transitively and are not pruning gains. The other old dependencies
removed from the item's direct proof_deps are def-weil-flat-morphism,
def-weil-proper-morphism, and def-sbc-locally-finite-presentation: all three remain
in its signature and in the clopen node's argument. Together with the three lemmas
above, this lists every old proof dependency absent from the new direct proof_deps.

The finite trivializing cover and enumeration of finitely many ranks in the old
step 1 are unnecessary for the clopen argument: the complement of the rank-r locus
on X is itself clopen, so its image under the open and closed map f is clopen.
Its complement in S is exactly the constant-r fibre locus, including empty fibres.
No blueprint UNIT statement or step was bypassed. The unit record
`dag/units/sk-prop-av-cube.json` is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies provide derived complexes and Betti-number jump
loci, but not the ordinary residue-field pushforward-rank interfaces needed to
compose the proof directly. Their signatures require explicit derived-category
localization instances and identifications with ordinary modules. The new
constructibility and residue-criterion nodes isolate precisely this remaining glue
and keep the existing perfect-image and residue-model nodes as dependencies.

The rank argument requires neither connected fibres nor surjectivity, and images
of different ranks must not be treated as disjoint. Empty fibres satisfy universal
matching with rank zero but belong to every fixed E-rank locus. The implementation
retains these cases through the B union term. Checked the new statements on an
empty source, identity morphisms with free modules (including rank zero), a fibre
with components of different E-ranks, and positive prescribed rank on an empty
fibre. None excludes these cases.

Read Stacks Tags 0BDP and 0BDI online. The specialization omits 0BDP's structural
sheaf hypothesis because only the rank portion of its proof is used, not its
representability or descent conclusion. The node/docstring proofs retain the proper
flat finite-presentation hypotheses required by 0B91(2). LeanSearch was unavailable
(HTTP Internal Server Error); this is recorded as unavailable, not as no match.
LeanFinder and local Mathlib grep ran successfully and their queries are in the
sandbox search log. Library and blueprint searches found no exact existing
statement for these three interfaces. The ancestor utility cannot infer ancestry
from this item's module-valued created.item; the new nodes inherit the explicit
existing blueprint ancestor `thm-sc-theorem-of-cube` and its recorded source route.

## New nodes

`lem-sc-picard-fiber-rank-clopen`, in
`lean/Sheaf/AlgebraicGeometry/PicardFiberRankClopen.lean`, isolates the rank-locus
argument of Tag 0BDP's first proof paragraph. The proof explains stalk-rank
invariance under residue-field extension and complements of open/closed images.

`lem-sc-picard-fiber-direct-image-rank-constructible`, in
`lean/Sheaf/AlgebraicGeometry/PicardFiberDirectImageRankConstructible.lean`, translates
Tags 0B91(2) and 0BDI(3) into an ordinary fibre-direct-image rank predicate.
Its statement concerns one arbitrary finite locally free E and is reused for E dual.

`lem-sc-picard-universal-rank-match-residue-criterion`, in
`lean/Sheaf/AlgebraicGeometry/PicardUniversalRankMatchResidueCriterion.lean`, isolates
the field-level equivalence using perfect base change and the minimal residue
models of Tag 0BCD. It explicitly handles empty fibres separately, and imposes
no constructibility or retrocompactness conclusion.

All three nodes have complete sources, natural-language proofs, search records,
chapter/unit/blueprint ancestry and verbatim Lean signatures. No change record is
needed because no existing signature or definition was changed, and no existing
module outside the item was adapted.

## Second reading by K1

1. **Signatures and definitions — pass.** Compared the delivered item with the
repository using diff, and compared its entire theorem signature byte for byte.
The only changes are four plain proof imports, a proved private helper, and the
proof body. The existing docstring is unchanged. No existing definition, theorem
statement, or other module is adapted, so no change record is needed.

2. **Lean proof and trust — pass as a decomposition.** Compiled all four final
modules locally through lcompile.py. There are exactly three terminal named theorem
sorries, all listed above, and no forbidden declarations or attributes or holed
definitions. Scratch-copy #print axioms probes show only propext, Classical.choice,
Quot.sound, and sorryAx for the main theorem and the three open lemmas. The private
locallyConstructible_isRetrocompact helper uses only the three standard axioms.
It has no sorry dependency. Scratch copies were removed before delivery.

3. **New statements — pass.** Read all three statements, docstring proofs and nodes.
Checked the sources [0BDP](https://stacks.math.columbia.edu/tag/0BDP),
[0B91](https://stacks.math.columbia.edu/tag/0B91),
[0BDI](https://stacks.math.columbia.edu/tag/0BDI), and
[0BCD](https://stacks.math.columbia.edu/tag/0BCD). The structural-sheaf hypothesis
of 0BDP is unnecessary for these rank-only facts. For the residue criterion,
base change of cohomology over a field is valid for every scheme over that field:
the perfect residue complexes split into their cohomology and extension of scalars
is flat. The empty-source case gives zero direct images of rank zero after every
base change, while the module on the empty fibre has every rank. For a nonempty
fibre, equality of ranks is detected at a point. Disconnected fibres with unequal
ranks are excluded by the complement of the wrong-rank image, without supposing
images of rank components disjoint. Identity maps with free modules, including
rank zero, satisfy the equivalence. The three statements address distinct parts
(clopen fibre ranks, ordinary direct-image constructibility, and fieldwise
universality); none restates the retrocompactness target. Independent LeanFinder
queries used locally constant stalk ranks, zeroth cohomology in a proper flat
family, and identity testing after scalar extension; grep used
finiteLocallyFree/isLocallyConstant/rank combinations. The logged results include
Module.rankAtStalk_baseChange and Module.isLocallyConstant_rankAtStalk, but no
existing theorem supplies these scheme-sheaf interfaces. Read the upstream
LocallyFreeRank module and the existing perfect-image, jump-loci, and residue-model
modules; they do not close a split statement in a few minutes without substantial
new sheaf/derived comparison work.

4. **Route, imports and pruning — pass after repair.** The top-level proof really
assembles A intersect (B union (C intersect D)), then uses local constructibility
and a proved finite affine-cover compactness argument. No quasi-separatedness
of S is introduced. The helper has no public duplicate; the analogous helper in
PerfectLowestRankBoundOpen is private and applies only to an open subset.
The unit sk-prop-av-cube and its realized fields are untouched, and no unit step
is bypassed. All old proof_deps absent from the new direct list are enumerated
under No longer needed; none represents a module pruned from the target closure.
Replaced the unnecessarily broad PicardUniversalRankMatch imports in the two new
fibre-rank modules by their actual statement dependencies TensorPullback and
LocallyFree, and removed their unused constructibility import from the clopen
module. Added plain imports of PerfectDirectImageBaseChange and PerfectJumpLoci
to the new constructibility module, and PerfectDirectImageBaseChange and
PerfectFiniteFreeResidueModel to the new residue criterion: these are the planned
proof dependencies of the open lemmas and were missing from the first delivery.
Every remaining public import supplies a notion used in its module's statement.

5. **DAG agreement — pass.** Checked every lean.statement against its module and
checked that proof_deps is exactly the union of proof-step uses. Only proof,
proof_deps and proof_origin differ in the existing node. New nodes have sources,
complete natural-language arguments, search records, creation data, blueprint
ancestry, chapter/unit, and Lean records. The existing node describes the actual
assembly and the affine-cover helper. Clarified its first step so the implication
uses openness together with retrocompactness when asserting constructibility.

Second reading changed only the new-module imports described in point 4, this
minor node-proof wording, and this report. It closed no further hole. Final local
accounting remains one original hole closed and three strictly smaller holes
added (a decomposition, net minus two); no module is claimed pruned.
