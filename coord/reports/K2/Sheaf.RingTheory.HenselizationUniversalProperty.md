## What changed
Replaced the earlier existence/uniqueness interfaces with one new module
Sheaf.RingTheory.HenselizationStageMap, stating the unique map from a single étale
stage. The target now constructs the compatible under-category cocone and descends
it with IsColimit.desc; it proves ideal control with Ideal.map_map and final
uniqueness with IsColimit.hom_ext. Existing signatures and public imports are unchanged.
The four original proof imports are relocated to the stage lemma's planned proof.

## Proved and sorry left
RingTheory.henselization_universal_property: proof completed relative to the single
stage lemma. Its axiom list still contains sorryAx through that open lemma, so this
is not a fully axiom-free universal property.
One sorry remains: RingTheory.existsUnique_henselization_stage_map, node
lem-weil-pbc-henselization-stage-map, in Sheaf.RingTheory.HenselizationStageMap.

## No longer needed
Removed direct proof imports EtaleSectionIdempotentSplitting,
EtaleSectionLiftingOfGabberRoots, HenselianFactorizationCriterion, and
IdempotentsDeterminedModuloRadical from the target; they remain the single-stage
lemma's planned dependencies. Removed the undelivered Exists/Unique modules and
nodes entirely.
Of the old parent proof_deps, def-weil-pbc-category-colimit is retained directly.
The henselian criterion, Gabber lifting, étale base change, diagonal splitting,
and idempotent uniqueness are retained transitively by the new stage node.
The following old proof dependencies are no longer needed by this reduction:
lem-weil-pbc-pair-henselization (its module remains public for the existing interface),
lem-weil-pbc-filtered-colimit-algebras-elementwise (the supplied under-category colimit
suffices), lem-weil-pbc-etale-composition-cancellation (Mathlib étale base-change
instances suffice for the stage argument), and def-weil-pbc-henselian-terminology
(a statement dependency, with the existing HenselianRing interface retained).
The global reach of these nodes elsewhere is not changed by this delivery.

## Where the brief, the DAG or earlier work was wrong
The earlier two interface nodes cited their own parent as a proof dependency,
creating a cycle, and did not update the parent route. The uniqueness interface
also lacked the morphism-of-pairs assumption used by its purported proof. Those
interfaces are removed. The original eight-step plan can be reduced concretely:
steps 2–5 are one single-stage statement, while compatibility, colimit descent,
ideal control, and final uniqueness are now Lean proofs. No departure from the
unit route is needed. The local Stacks source is absent on this machine; the final
paragraph was read at https://stacks.math.columbia.edu/tag/0A02 instead.

## New nodes
lem-weil-pbc-henselization-stage-map: unique extension from one étale algebra trivial
modulo J to a henselian pair along a morphism of pairs. This has no colimit hypothesis
or conclusion, and is strictly the stagewise part of the original argument.
LeanFinder, Loogle and source grep found no existing general stage-map theorem;
LeanSearch was attempted twice and returned HTTP Internal Server Error. No
unavailable search is treated as a mathematical negative result. No change record
is needed because no existing statement or definition changes.

## Second reading by K2
1. Compared the delivered target against the repository with diff. Its declaration
signature is byte for byte unchanged; its docstring and two public imports are
unchanged. There are no changed definitions or additional hypotheses on it.
2. Compiled both delivered modules in import order. The only explicit sorry is the
named single-stage theorem; there are no prohibited declarations or hollow
definitions. Scratch #print axioms checks for both declarations showed only
propext, Classical.choice, Quot.sound and sorryAx (the expected open stage lemma).
3. Read the single-stage statement and its full docstring proof against Stacks
0A02 and the imported criterion, section lifting and idempotent statements. For
J=0 the quotient hypothesis makes f an isomorphism; for f=id the map is φ. If
I=top, henselianness forces the target to be zero. Thus the degenerate cases are
consistent. The stage lemma includes hφ, and uniqueness is only used along a
morphism of pairs. Searches did not find a replacement in Mathlib or this library.
The theorem omits all colimit reasoning and does not restate the target.
4. Checked the top-down reduction: compatibility and final uniqueness genuinely
use stage uniqueness, while the supplied colimit directly gives the map. Imports
in the target are its existing public interface plus the one private proof import.
The new module imports the ingredients of its unfinished documented stage proof.
The complete old proof_deps accounting is above. sk-thm-p1.realized is unchanged;
this internal reduction preserves its route and all its realized steps.
5. Updated the parent proof and proof_deps to the stage lemma and categorical
colimit, and wrote the new node's full fields and exact Lean signature. Its proof
steps cite the existing stage ingredients, never the parent, so no cycle is added.
Changed: removed two circular coarse interfaces; introduced the single-stage
lemma; wrote the actual colimit reduction and ideal proof; corrected the nodes,
imports, pruning report and search provenance. The remaining stage lemma is not
closed: formal tensor-product and diagonal arguments are the next proof task.
