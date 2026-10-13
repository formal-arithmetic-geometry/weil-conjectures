## What changed

Reduced CategoryTheory.homTensorCurry_natural_pure, with its signature unchanged,
to naturality of the canonical presheaf-to-sheaf tensor map. Its proof now uses
the two curry conditions, the chosen Hom projection map law, and the total-tensor
summand formula. Private helpers prove projection evaluation, internal Hom
pre/postcomposition evaluation, and transport of a total pure tensor.
Added proof-only imports HomComplexProjections and HomTensorSectionNaturality.
The existing public import and all public signatures are unchanged.
Both delivered modules compile together through lcompile.py (2.3 s and 36.9 s).

## Proved and sorry left

Closed the original hole CategoryTheory.homTensorCurry_natural_pure
(lem-sc-hom-tensor-curry-natural-pure) by a complete Lean proof from the imported
statements. Added one lower hole: CategoryTheory.homTensorSectionMap_natural
(lem-sc-hom-tensor-section-natural), in HomTensorSectionNaturality. There are no
sorries in the item's module and none in private helpers or definitions.
This is a decomposition: one original hole closed, one strictly smaller hole
added, net zero holes. The new hole concerns arbitrary module-sheaf morphisms;
it has no complexes, Hom complexes, curry maps, sections or pure tensor summands.
The remaining identity is documented by its full counit/tensorator/unit proof.
Edge cases checked mathematically: zero maps and zero factors require no extra
hypotheses; no assertion that global pure tensors generate a sheaf tensor is used.

## No longer needed

No existing import was removed: HomTensorDegreewise is required by the statement.
The proof does not need lem-pc-sheaf-modules-tensor-closed or its module
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed. It uses the concrete tensor
comparison and sheafification unit instead of monoidal closure. That proof edge
was removed in the node copy; other consumers may still need this module.
No coproduct/internal-Hom extensionality, HomTensorLocalizedExt,
HomTensorNaturalityComponent, HomTensorNaturality, or HomTensorTotal is imported.
All other original proof dependencies are still used. HomComplexProjections and
the new section-naturality module are the only additional proof imports.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt left the main argument unfinished and had not
validated the tensor helpers. Its total_tensor_pure pipeline put the right-hand
tensor expression outside the intended local monoidal-instance scope; explicit
parentheses fix this. Its untyped congrArg also failed to infer the summand map.
The present helpers use explicit morphism types and instance-search size 256.
Rewriting the entire nested curry evaluation caused expensive unfolding; applying
congrArg to the two projection equations makes the actual comparison compile.

The source's tensor comparison naturality lemmas and SheafificationTensor's
private tensorPure_natural are restricted to equal site/coefficient universes,
so they cannot be applied directly to this arbitrary u,v signature. The canonical
section map naturality glue remains isolated, with no altered dependencies or
forced adaptations. Many attempted direct comparison calculations timed out;
no timeout limit was enlarged, no definition was changed, and no private proof
with sorry is delivered. Stacks 03EK and 03CY were read online because this
checkout does not contain literature/stacks-project/sites-modules.tex.

## New nodes

lem-sc-hom-tensor-section-natural: the categorical naturality square for
homTensorSectionMap. Its module is
lean/Sheaf/Algebra/Homology/HomTensorSectionNaturality.lean. Its proof is the
expanded naturality argument from Stacks 03EK and 03CY; it is strictly the tensor
transport part of the original node's second step. Three kinds of Mathlib search
were attempted (LeanSearch unavailable, LeanFinder/Loogle and source grep used).
No change record is needed: no existing statement, definition or public import
changed. The unit's route is unchanged.

## Second reading by K3

1. Compared every delivered existing module and node with the repository using
   diff. Verdict: unchanged existing declaration signature, docstring, visibility,
   definitions and public imports. Removed one extra space before the main
   theorem's proof delimiter and checked its entire signature byte for byte.
   The new module contains just the new public theorem, with no data definitions.
   No statement-change record or forced adaptation is needed.

2. Compiled both delivered modules in import order through lcompile.py: clean,
   2.4 s and 31.7 s, within the unchanged 60 s file limit. Read every private
   helper and the complete main proof. Verdict: the outer and inner projection
   evaluations and total-tensor transport establish exactly the two sides of
   the original equation. The only delivered sorry is the reported named public
   theorem homTensorSectionMap_natural; there are no forbidden declarations or
   hollow definitions. Scratch #print axioms checks for both public theorems
   show precisely propext, Classical.choice, Quot.sound and sorryAx. The latter
   is expected from the new lower hole and still-open imported specifications;
   this delivery is a decomposition, not an axiom-free completion.
   The original worker's local maxHeartbeats 800000 setting is retained; it
   changes the elaboration budget, not the wall-clock file limit.

3. Read the new lower statement, its complete docstring argument and its node.
   Verdict: true, needed for total_tensor_pure and strictly a part of the original
   argument; it has neither complexes nor currying maps. Checked identity maps,
   zero maps and zero factors: unit and inverse-comparison naturality apply
   without any injectivity, invertibility of f/g or generation-by-global-sections
   assumption. Independently searched using LeanFinder for inverse tensor
   comparison and monoidal adjunction-unit naturality, Loogle for mu_natural,
   and source grep for comparison/unit naturality. Mathlib provides ingredients,
   not this combined theorem. Read the existing private tensorPure_natural and
   tensorComparison_naturality proofs: their equal-universe restriction prevents
   direct reuse for this general u,v signature. No short direct replacement was
   found. Verified the source construction and universal property against
   [Stacks 03EK](https://stacks.math.columbia.edu/tag/03EK) and
   [Stacks 03CY](https://stacks.math.columbia.edu/tag/03CY).

4. Read downward from the main equation and checked all imports against actual
   use. Verdict: HomTensorDegreewise is needed publicly by the signature; both
   added imports are proof-only and used. No import is unused. Compared old and
   new proof_deps: lem-pc-sheaf-modules-tensor-closed is the sole removed edge,
   already listed under No longer needed. This is a proof-edge pruning only;
   no module was removed from this delivery's import graph, and no whole-target
   closure pruning is claimed. Read dag/units/sk-thm-picard-duality.json and its
   realized fields: none of these auxiliary nodes realizes a unit step, so the
   unit statement and route are preserved.

5. Compared node records with the Lean and checked proof_deps against the union
   of proof-step uses, all cited dependency nodes, new-node required fields and
   declaration/module names. Verdict: consistent. Only proof, proof_deps and
   proof_origin differ on the existing node. The new node records the exact
   lower statement, source, complete argument, searches and blueprint lineage.

Second-reading changes: repaired whitespace at the existing signature boundary
and added this review with explicit axiom results, the unchanged file time limit,
and the distinction between a removed proof edge and a pruned module. No proof,
statement, definition, import or node route was rewritten. One original hole is
closed, one lower hole added: net zero, with one genuine decomposition delivered.
