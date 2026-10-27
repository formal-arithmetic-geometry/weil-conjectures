## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-localization-tensorator-signed-shifts.json`: statement, now split in four steps; no Mathlib match.
- No new nodes and no new Mathlib leaves. All non-elementary inputs already have nodes.
- `citations.json`: twelve verbatim statement quotations, one for every step/node citation.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and localization/tensorator/shift notions found no project declaration proving this square. Nearby derived-pullback tensor modules concern different comparisons, and contain postponed arguments. No source declaration was treated as proved merely because it exists.

## WANTED

None. The relevant Stacks sources are available locally.

## Audit of the imported item

The statement is retained verbatim. Its previously empty proof is replaced with an explicit K-flat resolution and naturality argument. The localization shift comparison is a notion used explicitly in the statement, so `def-weil-abstract-derived-category` is added to `stmt_deps`. Every other pre-existing statement dependency is retained because it introduces an explicitly named object or comparison. `proof_deps` is exactly the union of the four step citation lists.

The source is an agent-formulated refinement: Stacks `cohomology.tex`, Tag 0FPB, `lemma-symmetric-monoidal-derived`, omits the proof and does not explicitly state this square. I therefore marked the assembly proof agent-written, rather than attributing the new compatibility proof to that tag. I read `sites-cohomology.tex`, Tags 06YS (`lemma-K-flat-resolution`), 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`) and 06YU (`definition-derived-tor`, including its preceding construction), and the parallel ringed-space construction in `cohomology.tex`. I also read `more-algebra.tex`, Tag 0FNH, `item-shift-tensor`, and the preceding definitions of shift, shifted maps, and total differential.

The sign convention deserves attention: Stacks writes its displayed comparison using the original first degree, whereas this item explicitly chooses the shifted first degree. They differ by the constant sign $(-1)^{ab}$. The item's convention is valid and is realized by extracting the second shift first and then the first, using the existing total-shift node. I checked its two differential signs explicitly in step 1; I did not silently substitute the other convention.

The latest blueprint unit `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md` were read under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. The inherited long provenance chain is a tensor/coherent-cup tool below the direct-image argument, not a new route for the geometric theorem. `tools/blueprint_refs.py ancestor` reports `None` for this existing chain. I retained its existing `blueprint.from` and the specific support place, and searched the whole blueprint for tensorator, signed, and shift comparison; no blueprint node states this arbitrary-complex compatibility. `same_as` remains empty.

## Mathlib searches

All six fresh searches were run with the required `msearch.py` command and recorded in `searches.jsonl`: LeanFinder with both the lax-localization/signed-shift phrasing and the K-flat-counit/naturality phrasing; Loogle with `CategoryTheory.Functor.LaxMonoidal, CategoryTheory.Functor.CommShift`; LeanSearch with the derived-localization two-factor shift description; and two source greps. All services returned answers. Results were read. The general `Functor.commShiftOfLocalization` comparisons descend a functor that already commutes with shifts; they do not state the arbitrary-complex lax tensorator square. `DerivedCategory.instCommShiftCochainComplexIntQ` states only that Q commutes with shifts. I read the pertinent definitions in Mathlib `CategoryTheory/Shift/Localization.lean` and `Algebra/Homology/DerivedCategory/Basic.lean` (lines 155–162). Tor functoriality results concern ordinary derived functors of degree-zero tensor, not this unbounded bifunctor compatibility. No exact match or one-line specialization was found. The inherited search records were preserved, and the fresh logged queries were appended without inventing queries or search results.

## Not duplicates

No new nodes, so there are no new/existing node pairs. Existing total-shift, shift-descent, K-flat-resolution, native tensor and fixed-tensor-triangulated nodes are cited directly. In particular I did not create separate nodes for K-flat shift stability, functoriality, cancellation, or the resolving-pair instance of the item.

## Review by Q32

I checked each proof step against the statements of all the nodes it cites, not their proofs. Step 1 uses `lem-weil-pbc-total-tensor-integer-shifts` for the unsigned first-factor shift, the signed second-factor shift and naturality, and `def-pc-tensor-complex-sheaves` for the total differential. Applying the second-factor shift to K[a] gives exactly the shifted first degree i in the item. The two parity calculations written there verify that s is a chain map; this is a direct calculation from the cited formulas, so the step is elementary.

Step 2 uses the actual existence statement of `lem-pc-kflat-resolution`: flat-term K-flat complexes mapping by quasi-isomorphisms to arbitrary complexes. It uses only the explicit sentence “Shifts preserve K-flatness and flat terms” from `lem-weil-pbc-kflat-fixed-tensor-triangulated`. Its small-site hypothesis is satisfied by the set of open subsets of the scheme X, in the chosen module universe. The localization and shift assertions of `def-weil-abstract-derived-category` make the shifted resolution maps invertible. Tensoring two isomorphisms has the tensor of their inverses as inverse by bifunctoriality; this does not require either original complex to be flat.

Step 3 uses `lem-sf-ringed-derived-native-tensor` for the inverse localization tensorator agreeing with the simultaneous K-flat comparison, and `lem-weil-pbc-derived-tensor-shift-descent` for exactly the representative normalization conjugated by that comparison and the localization shifts. Both P and R and their shifts are flat-term K-flat by step 2, so that normalization applies. The total-shift node fixes the composition order from step 1. Substitution of c = mu inverse is a cancellation of isomorphisms on these resolving pairs; it is not an assumption that mu is invertible on arbitrary complexes. The comparison inverse in the native node agrees with the fixed K-flat construction already specified in the statement, so no independent tensor structure is substituted.

Step 4 uses the native node's canonical lax tensorator, hence its naturality, the total-shift node's chain-map naturality, the descent node's natural isomorphisms on derived objects, and the localization shift comparison from the derived-category definition. The two written identities A v = w A' and B v = w B' state the whole naturality reduction. The equality from step 3 is postcomposed with w; only v is then cancelled, and its inverse was exhibited in step 2. In particular the proof does not claim that Tot(p tensor q) is a quasi-isomorphism: with arbitrary nonflat K and L that claim would be invalid. This last step is elementary diagram pasting with all the component naturality assertions cited.

For delivery-errors B1–B10 there are no new nodes, phantom definitions, alleged Mathlib leaves, or attachment claims. C1–C8 are addressed by the twelve verbatim quotations and the statement-by-statement audit above; the off-unit generic tools are expressly declared in `split_report.tool_uses`. D1–D5 are addressed by writing the sign computation and the two naturality identities in the item itself, with no relabelled clause nodes. For E1–E7 I checked the small-site hypothesis, source and target of v and w, all normalization hypotheses, and the constant sign distinguishing the two extraction conventions. There is no statement dispute and no source assertion was silently strengthened.

I tested a=b=0, one shift zero, mixed negative shifts, and a=b=1 with K=L=O_X[0]. In the last test the first shifted degree is -1 and the comparison is minus the unsigned identification, as stipulated; both sides have that same sign. Zero complexes and the empty scheme reduce to zero morphisms, and characteristic two simply removes the signs. K and L may be unbounded and nonflat: resolution existence is unbounded and the cancellation uses only their derived resolution images. Every proof step is shorter than 2000 characters; none hides an additional lemma. No Lean was written and no compiler was run.

## Unfinished work

None for the one-level stage-1 split. Proofs of cited existing nodes remain their own items; this delivery does not claim the whole dependency closure is Lean-closed.
