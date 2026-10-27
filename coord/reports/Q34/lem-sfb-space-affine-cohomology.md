# Stage-1 delivery: lem-sfb-space-affine-cohomology

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-cohomology.json`: item, split into three steps, retaining its statement and statement dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-higher-direct-image-vanishing.json`: new statement-only node, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the three proof citations.
- `searches.jsonl`: genuine msearch command records; all hits read. The item preserves its earlier searches and appends the searches of this attempt.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, algebraic-space terminology, affine cohomology and affine higher direct image found no declaration of this algebraic-space statement. `AlgebraicGeometry.Scheme.Modules.affine_morphism_cohomology_edge` in `AlgebraicGeometry/AffineMorphismCohomologyEdge.lean` is scheme/Zariski-module cohomology; it cannot attach the small-etale algebraic-space statement. The affine higher-direct-image scheme results have the same scope limitation.

## Literature wanted

None. All sources used are present in the repository. No SGA source is used.

## Corrections and scope

No statement dispute and no change of hypotheses or conclusion. The imported node had no proof. I read Stacks `spaces-cohomology.tex`, Tag 0D2U (`lemma-relative-affine-cohomology`), its cited Tag 073H (`lemma-affine-vanishing-higher-direct-images`), and the representable higher-direct-image discussion immediately before `lemma-higher-direct-image`. I read `sites-cohomology.tex`, Tags 0732 and 0733, as well as `lemma-cohomology-modules-abelian-agree` (03FD) and `lemma-limp-acyclic` (0731), to check that writing the vanishing input on underlying additive sheaves is legitimate. Module injectives are acyclic for the underlying abelian direct image, which is why the two interpretations of the higher direct image agree; the new node states only the additive vanishing actually used by this split.

The current blueprint was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-image proof. This item is a remote supporting input deep in the existing Tag 07VP branch of the direct-image stability route, not the statement node of that unit, so no unit realization record is edited. `blueprint_refs.py ancestor` returns `None` for this chain; I preserved its null ancestor and extended the exact existing `via` chain in the new node, rather than inventing a blueprint binding.

## Not duplicates

lem-sfb-space-affine-higher-direct-image-vanishing vs lem-sfb-space-affine-cohomology: the new node says the sheaves R^q f_* F vanish for q>0; the item says the canonical global cohomology edge is an isomorphism for all q>=0. The proof assembles vanishing, Leray and row collapse, rather than replacing its conclusion with a renamed node.

lem-sfb-space-affine-higher-direct-image-vanishing vs lem-pc-affine-morphism-hi: the existing result concerns schemes and their usual quasi-coherent module direct image, including preservation of quasi-coherence. The new input concerns arbitrary algebraic spaces on the small etale site and the derived direct image of the underlying additive sheaf. Passing between the two is the representable base-change and topology-comparison argument of Tag 073H, not a one-line specialization of the scheme result.

Searches of the full DAG by `073H`, `affine-vanishing-higher-direct-images`, higher direct image, affine vanishing and algebraic-space terminology found no existing node stating the new input. `blueprint_refs.py search` was run for `relative-affine-cohomology`, `affine cohomology`, `affine vanishing`, `073H` and `Leray`; the only affine-vanishing blueprint hits are affine schemes. A search of the current blueprint's files for the same affine higher-image and algebraic-space terminology likewise found no equivalent statement. Consequently `same_as` remains empty for both delivered nodes. The new node's source has Tag 073H; no existing node has that source tag.

## Review by Q34

For step 1 I opened the complete statement of the new vanishing node and checked it against Tag 073H, including the additive-sheaf convention just explained. It introduces S, X, Y, f and F itself. The map in the item is affine in exactly the new node's representable/base-change sense. Its coefficient is a quasi-coherent structure-sheaf module, not a constant torsion module. The cited conclusion is precisely R^b f_* (F_ab)=0 for b>0. This is the non-elementary smaller input; its proof remains for a subsequent item. No new clause of the desired global edge isomorphism is hidden in it.

For step 2 I opened `det-thm-groth-ss.json` and read its statement and its current blueprint statement and proof. Its statement explicitly includes the global Leray specialization with a punctual target, not just object cohomology on a site. Thus it applies even when the algebraic space is not a scheme object of its own scheme-valued small etale site. On forgetting the ring, the given small-etale-topos morphism is the morphism used by the abelian Leray sequence. The module pushforward and additive pushforward agree on sections by their definitions; no exactness of module pullback is asserted. The bottom row therefore uses exactly the coefficient f_*F of the item. The generic spectral-sequence tool is declared under split_report.tool_uses.

For step 3 I opened `lem-weil-pbc-first-quadrant-row-collapse.json`. Its statement explicitly identifies the bottom edge itself with the inclusion of the sole graded piece and asserts that it is an isomorphism. The preceding Leray sequence is first-quadrant, has the finite filtration in each total degree, and step 1 kills every positive row. The canonical edge has the required direction from H^q(X,f_*F) to H^q(Y,F); the q=0 identification is sections, and it is not an arbitrarily chosen abstract group isomorphism. Row collapse is also recorded as a generic tool use. These are all the non-elementary facts used in the assembly proof; every citation has a verbatim quotation in citations.json. None of the three steps exceeds 2000 characters.

I checked the small cases f=id (higher direct images vanish and the edge is identity), F=0 (all groups and sheaves zero), empty source (the direct image is zero), and q=0 (sections agree by direct-image definition). Non-affine open immersions are excluded by the hypothesis; the proof does not falsely claim vanishing for them. No quasi-compactness, Noetherianity or separation of X is inserted; affineness already supplies the relative conditions behind the source proof. Arbitrary, not necessarily finite-presentation, quasi-coherent F is retained.

Against delivery-errors B--E: the only new node is self-contained and statement-only, all notions cite existing definitions, TeX is written with single logical backslashes, and the source label and Tag 073H were checked in the Stacks tag table. The Mathlib searches are actual msearch calls, with both semantic phrasings read: returned affine-limit scheme geometry, quasi-coherence definitions and derived-category single-object vanishing do not state this algebraic-space theorem. Loogle and grep returned no hits. The item also has its own semantic cohomology-edge search. No generated or imagined search is recorded. I corrected the tempting use of the object-wise Leray-degeneration node: its statement asks for an object V of the target site, whereas this item needs global sections on a possibly nonschematic space. I used the existing global Leray node and explicit row-collapse node instead. No unresolved argument is concealed in a definition or elementary step, and no repo, launcher, Lean or compiler write was performed.

## Unfinished work

The new vanishing node is intentionally unsplit, as required for a one-level stage-1 split. There is no unfinished part of the item's assembly proof. Required server dry run and push follow this report.
