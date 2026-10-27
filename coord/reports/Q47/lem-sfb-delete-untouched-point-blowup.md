# Stage-1 report: lem-sfb-delete-untouched-point-blowup

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-delete-untouched-point-blowup.json: statement item, split into six steps, no Mathlib match.
- No new nodes and no Mathlib leaves. citations.json contains a verbatim statement quote for every step citation. searches.jsonl records the five fresh searches; the item's inherited search records remain intact.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for untouched exceptional curves, contractions, blowdowns and commuting blowups. The blowup library supplies general interfaces but no declaration giving this tower-deletion statement in all its clauses. No sorry declaration is treated as an attachment.

## WANTED

None. The sources needed are available locally.

## Corrections and scope

The item statement is unchanged. Added def-weil-scheme-over-base to stmt_deps because both the hypotheses and conclusions require S-morphisms. The inherited proof was empty; the new proof constructs the shortened tower rather than citing another version of the same assertion. No definition, target, unit or chapter statement was changed. No repair note exists for this item.

The latest blueprint is literature/blueprint/latest, specifically sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. Its current proof (3) records the direct-image route at a higher level and does not state this lower surface lemma. The item's inherited provenance traces the internal minimum-comparison deletion argument through the stable-curve alteration prerequisites. blueprint.from.node is already null throughout this inherited chain, and blueprint_refs.py ancestor reports None. I preserved that metadata and made the implemented place explicit in split_report.blueprint. Whole-blueprint searches for untouched, disjoint, contraction and commuting blowups found no blueprint statement of this result. The inherited same_as=[] remains appropriate.

The general nodes thm-nagata-global-blowup-complement, def-nagata-blowup-flat-base-change-map, thm-nagata-blowup-flat-base-change and lem-weil-pbc-scheme-morphism-gluing are declared as off-unit tools in split_report.tool_uses. They supply generic restriction and gluing interfaces, without replacing the unit's mathematical route. No top-level tool_uses field was added.

## Not duplicates

No new node was created. In particular, lem-sfb-point-blowdown-factorization supplies terminal factorization only; it does not reorder a tower. lem-per-surface-tower-discard-regular-centers concerns neighbourhoods of singular loci and explicitly provides no factorization through the original terminal surface, so it cannot replace the present statement. thm-nagata-blowup-product-ideal supplies a general alternative comparison of two extended ideal blowups; the present proof instead makes its two-open comparison explicit from existing flat restriction and gluing nodes. These facts were reused or distinguished rather than recreated.

## Review by Q47

I read the item against Stacks resolve.tex Tag 0C5J, label lemma-factor-through-contraction, including its quotient-space and structure-sheaf proof, and divisors.tex Tag 0805, label lemma-flat-base-change-blowing-up, including the proof by flat base change of Rees powers. I also read resolve.tex Tags 0AGQ (lemma-blowup) and 0AGR (lemma-blowup-regular), and the product-ideal comparison in divisors.tex Tag 080A (lemma-blowing-up-two-ideals) to check that no missing commutation theorem was being assumed. There are no new-node sources to review. The proof is marked agent-written because neither source states the finite-tower induction.

Step 1 uses exactly the complement isomorphism stated in thm-nagata-global-blowup-complement, to initialize the moving point blowup. The finite induction starts at a, and a=n requires no adjacent swaps; no inductive construction is assumed before being established.

Step 2 uses lem-sfb-regular-point-blowup-geometry for properness and for regular, integral and Noetherian blowup sources and local dimension two above the centre. Its hypotheses hold for each inductively constructed T, and q has local dimension two by the original tower hypothesis. The complement isomorphism transfers this dimension to y. def-weil-proper-morphism states universal closedness, so the image y of the closed point q is closed. The new surface has dimension at most two by specialization chains terminating at closed points and the stated local dimensions; the unaffected closed point z supplies dimension at least two. This avoids an unjustified claim that proper birational maps always preserve dimension without hypotheses. The two distinct closed points y and z need not have disjoint open neighbourhoods; only their complements are used.

Step 3 uses def-nagata-blowup-flat-base-change-map for the actual comparison and thm-nagata-blowup-flat-base-change for its invertibility. Each base-change map is an open inclusion, so its local rings are unchanged and it is flat under def-weil-flat-morphism. The two opens T minus y and T minus z cover T. Over the first the two iterated blowups are Bl_z; over the second they are Bl_y. The comparisons are over these opens, and over their intersection all blowup structure maps are isomorphisms, forcing both comparisons to be the same identity. The statement of lem-weil-pbc-scheme-morphism-gluing gives both existence and uniqueness for compatible morphisms; applying it to the comparisons and their inverses proves a genuine scheme isomorphism, without a separatedness hypothesis on S or Z. Centres are identified with their reduced scheme structures via local isomorphisms, so there is no set-theoretic factorization shortcut.

Step 4 uses def-nagata-strict-transform exactly as scheme-theoretic closure and the complement theorem for each blowup. Because q is disjoint from E_i, the full inverse image of E_i is closed and already contained in the unchanged open. Its closure is itself, which identifies the exceptional fibre as a closed subscheme, not just as a set. This is an elementary direct use of the definition. The new tower has a-1 old steps and n-a replacement steps, hence n-1. Composing the explicitly commuting squares gives the required equality to X_0.

Step 5 uses every clause of lem-sfb-point-blowdown-factorization: its base is regular Noetherian of dimension two, c is the reduced-point blowup constructed in steps 1--4, and its exceptional fibre has singleton image under f by the item's hypothesis. The cited statement supplies existence and uniqueness for any scheme Z. The second application is to the structure map to S, which is constant on that fibre because c is already over S. Its uniqueness gives s_Z f'=s_Y, precisely the S-linearity defined by def-weil-scheme-over-base. Thus no descent from equality merely on underlying points or a dense open is used.

Step 6 uses the complement theorem and the uniqueness part of scheme-morphism gluing. At every swap y=c_i(x_i) has the original centre's image in X_0, and the moved z' has z's image. All centres therefore stay outside V. The local comparisons are the identity over V and uniqueness makes their glued restrictions the same identity. This checks the last clause as equality of morphisms under the canonical identifications, not just equality of point maps.

I checked delivery-errors B--E against the written JSON: no new statement-only node conceals a proof; all notions retain their definition dependencies, with the S-scheme definition added; TeX has single escapes after JSON decoding; each non-elementary interface has a node citation and each cited statement was opened and copied into citations.json. No citation takes content from a dependency's proof. proof_deps is exactly the union of step uses. There is no relabelling of the item, no circular induction and no omitted compatibility. All six proof steps have fewer than 2000 characters. Edge cases checked were n=a=1 (identity empty tower), a=n, a=1, repeated later centres lying on other exceptional curves, arbitrary residue fields, arbitrary nonseparated target and base, V empty, and all original centres outside V. A centre meeting the distinguished exceptional curve is excluded by hypothesis and would invalidate the swap; the proof never extends to that case.

Fresh Mathlib searches used leanfinder with two phrasings, loogle, grep and leansearch, as recorded verbatim by msearch.py. The semantic hits concern normalization, smoothness, flat descent, locally ringed spaces or elliptic-curve points; the type patterns and source grep found no relevant declaration. None supplies the tower or a one-line specialization. I retained the original searches as history and appended the actual fresh results. No unavailable service was recorded as a negative result.

## Unfinished work

None for this one-level stage-1 split. The server review_split check passed with zero new nodes; the unit's absent realization is inherited and is not this item's key-node task. Required delivery preflight and push follow this report.
