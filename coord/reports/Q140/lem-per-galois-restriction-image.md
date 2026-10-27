# Q140 — lem-per-galois-restriction-image

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-galois-restriction-image.json`: statement, now split in six steps; not a Mathlib leaf as a whole. Its statement, statement dependencies, original searches and blueprint provenance are retained.
- `citations.json`: eight verbatim statement quotations, one for each citation in the six steps.
- `report.md`: this report.
- `searches.jsonl`: actual search-command output records. No new DAG nodes or Mathlib leaves were created.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint id, restriction/image terminology and absolute-Galois terminology, and checked the relevant FieldTheory files. No project declaration proves this whole arbitrary-extension restriction-image statement. Mathlib's infinite Galois correspondence is an input, not an attachment.

## WANTED

None. The needed Stacks sources and Mathlib source are present.

## What needed repair

The imported item was statement-only. I supplied the argument rather than creating nodes for its clauses. In particular, the fixed field of the restriction image must be calculated in the specified separable closures; replacing them by algebraic closures would introduce purely inseparable fixed elements in positive characteristic. I made the continuity argument explicit instead of assuming that a finite extension over K stays a finite extension over K inside L. Only the compositum over L needs to be finite over L.

An initial candidate list had two possible new leaves (separable closures are Galois; Krull Galois groups are profinite). Whole-DAG searches found the existing stronger `lem-weil-pbc-separable-closure-exists-galois` and the pair `lem-exc-galois-krull-finite-limit` / `lem-dl-a1-finite-group-limit-profinite`. They are cited and no duplicate was created. The generic closed-subgroup determination also already follows from the existing intersection-of-open-overgroups and open-Galois-correspondence leaves.

The source metadata of existing `lem-exc-etale-open-subgroup-fixed-field-galois` says `pione.tex` for Tag 0BML. That tag actually belongs to `fields.tex`; I read the theorem there and cite that correct source in this item's proof. The existing node is not edited.

## Unfinished work

None in this stage-1 item. No Lean was written and no compiler or Lake command was run.

## Not duplicates

No new-node/existing-node pairs: there are no new nodes. The item itself has no equivalent blueprint statement found by whole-blueprint searches for Galois, fixed field, separable closure, Krull, profinite and restriction. All prospective general inputs were replaced by existing nodes.

## Review by Q140

I read the current chapter and Fourier-perverse unit, the latest blueprint ancestor `lem-per-artin-gabber-affine-curve.proof.md`, and the item's parent dense-henselian-field comparison. This node supplies the Galois-group input in the admitted completion interface; it changes neither the chapter nor the unit's Fourier route. I read `fields.tex` Tag 0BMJ (`lemma-galois-profinite`), Tag 0BU2 (`lemma-infinite-galois-limit`), and the statement and proof of Tag 0BML (`theorem-inifinite-galois-theory`), including the finite-subextension test for a closed subgroup. I also read `topology.tex` Tag 08YD (`lemma-closed-map`) and Tag 08ZY (`lemma-profinite`). There are no new-node sources to review. The proof assembles these standard field and topology facts rather than invoking the desired restriction-image identity itself.

For step 1 I opened `lem-weil-pbc-separable-closure-exists-galois`: its clause (2) gives Galoisness for every supplied separable closure, not merely for a specially chosen one. Taking the intermediate field equal to the base gives precisely K^s/K and L^s/L. Normality is stated as splitting of all minimal polynomials. The root argument and the inverse automorphism therefore show actual preservation of K^s, so restriction is invertible on K^s. Composition is checked on elements. The arbitrary extension L/K is used only for its inclusion in the common overfield.

For step 2 I opened `lem-exc-galois-krull-finite-limit` and `lem-dl-a1-finite-group-limit-profinite`. The former states a topological-group isomorphism to the compatible-family limit and explicitly gives a nonempty directed indexing set of finite Galois intermediate fields. The latter gives compactness, Hausdorffness, total disconnectedness and continuous group operations for exactly that compatible-family limit, with no surjectivity assumption. Thus all its hypotheses are available, with a set of subfields of the given closure as index. No uncited compactness-of-an-arbitrary-limit assertion is used.

For step 3 I opened `lem-sc-finite-generated-integral-subring`. It applies with the coefficient ring L, ambient algebra L^s, and a finite K-basis of F. Every chosen basis element is integral over L because L^s/L is algebraic. Its conclusion is only that L[S] is a finite L-module; I did not cite it for being a field. The proof supplies that remaining elementary argument: injective multiplication on a finite-dimensional domain is surjective, giving an inverse for each nonzero element. Hence L[S] is a finite intermediate field, and its stabilizer is open by the stated Krull neighbourhood basis. Fixing that field fixes S and therefore all of F. The preimage of each basic identity neighbourhood contains this open subgroup, and translation in the already established topological groups proves continuity at every point. This avoids any separability or algebraicity requirement on L/K.

For step 4 I opened `lem-dl-a1-compact-hausdorff-closed-map`. Its final sentence explicitly gives closedness of the entire image for a continuous map from a compact space to a Hausdorff space. Step 2 supplies the two topological hypotheses and step 3 supplies continuity. The image is a subgroup by step 1.

For step 5 I opened `lem-exc-etale-galois-fixed-field-subgroup`. It works for arbitrary Galois extensions, not just finite ones, and says that the fixed field of the subgroup fixing a specified intermediate field is that intermediate field. Taking that intermediate field to be L in L^s/L gives the full group G_L and its fixed field L. For a in K^s, restriction acts by exactly the same element of L^s, so the common invariants are exactly K^s intersect L. This verifies both directions of the fixed-field identity and the inclusion of H into the subgroup fixing E.

For step 6 I opened `lem-exc-etale-open-subgroup-fixed-field-galois` and `lem-wf-profinite-closed-subgroup-intersection-open`. The first really gives the inverse-subgroup identity for every open U, not just existence of its fixed field. The second gives equality with the intersection of all open overgroups for a closed subgroup of a profinite group. H is closed by step 4 and G_K is profinite by step 2. For each U containing H, its fixed field is contained in E by step 5, so every automorphism fixing E belongs to U. Intersecting proves the missing inclusion. Nothing assumes that E/K is finite or that H is normal.

I tested the statement on K=L (full image), on L containing K^s (trivial image), on L=K(t) (E=K, hence surjective image), on finite separable nonnormal L/K (the potentially nonnormal stabilizer of E), and on a purely inseparable extension of an imperfect field (E=K, with full image). These cases expose neither a missing regularity hypothesis nor a spurious normality assertion. The original statement is unchanged and no statement dispute is needed.

I checked B–E of `coord/delivery-errors.md` against the files: no statement-only-node proof payloads or new definitions, no duplicated clauses, no cycle-producing citation of the parent, no replacement of a theorem by a definition, no extra field-extension hypothesis, and no use of a cited proof instead of its statement. All eight citations were copied verbatim into `citations.json`. Every non-elementary fact is a cited existing Mathlib leaf; the linear algebra, root and subgroup inclusions are written out. The six steps total 2726 characters; each is below 2000 characters. The statement and both original notion dependencies are retained, blueprint `from.place` remains specific, `same_as` is searched, and the generic tools are explicitly declared in `split_report.tool_uses`.

Server-only preliminary `review_split` returned PASS with 0 new nodes. The required delivery dry run and push follow this report.
