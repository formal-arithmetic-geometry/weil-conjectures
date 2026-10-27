## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-etale-cover-local-sections.json`: split item, no new nodes, no Mathlib leaves.
- `citations.json`: verbatim statements for every step citation.

## Attachments

None. I searched the upstream project for the blueprint tag and the relevant finite-étale section declarations; no sorry-free project declaration states this item exactly.

## WANTED

None. The cited Stacks Project document `literature/stacks-project/criteria.tex` is present.

## Source and DAG review

The item statement was checked against Stacks Tag 05XQ (`criteria.tex`, `lemma-surjection-space-of-sections`) and retained verbatim, including the absence of flatness, separatedness, and quasi-compactness assumptions on the input map and the allowance of empty schemes. The latest blueprint unit and direct-images proof were read; this input is the Tag 05XQ / relative Hom atlas surjectivity step already named by that route. The inherited blueprint ancestry has `from.node: null`; its existing `from.place` and `via` chain were retained, and whole-blueprint searches for 05XQ, “finite scheme”, “isolated”, and “section” found no duplicate statement.

The proof follows the source’s local-to-global argument. Step 1 reduces the representable algebraic-space source to a scheme by testing representability on the identity of the scheme target, chooses finitely many affine neighbourhoods of the points in the finite fibre, and handles the empty fibre. I checked the finite base change and finite coproduct claims against the cited DAG statements. Step 2 verifies the hypotheses for the existing isolated-point splitting theorem: finite maps are quasi-finite, etale maps are unramified and locally quasi-finite, locally quasi-finite maps compose, and the auxiliary affine scheme is separated. Step 3 applies the existing purely-inseparable isolated-point decomposition, intersects with the original clopen summands, and removes the closed image of the unused finite component; the cited finite-map statement supplies both finiteness and closedness.

Step 4 uses the fibre-product point description and faithful-flatness/surjective-spectrum statements to produce a point above each selected finite piece and the chosen lift in the etale cover. Step 5 applies the covering-base-change theorem to the jointly surjective family consisting of the etale map and the identity, obtaining arbitrary etale base change without assuming the chosen affine neighbourhoods cover the entire source. It then checks that the matching map is finite, etale, has a singleton fibre, and has a finite purely inseparable residue extension; the intermediate-field argument is written out directly from the definition of a purely inseparable extension, since powers landing in the smaller base field also land in the intermediate field. Step 6 applies the existing finite-unramified singleton-fibre theorem and the etale-closed-immersion theorem, spelling out the resulting local isomorphism. Step 7 removes the finitely many closed bad images and assembles inverse maps over the disjoint clopen pieces by the coproduct mapping property. Step 8 takes the coproduct over all base points, obtaining a surjective etale cover and a global section; the empty-base and empty-cover cases are explicit.

I read the full statement of each cited node and included it verbatim in `citations.json`. I removed a maintainer-owned `tool_uses` field before delivery. The item’s existing Mathlib searches were retained, and I ran additional LeanFinder, LeanSearch, Loogle, and Mathlib-grep searches on 2026-10-23/24; they found only generic etale permanence and ring-level facts, not this simultaneous section theorem. No new node was created because each intermediate fact is already an existing node or is a short assembly step from cited statements.

## Review by Q73

I checked every hypothesis in the eight proof steps against the source and against the cited node statements. In particular, I verified that representability is used only to obtain a scheme after base change, that finiteness is preserved under base change and clopen restriction, that the isolated-point theorem is applied to a separated locally finite-type map, and that no flatness or quasi-compactness of the original etale cover is smuggled in. I checked the residue-field tensor product lift rather than assuming a section exists, and I checked the purely inseparable extension by an explicit intermediate-field argument. I also checked the zero-fibre, empty-base, and zero-index coproduct cases. I removed an unnecessary transitivity citation: that node assumes two purely inseparable extensions, whereas this step simply restricts the base of an already purely inseparable extension to an intermediate field. The explicit power argument already proves the needed assertion from its definition. The source’s sentence “we may assume W is a separated scheme” is implemented locally by taking a finite disjoint union of affine neighbourhoods of the selected lifts; this auxiliary affine scheme is separated over the base. No separation hypothesis is added to W.

## What was wrong or incomplete

No statement error was found. The imported item had no completed split and no exact project declaration. The draft had an unnecessary transitivity citation with stronger hypotheses than this intermediate-field argument needs; I removed it and kept the complete elementary power argument. I also replaced the citation for etale base change: the former node covered only surjective families, so step 5 now explicitly adjoins the identity and invokes the existing scheme-covering base-change Mathlib leaf. Step 6 uses etale composition and cancellation for restriction to an open target.

## Could not finish

Nothing remains unfinished in the sandbox. The server check_dag check passed, and the first delivery dry run passed at 83eef7e615c. After the citation correction above, the final required dry run and push are run again. No Lean or Lake compiler was run.
