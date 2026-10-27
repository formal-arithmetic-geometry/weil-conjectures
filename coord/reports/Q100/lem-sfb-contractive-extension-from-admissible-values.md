# Stage-1 delivery: lem-sfb-contractive-extension-from-admissible-values

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-contractive-extension-from-admissible-values.json: split; statement unchanged; explicit linear one-vector construction and contractive estimate, followed by the existing conditional bounded-extension theorem. No exact Mathlib match.
- citations.json: two verbatim statement extracts for the only proof citation, in step 5.
- searches.jsonl: searches recorded by the prescribed msearch.py command. Existing imported searches in the item were retained and six actual Q100 searches appended.

New nodes: 0. New Mathlib leaves: 0. No Lean files or unit records changed.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and admissible-value, contractive, Ingleton and extension notions found no declaration stating the item. The unrelated CompatibleRingTowerRecursion admissible-values docstring concerns ring towers. Searching lean/Sheaf also found no exact statement.

## Wanted literature

WANTED: A. W. Ingleton, The Hahn-Banach theorem for non-Archimedean valued fields, scalar-valued one-vector extension and maximal partial-functional extension argument, for lem-sfb-contractive-extension-from-admissible-values. No such proof is present in literature/LIST.md. This delivery supplies its own elementary calculation and cites the already existing conditional Zorn extension node; proof_origin.by is agent. No SGA source is used.

## Findings and route

The existing statement is correct as written. No STATEMENT-DISPUTED correction is needed. Its scalar-value condition quantifies over every contractive partial functional, which is essential when extending an arbitrary partial extension of f. Merely assuming admissible values for the original f would not justify the maximal-domain argument. The item already has the necessary universal quantifier.

I read the chapter sec-six-functors-basics and unit sk-thm-sf-ctf-stability, and the current main-20261015 direct-images proof, Paragraph (3). The blueprint establishes preservation through proper and open direct images and does not itself contain the scalar-extension proof. The inherited source explicitly records this as an agent auxiliary to that paragraph. Its proof now makes the auxiliary calculation explicit and reuses the existing lemma of the same unit. blueprint_refs.py ancestor returns None for this inherited chain; the precise existing from.place and via list remain intact. Whole-blueprint searches for contractive, Zorn and scalar extension gave no exact blueprint statement to cite or identify as same_as.

The existing node lem-sfb-bounded-extension-zorn already supplies maximal partial graphs and the passage from local bounded extensions to a global one. Its local hypothesis asks for an actual bounded map on U+Kx; this item assumes only an admissible scalar b. Steps 1–3 establish exactly the missing implication. Reusing it avoids both a duplicate Zorn lemma and a new node restating the local calculation. All proof steps have fewer than 2000 characters; after repair the complete proof has 2100 characters.

## Mathlib searches

The prescribed Q100 msearch commands ran LeanFinder with two different plain-language formulations, Loogle for LinearPMap.supSpanSingleton, LeanSearch for the conditional global extension, and two grep queries in Analysis. I read all returned hits and the candidate sources: LinearAlgebra/LinearPMap.lean:535–578, Analysis/Normed/Module/HahnBanach.lean:40–46, Analysis/Normed/Operator/Extend.lean:182–204, Analysis/Convex/Cone/Extension.lean:150–164, and Algebra/Module/Injective.lean:375–380. supSpanSingleton is an algebraic construction without a bound or global conclusion; Hahn–Banach is RCLike; the dense extension theorem assumes density and completeness; Riesz/sublinear extension is real-linear; Baer extension has no norm bound. None specializes in one line to this statement. The second grep returned singleton/subsingleton substring noise, recorded as such rather than claiming no hits. All six services returned successfully; inherited unavailable records were preserved verbatim.

## Not duplicates

No new nodes were created. Existing candidate lem-sfb-bounded-extension-zorn is reused rather than duplicated: it assumes local bounded maps, whereas the item constructs those maps from scalar inequalities. lem-sfb-admissible-scalar-balls derives the scalar-value hypothesis from compact balls and is not needed here, since that hypothesis is given. lem-sfb-proper-ultrametric-scalar-extension additionally assumes compact balls and a nontrivial absolute value and concludes a continuous extension with an unspecified bound; it cannot establish this item's exact contractive conclusion under the item's weaker hypotheses. lem-weil-pbc-zorn-lemma is the existing generic Mathlib Zorn leaf; its work is already encapsulated by the bounded-extension node.

## Review by Q100

I checked delivery-errors B–E with the item, cited statement, and blueprint open. B: there are no new nodes or unstated imported notions; the field definition is already a statement dependency and the norms, vector space, linearity and scalar-value hypothesis are explicit in the item's statement. The existing blueprint place is precise, same_as is empty after search, the original provenance and other fields are preserved. Mathlib search entries correspond to actual recorded commands and checked types.

Step 1 uses precisely the scalar-value assumption in the item for an arbitrary U,g,x; the hypotheses hold because g is a contractive linear extension and x lies outside U. This is direct hypothesis instantiation, not a citation of the compact-ball selection theorem. Step 2 uses only field inversion and the definition of a subspace: equality of two coordinates with different scalars would put x in U. I wrote both additive and scalar identities for G, so well-definedness, linearity and the restriction are explicit. These are elementary algebraic calculations, not an unquoted linear-extension theorem. Step 3 splits off a=0 before any inversion and then uses z=-a^{-1}u. I verified both identities u+ax=a(x-z) and G(u+ax)=a(b-g(z)), including the minus sign. Multiplicativity and the stated norm homogeneity give the exact constant one, without a missing triangle-inequality or continuity theorem. This is a few-line elementary calculation.

For step 5 (step 4 before this repair) I read the complete statement of lem-sfb-bounded-extension-zorn, not its proof. It explicitly quantifies over every U containing W, every bounded extension of f, and every outside x, and returns a global map with the same bound. Steps 1–3 meet those exact quantifiers. With C=1, its positivity condition and initial bound hold. Its ordinary triangle inequalities follow from max(r,s)<=r+s for nonnegative reals. The node explicitly excludes additional completeness/closedness/compactness assumptions; it imposes no finite-dimensionality. The citation quotes reproduce its local-condition sentence and its entire global-existence sentence verbatim. This node has no dependencies back to the item and is in the same unit, so no circularity or off-route tool approval is introduced. No non-elementary fact is used without a cited node.

I tested the zero space V, W=V (no local extensions needed), W=0, U=0, a=0, x=0 (excluded automatically by x outside a subspace), and a nonzero with cancellation u+ax=0 (impossible for x outside U). The construction works with trivial absolute values and over finite fields; neither a small scalar nor a limiting or completeness argument occurs. Infinite-dimensional and nonclosed subspaces are covered by the cited maximality principle, not by an illicit finite iteration. No source error or hidden hypothesis was found, and there is no long proof step concealing an independent lemma.

## Unfinished work

None for this one-level split. The already existing node lem-sfb-bounded-extension-zorn is now split and reviewed in the current DAG; this delivery cites its statement and does not modify it. Required server dry run and direct push follow this self-review.


## Repair of returned delivery 2b855e98962 (2026-10-23)

The single return point was the landing refusal caused by a completed side-DAG item not being promoted to the live DAG, followed by an instruction to rebase, reread changed citations and adjust the split. I continued the retained returned sandbox rather than recreating it. Comparison with the current read clone shows that this item is unsplit there: its statement, statement dependency, source, blueprint ancestry and imported search records agree with the retained version. The retained differences are precisely the four-step proof, its dependency/origin, six actually logged Q100 searches, split status and split report. The delivery tool now builds a fresh commit on the current origin/sheaf-dag, preserving current maintainer metadata. The initial required dry run completed successfully at e1aceeeebfe before these repairs.

I reread both current dependencies in full. def-weil-field still states a commutative field with nonzero one and inverses for all nonzero elements; this justifies the inverse used when a is nonzero. The sole proof citation, lem-sfb-bounded-extension-zorn, is now split, with proof_deps=[lem-weil-pbc-zorn-lemma] and a passing L review dated 2026-10-22, rather than unsplit as the old report said. Its statement still quantifies over all bounded extensions g on all U containing W and all x outside U, requires an actual bounded map G on U+Kx, and concludes an everywhere-defined map with the same constant. I checked its stated hypotheses directly, including C>0, both ordinary triangle inequalities and restriction to f. No new compactness, nontrivial-valuation, completeness or dimensional assumption appears. Its dependency graph does not return to the item.

The repair adjusts the proof, rather than making an unchanged re-push: new elementary step 4 writes out max(r,s)<=r+s by the two possible orders of nonnegative r and s. Final step 5 explicitly matches all quantified U,g,x and the bound C=1 with the maps of steps 1–3, then takes precisely the global-existence clause of the current cited statement. The two verbatim citation extracts remain valid and have been renumbered to step 5. The existing Review by Q100 above covers steps 1–3 and the final citation; this paragraph supplies the review of the new step and of the current dependency state. Zero-dimensional, full-domain, zero-domain, zero-coefficient and trivial-absolute-value cases remain valid. I reread the main-20261015 paragraph (3), which still contains no scalar-extension argument, and retained the honest agent origin and WANTED reference. No new node is created, no old search is rerun or invented, and no external source or Lean compilation is used. A final dry run and direct delivery will validate the repaired files on the current server DAG.
