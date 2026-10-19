# Worker report: lem-coef-presheaf-weak-mono-bounded-enlargement

## Files written

- `dag/nodes/sec-six-functors/lem-coef-presheaf-weak-mono-bounded-enlargement.json`: item, statement unchanged, split into nine steps. Not a Mathlib leaf.
- `dag/nodes/sec-six-functors/lem-coef-presheaf-bounded-intersection-replacement.json`: one new statement-only lemma, unsplit, no Mathlib match after two semantic phrasings, Loogle and source grep. It states replacement for an arbitrary small set of monomorphisms, with intersection, support, size and chain-union controls. It neither mentions weak equivalences nor asserts a bounded enlargement.
- `citations.json`: every citation of every item step, with its cited statement quoted verbatim.
- `report.md`: this report. `searches.jsonl` was written by the required search command; `make_split.py` is a sandbox-only working script.

## Attachments

None. Searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the blueprint id, weak/bounded enlargement terms, fibrant/anodyne terms and intersection-preserving replacement terms. There is no declaration of this item or the new lemma. The upstream master source was also checked as reference, without treating any sorry declaration as a proof. The item has no existing Lean audit declaration to attach.

## Wanted literature

WANTED: Denis-Charles Cisinski, Higher Categories and Homotopical Algebra, https://cisinski.app.uni-regensburg.de/CatLR.pdf, construction 2.4.36, Lemmas 2.4.37-2.4.38, printed pp. 64-66 (PDF pp. 79-81), for both delivered nodes. Read online; not archived in literature/. No download or literature change was made.

WANTED: Cisinski, Les prefaisceaux comme modeles des types d'homotopie (2006), Propositions 1.2.16, 1.2.17, 1.2.35 and Lemme 1.2.32, for the omitted set-theoretic details behind CatLR Lemma 2.4.37. The present new node is an agent formulation of the small-object replacement input; the item's proof is marked agent-written.

No Stacks tag states the arbitrary-set, pre-model interval-homotopy bounded-enlargement lemma or the intersection-preserving replacement input. I did not substitute a general model-category theorem whose hypotheses would presuppose the parent theorem. The generic well-order and recursion leaves already carry their verified Stacks provenance (065T and 03C3 respectively).

## Source error

The item statement is unchanged and is true. The printed proof of Cisinski Lemma 2.4.38 takes an increasing family indexed by a well-ordered set of cardinal alpha, proves each proper stage has size < alpha, and then takes its full union. That establishes at most size alpha, not < alpha. The inference fails even in sets: the increasing proper initial segments of an infinite regular cardinal alpha all have cardinality < alpha, while their union has cardinality alpha. The empty/one-point indexing category does not fix this cardinal issue. I do not claim this example disproves the lemma; it disproves the bound inferred from that construction.

The new replacement input distinguishes a regular preservation rank lambda from a larger regular size bound alpha, with lambda < alpha. Step 7 closes under the homotopy for only lambda stages. Replacement commutes with that union, and regularity of alpha bounds the final union. This keeps the source's replacement/relative-homotopy route and the exact target statement, and changes no unit or chapter route. It also writes out the source's final assertion that the retraction restricts: at endpoint 1 the homotopy puts kr(R(V)) in R(V), while it is already in R(X); preservation of intersections gives R(V cap X).

## New-node mathematical check

The new lemma is a genuine input about a replacement functor, not a clause of the item. It holds for any small set Lambda of presheaf monomorphisms and any fixed auxiliary presheaf B; there is no interval, homotopy, W class, weak monomorphism or desired subobject V in its hypotheses or conclusion.

I read CatLR 2.4.36's simultaneous attachment construction and all clauses of 2.4.37, and the preceding presheaf pushout/intersection calculation 2.4.35. The separate-rank formulation is justified by the following construction (this explanation is in the report, not a proof inside the unsplit node). Choose an infinite regular lambda strictly larger than the total-element sizes of all generator domains and the number of morphisms of A. Form the one-step functor by adjoining, for every generator D -> E and map D -> F, a copy of E along D, then iterate it for lambda stages. Hom(D,-) commutes with lambda-filtered colimits: fewer than lambda elements choose representatives at a common stage, and fewer than lambda naturality/equality conditions hold at a later common stage. Thus every lifting problem occurs before the final stage and is filled at its successor. The same fact and commuting colimits give preservation of lambda-filtered colimits, in particular the lambda-long increasing unions.

At one step, outside the old presheaf, a new element has a generator index, an attaching map and an element in the codomain outside the domain; this description is objectwise and can identify a restriction with an old element. Under an inclusion, two new elements can agree only with the same generator, attaching map and codomain element. A map into an intersection is exactly one whose image lies in both subpresheaves. This proves preservation of monomorphisms and binary intersections at each step; increasing unions preserve the calculation. The empty-generator-domain case is included: its added cells occur in every R(T), including R(empty), so it does not invalidate the intersection formula.

For the simultaneous size bound choose an infinite nu dominating lambda, |B|, |Mor A|, the set of generators and their total domain and codomain sizes, and put mu = 2^nu and alpha = mu^+. If |F| < alpha, then |F| <= mu; there are at most mu^nu = mu attaching maps for each generator, at most mu cells in total, and at most mu elements after a successor or any of the lambda stages. Consequently |R(F)| <= mu and |B x R(F)| <= mu. All cardinals stay in the fixed universe. The poset of subpresheaves of Y of size < alpha is lambda-filtered: a union of fewer than lambda such presheaves has size < alpha, and every element of Y lies in a generated presheaf of size at most |Mor A|. Preservation of its filtered union gives the small-support property. This explains the compatibility of clauses (3)-(5), rather than merely increasing a cardinal that happens to satisfy the printed lemma.

Small cases tested: A empty (the unique presheaf has size zero); Lambda empty (R can be the identity); generators with empty domain (new cells appear in R(empty)); arbitrary B including empty; F empty; X = Y and Y of size < alpha (V = U or V = Y already works). For A terminal, I the two-point discrete interval, and Lambda containing empty -> point, naive fibrant sets are nonempty, every pair of maps into one is directly homotopic, and the construction reduces to adding a point plus closing under a retraction; empty domains and empty U cause no exception. For the nontrivial simplicial examples the argument uses no claim that representable boundaries generate all presheaf monomorphisms.

## Not duplicates

`lem-coef-presheaf-bounded-intersection-replacement` vs `lem-coef-presheaf-weak-mono-bounded-enlargement`: the new lemma constructs replacement for any small set of monomorphisms and has no weak-equivalence or bounded-subobject conclusion; the item constructs V by an explicit relative-homotopy closure using that input.

`lem-coef-presheaf-bounded-intersection-replacement` vs `lem-coef-accessible-small-object-factorization`: accessible small-object factorization asserts a factorization with sufficiently filtered-colimit preservation. It does not assert that its middle object preserves intersections of subpresheaves, nor the simultaneous total-element size, small-support and shorter-chain properties required here.

`lem-coef-presheaf-bounded-intersection-replacement` vs `lem-coef-presheaf-local-finite-presentability`: that node gives generators and filtered presentations of a presheaf category, not any injective replacement or intersection compatibility.

`lem-coef-presheaf-bounded-intersection-replacement` vs `sk-def-exchange`: the blueprint search for "injective replacement" returned only this module-sheaf derived exchange definition. Its statement was read; the phrase is an injective resolution of complexes in the formula for derived exchange, unrelated to a set-valued presheaf replacement preserving intersections.

The whole-DAG searches for 2.4.36, 2.4.37, the new id, replacement and intersection terms found no existing statement giving the new lemma. The target itself contains the source reference but not the replacement statement. Whole imported-blueprint searches for "fibrant replacement", "small object", "cardinal bound", "intersection preserving replacement", and "injective replacement" found no equivalent blueprint node. Both same_as fields are empty; from.node is prop-coef-integral-exceptional-adjoint, and the new via list adds the item before its existing ancestry. The current main-20261015 proof paragraph 2 was read and is precisely the finite-stage derived coefficient-adjunction infrastructure in that ancestry.

## Review by Q58

I checked delivery-errors B through E against both final node statements and all nine steps. The source for the item is the full online statement and proof of CatLR Lemma 2.4.38, including its use of 2.4.37 and 2.4.34. For the new node I read construction 2.4.36, all clauses of 2.4.37, and 2.4.35's intersection hypotheses; I formulated the separate ranks and tested them by the explicit cardinal calculation above. I did not create nodes for the three-face homotopy fill, the elementary anodyne weak-equivalence argument, a restriction of a retraction, or the final two-out-of-three inference. Those arguments appear in the item's steps. The one new node is unsplit and has no proof or proof dependencies or proof sketch in its statement. Every object and all universe, lifting, size and regularity conventions in it are introduced explicitly.

Step 1 cites no node: its maps on the three faces and their endpoints are written out, with e0 square (delta x K) anodyne by the item's actual hypothesis. It proves the equivalence-relation assertion without assuming fibrancy of K. Step 2 also cites no node: surjectivity uses exactly naive fibrancy, injectivity uses exactly delta square a and Step 1, and two-out-of-three is the elementary bijection calculation. Neither step presupposes a model structure.

Step 3 cites the new replacement statement for its actual clauses (1)-(3), with B = I and the generating Lambda furnished by the item. The right lifting extension uses the retract and pushout closure actually stated by lem-coef-lifting-class-closure and the continuous small-ordinal composition actually stated by lem-coef-transfinite-left-lifting. I opened both files; the first does not claim transfinite closure, which is why the latter is separately cited. Thus Lambda-injective objects really are naive fibrant. Naturality supplies the exact commuting square for R(i), and both replacement maps are weak by Step 2.

Step 4 cites lem-coef-presheaf-local-finite-presentability for its stated relative local finite presentability and small colimits, not for properties of R. Its hypotheses are the same small A and input universe. The small Hom sets are exhibited as subsets of component function products. I read the statement of lem-coef-accessible-small-object-factorization: it supplies j in the specified weak saturation and q lifting against Lambda, so it applies to k in this locally presentable category. The two closure leaves extend that lifting to An as in Step 3. I read the full statement of lem-coef-presheaf-naive-fibration-whitehead and checked both hypotheses: q is naive fibrant and its actual codomain R(Y) is naive fibrant; two-out-of-three gives q in W. The arrow-retract equations dk = j and qd = 1 are explicitly checked. I did not cite the parent cylinder-model-recognition theorem, which would be circular.

Step 5 cites no node: it constructs the retraction and a relative homotopy by two fillers using k in An and delta square k in An, checking agreement on the overlap from rk = 1. Both codomains are proved naive fibrant in Step 3. This is the full strong-deformation-retract argument that the printed source packages as 2.4.33-2.4.34.

Step 6 cites replacement clauses (3) and (4) for exactly the small homotopy-image set and the element supports, and lem-weil-pbc-well-ordering-theorem for choosing least support witnesses in the small set of subpresheaves. I opened that leaf; its statement asserts a well-order for every set. Regularity of the chosen alpha is defined in the new node and bounds the displayed union. No local presentability statement is used as a substitute for small support.

Step 7 cites lem-weil-pbc-transfinite-recursion for its stated recursion on a well-ordered set, and replacement clause (5) for the final lambda-chain union. I opened the recursion statement and supplied a total fallback rule as its quantifier over arbitrary prefixes requires. The invariant, the initial stage, the successor, the nonzero limits, the final size bound and the fact xi+1 < lambda are all given. In particular the final bound uses lambda < alpha; it does not repeat the source's alpha-stage gap.

Step 8 cites precisely replacement clause (2), the identity R(V cap X) = R(V) cap R(X), not merely preservation of monomorphisms. The endpoint equation kr = h1 puts the retraction image in that actual intersection. Its inverse homotopy and induced inverse testing functions are written out, so the step takes no characterization theorem from a definition node. Step 9 cites no node: the two composites in the naturality square give the final weak equivalence using already proved two-out-of-three. Uniformity and the universe bounds are explicitly carried from Step 3, not chosen separately for each weak monomorphism.

The sources do not use any SGA route. All cited nonleaf supporting statements are in the item's own unit sk-prop-sf-biduality-general; the two proper-base-change set-theory citations are Mathlib leaves. No off-unit tool declaration or unit realization change is needed. There is no changed statement, no missing hypothesis supplied silently, no new definition with hidden data, and no duplicate source-tag node. The source error corrected above is a proof-bound error, not a dispute about the target statement.

## Unfinished work

The new replacement lemma remains statement-only as required for a one-level stage-1 split. Its future split must prove its simultaneous controls, including the shorter preservation rank; the report gives a precise construction to check against 2.4.36-2.4.37. No work on the target's own proof remains beyond automated dry-run validation. No Lean, compiler, Lake, git command in the shared repository, live-project write, or other agent was used.

## Validation

Validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q58 lem-coef-presheaf-weak-mono-bounded-enlargement --no-push .`. The worker issues READY only after that command prints OK and leaves the sandbox at its accepted result for the independent second reader. This worker does not deliver.

## Second reading by Q58

- Item statement: checked against Cisinski CatLR Lemma 2.4.38 and the definitions of the interval, anodyne class, homotopy classes, and total-element size; all hypotheses and the uniform cardinal conclusion agree, including the empty and one-point cases.
- Step 1: checked against CatLR Lemma 2.4.24 and the displayed (e_0\square(\delta\times K)) three-face pushout; the filler proves direct homotopy symmetry/transitivity without assuming fibrancy of (K); verdict correct.
- Step 2: checked against CatLR Proposition 2.4.25 and Remark 2.4.21; extension, injectivity, and two-out-of-three use exactly the stated anodyne and naive-fibrancy hypotheses; verdict correct.
- Step 3: checked against the replacement node, lifting-class closure, and transfinite-left-lifting statements; the replacement rank and size bound are uniform and the naturality square gives (R(i)\in W_I); verdict correct.
- Step 4: checked against local finite presentability, accessible factorization, lifting closure, transfinite lifting, and the naive-fibration Whitehead node; the retract equations are typed and the codomain fibrancy hypothesis is present; verdict correct.
- Step 5: checked against the explicit two fillers in CatLR Lemma 2.4.33 and Proposition 2.4.34; the endpoint and overlap formulas agree; verdict correct.
- Step 6: checked against replacement clauses (3)--(4) and the well-ordering leaf; the image and support choices remain below the fixed regular α; verdict correct.
- Step 7: checked against transfinite recursion and replacement clause (5); the fallback rule is total, the induction is below λ<α, and the final union has size (<\alpha); verdict correct.
- Step 8: checked against replacement clause (2) and the strong deformation-retract formulas; repaired the restriction argument to state explicitly that monicity of (k) cancels (k), yielding (r(R(V))\subseteq R(S)); verdict correct after repair.
- Step 9: checked against the naturality square and (W_I) two-out-of-three; the conclusion has the required independent α and no model-structure assumption; verdict correct.
- New node `lem-coef-presheaf-bounded-intersection-replacement`: checked against CatLR Construction 2.4.36 and Lemma 2.4.37, with all notions introduced, statement-only form preserved, source and search records present, and small cases (A=\varnothing), Λ=\varnothing), empty generator domains, (B=\varnothing), and (F=\varnothing) tested; verdict correct.

Changes made: added the explicit monomorphism-cancellation sentence in Step 8 so the restriction of (r) is justified from the cited intersection statement; appended this second-reading audit. No statements, citations, source records, or search results were otherwise changed.
