# Q25: lem-trf-essential-pro-initial-evaluation

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-essential-pro-initial-evaluation.json`: existing statement, now split into three elementary steps; no exact Mathlib match.
- `citations.json`: verbatim statement quotations for both uses of the existing definition node.
- `searches.jsonl`: actual Q25 wrapper searches, retained unchanged.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The sandbox had no prior item or report, so the live item was the starting copy. Its inherited statement, blueprint chain, citations and search records were preserved; Q25 searches were appended.

## Attachments

None. Searches for the blueprint tag and the notion under `lean/WeilConjectures/` found no declaration proving the complete item for the specified cone and arbitrary witness. `CategoryTheory.initial_iff_essentiallyConstantProDiagram` concerns restriction/extension along an initial functor, rather than this initial-object component and explicit inverse. `CategoryTheory.essentiallyConstantPro_hom_colimit` gives a Hom-colimit bijection, not the asserted inverse formula.

## WANTED

None. The complete source needed for this calculation is present in `literature/stacks-project/categories.tex`.

## Findings and changes

The statement is correct and unchanged. It was an unsplit agent-formulated consequence, not a verbatim Stacks lemma. Stacks Tag 05PU, label `categories-definition-essentially-constant-diagram`, part (2)(a)-(b), gives precisely the natural cone, retraction and common-stage equality spelled out in the item. The new proof derives both inverse identities directly and labels its origin as agent-written. There is no use of a limit existence theorem, a Hom-colimit comparison, smallness, abelian hypotheses, or a special choice of the essential-value cone.

The three-level instructions, chapter `sec-trace-formula`, and unit `sk-i-curve-zero` were read. The current blueprint at `literature/blueprint/latest/` is snapshot `main-20261023-1620`, commit `7284bb09daf97437d544c51882b325f9c52cd345`. Its ancestor `lem-trf-local-term-locality`, proof (1)--(2), supplies the inherited local-term route; the present generic categorical calculation occurs much farther down the inherited chain, at the left-derived object comparison. Nothing at chapter or unit level is changed. Whole-blueprint searches for essentially constant diagrams and initial objects found no separately stated equivalent blueprint node; `blueprint.same_as` remains empty. The existing exact `blueprint.from.place` and `via` chain were retained.

## Mathlib searches and candidate readings

All new Mathlib searches were run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`, and their unmodified summary records appear in `searches.jsonl` and the appended `mathlib_searches`. LeanFinder was tried with two different phrasings, plus LeanSearch, Loogle and two grep patterns. All services answered. The older searches in the live item were retained as inherited records, not claimed as Q25 searches.

I read `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean:427-432`: `CategoryTheory.Limits.IsLimit.isIso_π_app_of_isInitial` needs a limit-cone certificate. That certificate does not occur among the item's hypotheses; deriving it is additional mathematics, and the declaration also does not give the inverse for every witness. I read `EventuallyConstant.lean:38-39,136-145`: the eventual-constancy predicate requires transition isomorphisms, while the comparison results additionally use a limit cone. These do not turn this statement into a one-line specialization. The explicit short calculation is the appropriate split.

## Not duplicates

No new nodes were created. The existing pro-diagram definition was reused. Other existing nodes with Tag 05PU were inspected by their statements: the Hom-colimit lemma computes Hom sets, the cofinality lemma changes the indexing category, the criterion constructs a cone from Hom-colimit bijections, and the K-projective denominator lemma proves initiality in a special denominator category. None states the present general assertion about each specified cone and each witness. No duplicate or clause-restating node is introduced.

## Review by Q25

I read Stacks 05PU(2) in `categories.tex`, including the direction of every arrow, and opened the full statement of `def-pc-essentially-constant-pro-diagram`. The latter says exactly that the cone maps are natural, that $r u_{j_0}=1_X$, and that the map $G(k)\to G(j)$ equals the composite through $G(j_0)$, $r$ and $u_j$. Both citations in `citations.json` quote that statement verbatim. No theorem is inferred merely from the definition's name.

Step 1 uses that definition's naturality and retraction clauses: naturality along $\iota_{j_0}$ gives $G(\iota_{j_0})u_i=u_{j_0}$, and composing with $r$ gives $wu_i=1_X$. Naturality along $\iota_j$ also proves the required component formula. The domains are $X\to G(i)\to G(j_0)\to X$ throughout.

Step 2 uses exactly the common-stage clause of the same statement at $j=i$. The hypotheses provide $k,a,b$ before they are used. Initiality provides $c:i\to k$, and uniqueness of maps from $i$ gives both $bc=1_i$ and $ac=\iota_{j_0}$. Precomposition by $G(c)$ then gives the displayed identity $1_{G(i)}=u_iw$ solely by the functor laws. This is an explicit finite calculation, not an appeal to an unnamed pro-category or limit comparison theorem.

Step 3 uses the two identities already proved, and the definition of an inverse morphism. Since the witness was arbitrary throughout, the proof covers the final universal assertion as well. Every step is elementary and below 500 characters; no step hides an auxiliary comparison or an omitted standard argument. The only proof dependency is a definition, so no off-unit statement tool or route exception is needed.

For small cases, when $J$ has one object and only its identity, the common-stage equality becomes $1=u_i r$ and the retraction is $r u_i=1$, exactly the inverse identities. When $j_0=i$, the formula reduces to $w=r$. For the two-object category $i\to t$, take $G(i)=X=\{0,1\}$, $G(t)=\{*\}$, $u_i=1_X$ and the collapse as the remaining maps: the hypotheses hold using $j_0=i$, while $u_t$ is not an isomorphism. The proof correctly concludes invertibility only at the initial stage. Conversely, in the singleton indexing category, a proper inclusion $\{0\}\to\{0,1\}$ has a retraction but fails the common-stage clause: this verifies that Step 2 actually uses the necessary hypothesis. Empty $J$ is excluded by the existence of $i$. No cancellation, faithfulness, small indexing category, or invertibility of arbitrary transitions has been assumed.

I checked delivery-errors B--E point by point: the existing statement is self-contained and TeX unchanged; the Stacks tag and label agree; every non-elementary input is absent because all steps are the written naturality/uniqueness calculation; citations use statements only; there is no cycle-producing new dependency; no content was moved into a new node; and no hypothesis or conclusion changed. No mathematical correction or statement dispute was necessary.

## Unfinished work

None in the stage-1 split. No Lean was written and no compiler, Lake or global build was run. Required server dry run and direct delivery follow this self-review.
