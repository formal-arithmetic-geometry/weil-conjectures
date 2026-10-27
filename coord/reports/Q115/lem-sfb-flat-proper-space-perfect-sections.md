# Q115 stage-1 delivery: lem-sfb-flat-proper-space-perfect-sections

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-flat-proper-space-perfect-sections.json`: statement, split; the original statement and statement dependencies are unchanged. The proof has four steps, 2014 characters in total, and reuses six existing theorem nodes. No new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`: actual msearch.py log; the item retains its imported searches and records the five searches run for this delivery.
- `report.md`: this report.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by flat/proper/perfect/global-sections terminology, and checked `lean/Sheaf/` for the item tag as well. PointPerfect.lean has finite constant-coefficient constructible cohomology over a separably closed field, not structure-module cohomology on a flat proper algebraic space over an arbitrary ring. It does not attach to this statement.

## WANTED

None. All sources used are available in the shared read clone.

## Corrections and scope

There is no statement dispute and no changed hypothesis. The empty imported proof is replaced by the structure-module specialization of Stacks 0CTM(1), followed by the affine-module interpretation explicitly requested in the statement. No proof of a cited node is used as its public statement. In particular, the existing proper-flat-space-derived-base-change node concerns a single flat finitely presented module; it would not cover an arbitrary perfect E, so it is not used here. The more general proper-support tensor theorem does cover E.

The initially considered pseudo-coherence/Tor-amplitude decomposition would repeat existing infrastructure. Reading 0CTM shows that its proof is directly the specialization of 0A1P with the structure sheaf in degree zero, and the DAG already has that theorem. No node is introduced merely to restate this item or one of its clauses.

The current blueprint is `literature/blueprint/latest/`. I read its `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, together with the existing chapter/unit records and this item's inherited blueprint provenance. This supporting lemma serves the 0D3F perfect-sections input in the existing alteration/versality branch; it changes no chapter or unit route. Its imported nearest-blueprint field is null, as also printed by blueprint_refs.py ancestor; I preserve that provenance and the precise inherited from.place rather than invent an ancestor. The item is not the unit's key statement and no unit realization record is changed.

## Mathlib and duplicate searches

I ran blueprint_refs.py search for `perfect direct image`, `affine perfect`, and `proper support`, and searched the entire DAG statements and sources for 0CTM, pseudo-coherence, finite Tor amplitude, affine derived equivalence and the small-etale/Zariski comparison. The projective-Noetherian blueprint theorem is a different, narrower situation. The existing proper-support tensor and affine/etale comparison nodes give all the needed non-elementary tools.

The five actual Mathlib queries are recorded verbatim in the item: two LeanFinder phrasings, Loogle `AlgebraicGeometry.IsProper, AlgebraicGeometry.Flat`, grep `perfect.*(proper|directImage)|proper.*perfect` in AlgebraicGeometry, and a LeanSearch formulation. All services answered. Loogle and grep returned zero hits. Semantic hits were module-category abelianity, Ext, derived t-structure and K-projectivity, ordinary scheme flatness/properness and smooth finite presentation. Reading their returned types rules them out as statements about perfect structure-module derived sections of arbitrary algebraic spaces. They do not give the item by a one-line specialization. No new-node searches need to be inferred or fabricated.

## Not duplicates

No new nodes. The existing lem-sfb-proper-support-tensor-perfect, lem-sfb-scheme-derived-etale-qcoh-comparison, lem-sfb-etale-detects-perfect, lem-pc-perfect-affine-bounded-projective, lem-weil-pbc-ringed-topoi-derived-pushforward-composition and lem-pc-affine-qcoh-derived-equivalence are reused. Off-unit affine comparison and ringed-topos composition statements are declared in split_report.tool_uses as general black-box tools, not replacement routes.

## Review by Q115

I read Stacks spaces-perfect.tex, lemma-flat-proper-perfect-direct-image-general (Tag 0CTM), especially its proof of (1), and lemma-base-change-tensor-perfect (0A1P), including its approximation proof. This is structure-sheaf perfectness on the small etale site, not constructible finite constant coefficients. I read lemma-derived-quasi-coherent-small-etale-site (071Q), lemma-descend-perfect (08HG), and remark-match-total-direct-images (08GH). For the final identification I read perfect.tex lemma-affine-compare-bounded (06Z0) and lemma-perfect-affine (08EB), and sites-cohomology.tex lemma-derived-pushforward-composition (0D6E). There are no new nodes requiring additional sources and no SGA citation.

Step 1 is the elementary specialization, not an assertion of the conclusion: O_X is itself a finitely presented quasi-coherent module, has a one-term bounded complex, is flat over U by the given morphism flatness, and has support X because its annihilator is zero. The hypotheses proper and finite presentation are exactly those already in the item. Setting S=Y=U is permitted in the space theorem. No Noetherianity or scheme chart that represents all of X is assumed.

Step 2 cites the opened statement of lem-sfb-proper-support-tensor-perfect. That statement allows an arbitrary perfect E and a bounded complex of finitely presented quasi-coherent modules flat over Y with proper support, and concludes both perfectness and quasi-coherent cohomology of the direct image. These are precisely what the step takes. Tensoring the K-flat representative term by term with O_X has the explicit unit isomorphism and leaves all differentials unchanged; this does not introduce a separate tensor lemma.

Step 3 uses only the three cited statements. The scheme-derived-etale-qcoh-comparison states an equivalence with quasi-inverse R epsilon_* and sends O_U to the etale structure module; hence its counit identifies epsilon^*L with K. The etale-detects-perfect statement has an if-and-only-if for every derived object on every scheme, so it does apply to L without boundedness or Noetherian assumptions. The affine-bounded-projective statement explicitly supplies a bounded finite-projective A-module complex representing the Zariski perfect L. I checked that L has quasi-coherent cohomology before applying this theorem, using the equivalence and the direct-image theorem's extra quasi-coherence clause.

Step 4 cites the general unbounded ringed-topoi pushforward-composition statement, rather than a scheme-only or constant-coefficient analogue. Both etale sites are small in the stated universes; the one-point site with structure ring A is a third ringed topos. The structural map A to Gamma(X,O_X) is the composite through f, so the comparison is A-linear and computes exactly the scalar-restricted sections in the item. The scheme-derived-etale-qcoh-comparison explicitly identifies derived global sections on both sites. Finally, affine-qcoh-derived-equivalence explicitly gives R Gamma as quasi-inverse to termwise tilde; applying that inverse to L isomorphic to tilde(P) gives P in D(A), not merely degreewise cohomology isomorphisms. Thus there is no missing derived-composition or perfectness-transport claim. Every cited statement is copied verbatim into citations.json.

I tested the argument on the identity Spec A, where it reduces to the input perfect A-complex, on the empty space and the zero ring, where the result is the zero perfect complex, and on zero and shifted perfect complexes. No finite-dimensional cohomology assumption was used, so arbitrary non-Noetherian A is still covered by 0A1P. These checks also distinguish the finite coefficient PointPerfect theorems from this item.

Against delivery-errors B--E: there is no new statement-only node to make hollow, duplicate, elementary, or circular; the original statement is preserved; every non-elementary step cites the exact statement it uses; all hypotheses are checked above; and no tag substitutes for a missing node. Every proof step is below 2000 characters, and the entire assembly is below 3000. The two local tensor/unit and support calculations are written explicitly. No Lean or compiler was used and the shared repository and launcher were not modified.

## Unfinished work

None in this one-level split. Existing unsplit dependencies remain their own stage-1 items. Server dry-run and delivery results are recorded by the delivery tool.
