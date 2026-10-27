# Stage-1 report: lem-sfb-relative-pseudocoherence-composition

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-pseudocoherence-composition.json: item, statement unchanged, split into five steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-pseudocoherence-flat-base-change.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-closed-pushforward-pseudocoherence.json: statement, unsplit; no Mathlib match.
- citations.json: every step/node pair with a verbatim statement quotation.
- searches.jsonl: real search-command output records, retained as generated.

## Attachments

None. Searched lean/WeilConjectures for the item's exact blueprint tag and relative/pseudo-coherence keywords. Existing absolute pseudo-coherence modules do not state this relative-composition equivalence. None of the two new supporting statements has a matching project declaration. No Lean files were written and no compiler or build was run.

## Wanted literature

None. All mathematical sources used are present in literature/stacks-project/.

## Corrections and route

The item is faithful to Stacks Tag 09UT, lemma-composition-relative-pseudo-coherent (more-morphisms.tex, lines 17235ff), including both directions, all integers m, locally finite type assumptions, and the ambient category of arbitrary structure-module complexes. The statement needed no correction. In the source proof the occurrence of j_* O_{A^n_Y} is an index typo: j has source A^r_Y, where r is the number of coordinates for X over Y. The delivery calls the source T=A^r_V, the target Q=A^{n+r}_W, and keeps m for the approximation degree. This corrects only proof notation, not any statement or route.

Read the chapter/unit records, SETUP's three levels and the latest blueprint's chapter/unit. This is a supporting Stacks tool below the inherited direct-image/perfect-test/cohomology-and-base-change chain, not a unit key node. No unit realization or chapter file is changed. blueprint_refs.py ancestor returns None because the inherited created.item chain no longer reaches an imported ancestor; new nodes preserve that null from.node and extend the inherited via list by the item. The detailed inherited from.place is retained and extended. Whole-blueprint searches for relative pseudo, composition relative pseudo, 09VA, 09UR, closed push pseudo, base change relative pseudo, pseudo coherent and pseudo-coherent returned no equivalent blueprint nodes; direct searches in literature/blueprint/latest/blueprint likewise found no equivalent statement.

## Not duplicates

No existing DAG node has source Tag 09VA or 09UR. DAG searches used those tags, their Stacks labels, and pseudo-coherent statements filtered for relative, closed immersion, base change and pullback.

lem-sfb-closed-pushforward-pseudocoherence vs lem-sfb-closed-support-relative-pseudocoherence: the new node is an ABSOLUTE statement about K on Z and Ri_*K on P, requiring i_*O_Z to be pseudo-coherent. The existing node compares RELATIVE pseudo-coherence over a third base, without that hypothesis. The existing node is not a replacement for absolute detection, and the delivery does not use its proof.

lem-sfb-relative-pseudocoherence-flat-base-change vs lem-sfb-scheme-relative-perfect-base-change: the new node preserves a prescribed finite stage m of relative pseudo-coherence for arbitrary E; relative-perfect base change has a different conclusion and extra quasi-coherence/Tor hypotheses.

lem-sfb-relative-pseudocoherence-flat-base-change vs lem-sfb-flat-ambient-relative-pseudocoherence: flat base change is a cartesian pullback statement, whereas the existing node compares relative and absolute pseudo-coherence after a fixed flat ambient embedding and depends on this item.

The two new nodes are genuine prerequisites of different kinds. Neither states a direction of this item's comparison across X -> Y -> S. Neither duplicates the existing all-affine-charts criterion, which the item reuses.

## Review by NY

I read coord/delivery-errors.md B--E in full, including the duplicated inherited sections, and checked the written nodes against them with their sources open. For the item I read the statement and whole proof of Stacks 09UT in more-morphisms.tex; for flat base change I read 09UR, lemma-base-change-relative-pseudo-coherent, statement and the chartwise derived base-change proof at lines 17110ff. Flatness of the new base kills positive Tor, so the new node is its flat specialization, without a hidden finite-presentation or quasi-coherence assumption. For absolute closed pushforward I read 09VA, perfect.tex lemma-closed-push-pseudo-coherent, statement and both halves of its induction proof at lines 2926--3007. Its required structure-module pseudo-coherence is explicit in the new statement and is proved before application in the item. I also read Modules 01AX, lemma-i-star-exact, for the ordinary closed pushforward calculation.

Step 1 cites the locally-finite-type definition for the covering choices, the existing all-affine-charts lemma for existence of i and k, the closed-immersion definition for the affine surjections, and the affine-space definition for the polynomial rings. Their statements provide exactly these data. Adjoining variables to the first surjection gives j; composing with the second gives l. Thus no theorem about base change or composition of closed immersions is being taken from a definition without proof. No intersections of arbitrary affine opens are asserted affine.

Step 2 uses the all-affine-charts lemma on O_Y[0] for every integer a and the relative definition to obtain the restricted relative hypothesis on V/W. The polynomial-projection-flat leaf explicitly states flatness of Spec B[T] -> Spec B. The new flat-base-change node then gives relative pseudo-coherence of the pulled-back structure complex on T. The derived pullback definition identifies that complex with O_T[0] by tensoring the rank-one free module; a second application of all-affine-charts gives the needed absolute pseudo-coherence of the derived structure-sheaf image on Q. Step 3 then identifies it with the ordinary pushed-forward structure module. The absolute definition states its equivalence with all finite stages. Each ambient scheme is affine at this point, j is already a proved closed immersion, and all finite-type hypotheses hold for polynomial maps and their quotients.

Step 3 uses the existing exactness node only for what it states, exactness on abelian sheaves along a closed topological inclusion. The extension to structure modules is elementary: kernels and cokernels carry their inherited scalar actions and have the same underlying abelian sheaves. Exactness allows computation of each derived direct image by the ordinary functor on representatives, in accordance with the derived-direct-image definition. The displayed equality of sections gives the composite identity term by term, including its ring actions. This avoids silently invoking a derived-composition theorem. This off-unit exactness lemma is a generic tool, declared in split_report.tool_uses; it does not replace any unit route.

Step 4 uses precisely the new 09VA statement: j is a closed immersion and steps 2--3 established its pushed-forward structure module is pseudo-coherent. It applies to K=Ri_*(E|_U) in the unrestricted derived category. Step 3 supplies the identification of its image with Rl_*(E|_U). There is no extra boundedness, Tor-dimension, coherent-cohomology or Noetherian requirement.

Step 5 cites all-affine-charts to test an already relative-pseudo-coherent E on the specifically chosen embeddings and the relative definition to assemble the converse witnesses. The covers over W and over V are separately described, so the two base schemes are never silently identified. Applying step 4 in both directions completes the argument for the fixed m. Every non-elementary fact in this assembly is a cited statement. Steps 1 and 3 are elementary constructions from their cited statements; steps 2, 4 and 5 are marked non-elementary. Every step is under 2000 characters, so none conceals a long auxiliary argument.

The new statements introduce all objects and cite their notions; both are unsplit with empty proof/proof_deps, so neither hides a proof in its statement. Their Stacks tags and exact labels were checked against literature/stacks-project/tags/tags. Searches were made through the prescribed msearch.py command with LeanFinder, LeanSearch, Loogle and Mathlib grep, followed by second semantic phrasings. Read all returned hits: these concern ordinary pushforward/adjunctions, pseudofunctor composition, morphism flatness/base-change, finite presentation or affine transition limits; none asserts pseudo-coherence of derived complexes. Loogle and the focused greps found no pseudo-coherent declarations. The exact logged query texts and actual successful results are recorded, without invented or unavailable-as-negative searches.

Small-case checks: for X empty both directions and both new nodes are vacuous; for E=0 all conclusions hold. For r=0 or n=0 the affine diagrams and the formula n+r still make sense, including identity embeddings. On a point an infinite-dimensional vector space in degree 0 is m-pseudo-coherent for m>=1 by the zero approximation but not for m=0; the item retains its finite-stage statement and never replaces it by full quasi-coherence or all-stage pseudo-coherence. For the closed-pushforward prerequisite, the quotient of the dual numbers by their nilpotent parameter is pseudo-coherent despite an infinite free resolution: the node requires pseudo-coherence, not finite projective dimension. Identity and zero/empty flat base changes satisfy the new flat statement, and its proof source does not require a finite-presentation base change. Non-Noetherian rings are allowed throughout; the structure-sheaf hypothesis on j is retained, since dropping it for an arbitrary quotient would make the absolute comparison false already for K=O_Z[0].

No source error beyond the proof-index typo was found. No SGA source is cited. All citations.json entries were copied verbatim from the cited statements, including the new ones. No maintained field, other item's node, repository file, launcher file or Lean source was edited.

## Remaining work

The two new prerequisites are intentionally statement-only stage-1 queue items. No unfinished argument remains in the item's five-step split. The first server dry run passed at 8f28294b812. The final reading then made the distinction between Rj_*(O_T[0]) in step 2 and (j_*O_T)[0] explicit; step 3 supplies their equality before the step-4 application. A fresh dry run and delivery follow this notation repair.
