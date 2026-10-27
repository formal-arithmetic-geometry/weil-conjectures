## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-action-free-restriction.json: statement item, now split; its statement and statement dependencies are unchanged. The theorem is not a Mathlib leaf.
- citations.json: a verbatim statement quote for every node used in every proof step.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, profinite/free restrictions and right translations. Hits concern discrete modules, algebraic groups or unrelated free restrictions; none states this item. The source project's declarations containing sorry are not used as completed proofs.

## WANTED

WANTED: an exact external non-SGA reference for the profinite free-parameter restriction and internal right-translation action, for lem-sfb-profinite-action-free-restriction. The source node already identifies this as agent-formulated auxiliary infrastructure. The explicit proof here is marked proof_origin.by = agent.

## Corrections and scope

No statement dispute and no statement correction. This is the repair of the retained Q105 delivery: its approved five-step proof, citations, prior report and logged searches are preserved. The current live item is still unsplit, has the same statement and statement dependencies, and has no released stage-1 repair note. I rebased the retained split-owned fields onto the current live node, rather than treating the side-project completion as a live completion. The existing null blueprint.from.node is retained: tools/blueprint_refs.py ancestor returns None. The exact paragraph and returned presentation steps are recorded in blueprint.from.place and split_report.blueprint. Whole-blueprint searches for “right translation” and “profinite action” produced respectively an unrelated group-scheme definition and no imported node.

I read the chapter record and unit record and the current main-20261015 direct-images proof. Paragraph (3) concerns proper and open direct images and their compactification assembly; it does not assert the auxiliary presentation theorem. This split realizes the same auxiliary free-restriction route specified in the item's source, without changing the unit or chapter. The generic Stacks 00WW lemma belongs to another unit, so its precise use is declared in split_report.tool_uses.

## Mathlib searches

The pre-existing searches were retained and their results re-read; no search question or statement changed during this repair, so no search was repeated. The searches from the original split are logged in searches.jsonl and copied as actual result records to the item: LeanFinder for free parameter restriction and internal right translations; Loogle for “Condensed” and “Action”; grep in Condensed for translations/free actions/action sheaves; and two LeanSearch phrasings. I read the returned ContAction.resComp definition in Mathlib/CategoryTheory/Action/Continuous.lean and the condensed constructors in Mathlib/Condensed/Explicit.lean. The former restricts actions along group homomorphisms; the latter requires a sheaf/equalizer condition and supplies no reconstructed internal action. The second LeanSearch returned value-category composition lemmas rather than this free-space restriction construction. No exact theorem or one-line specialization states every clause of the item.

## Not duplicates

No new node is proposed. I reused lem-sfb-profinite-action-finite-cover-site rather than creating a group-valued representable sheaf or action-site lemma. I reused lem-weil-pbc-site-continuous-pushforward-sheaf rather than creating another cover-and-pullback sheaf restriction lemma. DAG and blueprint searches for right translations, profinite actions, representable sheaves and continuous-map descent were read before settling this dependency list.

## Review by Q105

I checked B through E of coord/delivery-errors.md against the item, the actual cited statements, and the sources. There are no unsplit new nodes, so there is no new statement with hidden proof, missing notions or duplicated Stacks tag. The statement introduces J, P, P_J, F, H, the parameter maps and the action, and cites the existing definition nodes. All recorded searches from the original split were actually run with msearch.py; I read the hits and recorded their limitations. No SGA source was used.

For the item I read the current blueprint paragraph (3) at the exact source path. It supplies the surrounding direct-image route, not a proof of this agent-formulated auxiliary theorem. I read Stacks sites.tex Definition 00WV (definition-continuous) and Lemma 00WW (lemma-pushforward-sheaf), including its proof, and Definition 00VM (definition-sheaf-sets) with its empty-cover remark. No external source is represented as asserting more than it says. No new node needs a separate source review.

Step 1 cites lem-sfb-profinite-action-finite-cover-site, whose statement explicitly says that P_J is a finite-cover site and that the continuous-map descent assertion also holds on P. This gives the sheaf C(-,J) for a profinite J, without borrowing an abelian-only condensation result. Group operations and the induced action on h_T are pointwise continuous and satisfy the equations pointwise. I verified that J is compact Hausdorff totally disconnected, exactly the target class permitted by that continuous-map descent statement. This citation does not use the parent presentation theorem, which would make a cycle.

Step 2 cites def-sfb-profinite-action-parameters, which gives H(S)=J times S, left multiplication on J, and H(f)(j,s)=(j,f(s)). The proof computes the fibre product in both directions, checks continuity by coordinates and equivariance, and lifts each (j,s) along a jointly surjective family by keeping j fixed. Naturality follows because both projection maps retain the same coordinates. This is a direct verification, not a new lemma that merely restates the item. It does not claim preservation of the terminal object: H(point)=J generally is not the terminal action.

Step 3 cites lem-weil-pbc-site-continuous-pushforward-sheaf. I read its full statement: its hypotheses are preservation of covering families and the isomorphism for the covering pullbacks, and its conclusion is exactly that F composed with H is a sheaf. Those hypotheses are supplied in step 2 for arbitrary maps into S, not only overlaps. The finite-cover-site citation in step 1 supplies the required site structure. I also spelled out matching-family gluing, so the application is checkable against Stacks 00WW rather than a vague appeal to continuity.

Step 4 cites only the definition clause of lem-sfb-action-topos-geometric-restriction: a K-object is a sheaf with a sheaf morphism K times X to X satisfying unit and associativity. It does not use the action-site equivalence or geometric-morphism assertions. I checked the order carefully: r_h after r_g sends (j,s) to (j g(s) h(s),s), hence is r_(gh). Contravariance then gives F(r_g) after F(r_h)=F(r_(gh)). The displayed base-change square is checked on (j,v) and gives exactly the restriction equation for the action. No inverse or commutativity hypothesis is inserted.

Step 5 uses the same cited node's definition of equivariant sheaf morphisms. Naturality of alpha for H(f) is the sheaf-map condition, and naturality for r_g is the equivariance equation. Identity and composition are checked componentwise. Every node cited in a step has a verbatim statement quote in citations.json; none of these uses requires material from the cited node's proof.

Small cases: for the empty parameter space H(empty)=empty; the empty covering forces F(empty) and thus G(F)(empty) to be singletons. Finite covers can have empty members without affecting the lifting argument. For the trivial group, H is naturally the identity and every translation acts as the identity. Noncommutative J is allowed, and the computed composition order gives a left action without inversion. All five proof steps are under 2000 characters and carry their explicit arguments; none hides an omitted comparison lemma. What is not elementary (the site/continuous-map descent result and the general sheaf restriction theorem) is cited, while the coordinate and naturality verifications are marked elementary.

## Unfinished work

None for this one-level split. The existing cited DAG nodes retain their own independent stage obligations. No Lean files were written and no compiler, Lake or build command was run.

## Return repair: live-DAG promotion

The return says that the reader approved the split but landing refused the side-project completion because it had not reached the live DAG. The retained dry-run receipt identified the previous delivery head as 38061f34965. I compared the retained node with the current shared DAG: the statement, statement dependencies, source, created record, chapter, unit and blueprint lineage agree; the live item has no proof and remains unsplit. The differences are the proposed proof, proof dependencies, proof origin, split status, search records and split report. I reconstructed the delivery node from current live metadata plus those retained split fields, and updated its split report to record this repair. The delivery tool prepares its own commit on the current server base; the first required dry run passed at 8bb1a54fb74 before these report updates.

I re-opened every cited current node, including all statement dependencies. The four proof dependencies are lem-sfb-profinite-action-finite-cover-site, def-sfb-profinite-action-parameters, lem-weil-pbc-site-continuous-pushforward-sheaf and lem-sfb-action-topos-geometric-restriction. Their used statement clauses have not changed: each of the five retained citations.json quotes is still a verbatim substring. The finite-cover-site node remains an independent unsplit obligation; it still states descent for continuous maps on P, exactly what step 1 uses. The parameters node still defines the identical H and H(f). The 00WW node still assumes only covers and covering pullbacks, which step 2 verifies, and the internal-action node still gives exactly the definition used in steps 4 and 5. No replacement citation or mathematical route adjustment is required.

In this repair review I again read the current blueprint paragraph (3), Stacks sites.tex Definition 00WV (definition-continuous), Lemma 00WW (lemma-pushforward-sheaf) and its proof, and Definition 00VM (definition-sheaf-sets) with remark-sheaf-condition-empty-covering. I checked the empty parameter space, trivial group and noncommutative composition order again. The proof steps have respectively 648, 747, 655, 839 and 602 characters, so no long step conceals an unreviewed lemma. This addresses the return by a current-base reconstruction and citation revalidation; it does not claim that a side completion alone discharged the live obligation. No shared repository files, launcher files or Lean sources were modified.
