## Worker report

Files written: `dag/nodes/sec-smooth-purity/prop-sf-pf-reduction.json` (item, split); `dag/units/sk-prop-sf-pf-reduction.json` (unit realization); `citations.json` (citation audit); and this report. No new node files were created.

The item is split in place with no new child nodes. I checked the unit route in `dag/units/sk-prop-sf-pf-reduction.json`, the section proof in `dag/notes/sec-smooth-purity/sk-prop-sf-pf-reduction.json`, and the imported item node. The source declaration search in `WeilConjectures/SixFunctors/Etale/Derived/Exchange.lean` found only `nonempty_iso_reductionModIdeal_rightDerivedLowerShriek` (lines 177–180) and `nonempty_iso_reductionModIdeal_leftDerivedUpperStar` (lines 193–196), both with `sorry`; no declaration states the proposition itself, so this is not an attachment.

## New nodes

None. The existing nodes `lem-fix-operation-reduction`, `lem-fix-compact-support-coefficient-change`, `def-exchange-projection`, `def-sf-pf`, `lem-sf-generating-class-determination`, and `thm-sf-pf-finite` already state the comparisons, map construction, warning about equality of natural transformations, and finite-level invertibility needed by the proof.

## Attachments

None.

## WANTED

None.

## What was wrong in the node, blueprint, or brief

The imported proof compressed the construction of the reduction square, the mate calculation, and the invertibility cancellation into one paragraph, and its phrase “both horizontal maps” was ambiguous about whether it referred to the projection maps or the comparison arrows. I rewrote it as three steps: (1) identify the four comparison isomorphisms; (2) prove commutativity by transposing the two routes and using counit and tensor coherence; (3) cancel the comparison isomorphisms and apply the finite projection theorem at both levels. The imported statement omitted the morphism f and did not define K_m,L_m as the reductions; I repaired it by introducing f explicitly and writing K_m=K⊗ᴸA_{E,m} and L_m=L⊗ᴸA_{E,m}. No mathematical statement error or false small case was found.

## What could not be finished

Nothing. The split is DAG-only as required.

## Review by NM

For the item I read the unit and section sources named above and the archived source module. The preflight caught that the imported statement was not standalone: f was implicit and K_m,L_m were only named. I corrected those hypotheses and definitions before this review. The two source declarations carrying the blueprint tag are explicitly `sorry`, so I did not attach them. For step 1 I opened `lem-fix-operation-reduction`: it states that finite reduction commutes with pullback, tensor, and compact-support direct image and that all comparisons preserve tensor associativity, units, and counits. I also opened `lem-fix-compact-support-coefficient-change`: it states that the compact-support coefficient comparison is an isomorphism on bounded constructible finite-Tor complexes and is compatible with reductions, pullback, and the counits defining projection. These statements supply exactly the comparison arrows and their hypotheses.

For step 2 I read `def-exchange-projection` and `def-sf-pf`; they give the displayed projection transformation and its compactification description. I used the compact-support node’s explicit counit compatibility and the operation-reduction node’s preservation of counits and associativity to justify equality of the two transposes. I also checked `lem-sf-generating-class-determination`, whose statement warns that equality of comparison maps must be proved from constructions; the step follows that warning and does not use stalk or generator detection. For step 3 I re-read the two comparison statements for their isomorphism claims and `thm-sf-pf-finite`, whose hypotheses match the finite rings (A_{E,n}), (A_{E,m}) and the (D^b_{ctf}) objects; cancellation in a commutative square then gives the claimed equivalence. I recorded verbatim statement excerpts for every cited node in `citations.json` and corrected the imported horizontal/vertical map ambiguity in the proof text.


## Second reading by NM

- Step 1: checked the complete statements of `lem-sf-proetale-constructible-origin`, `lem-sf-comparison-tor-amplitude` and `lem-sf-flat-model`, including their site, boundedness, finite-Tor and Noetherian clauses; PASS after adding the actual witnesses and bounded flat constructible models. Finite-type-over-field schemes meet the flat-model lemma's explicitly stated example of the Noetherian hypothesis. Tensoring the models and pulling back their finite stratifications checks every coefficient domain used later.
- Step 2: checked `lem-fix-operation-reduction` and `lem-fix-compact-support-coefficient-change` against the level-n and level-m source/target objects; FIX: replaced the unexplained “four vertical comparison isomorphisms” by the two explicitly typed composites u and v in the actual square. Its upper arrow is rho(PF_A), not PF_A.
- Step 3: checked the full statements of `def-exchange-projection`, `def-sf-pf`, `def-compact-support-direct-image-detailed` and both coefficient-comparison lemmas against the unit's counit–tensor argument; FIX: wrote the counit identity, the common transpose, and the extension-by-zero tensor identity. The proper direct image is used via the compactification (id,p); no finite ordinary-direct-image commutation theorem for an arbitrary map is assumed. Equality follows from the specified maps and their stated unit/counit/tensor compatibility, not from testing a generating class.
- Step 4: checked `thm-sf-pf-finite` on its stated étale domain and `lem-weil-finite-compact-projection-formula` on its witnessed pro-étale domain; FIX: cancellation proves only the statement about rho(PF_A). The original-map equivalence follows by applying the finite theorem at both levels, exactly as the unit's closing sentence does.
- New nodes: none; checked the sandbox inventory. There are no new statements to duplicate-check, no Mathlib leaves to verify, and no new-node Mathlib searches to record. All facts newly needed by the repaired argument were already existing nodes.
- Item statement: checked hypothesis by hypothesis against `dag/notes/sec-smooth-purity/sk-prop-sf-pf-reduction.json`, the unit's statement and proof, and `WeilConjectures/SixFunctors/Etale/Derived/Exchange.lean` lines 167–196 plus `Coefficients.lean` lines 75–105 in the read-only slopmaster2 source. Retained the first worker's explicit f, positive levels and definitions of the reductions. The two source declarations cover only the operation comparisons, not this proposition, and both are `s: true` in `local/sorry_map_slopmaster2_7d675a26.jsonl.gz`; neither is a finished proof or attachment. The node and unit sources are blueprint Markdown, with the imported unit/section text retained in the DAG; neither the item nor any new node names a Stacks tag requiring a new .tex comparison.
- Small cases: K=0 or L=0 gives the zero-to-zero projection isomorphism; an empty source gives zero compact support; f=id over a point gives tensor reassociation; m=n gives identity coefficient comparisons; n=1 forces m=1. For n=2,m=1 the ring quotient is generally nonflat, so the proof uses derived scalar extension and flat models, never flatness of A to B. All checks pass.

Changes and reasons:

1. Added a domain-check step using existing origin, Tor-comparison and flat-model nodes. The previous proof applied an étale theorem to intrinsically pro-étale objects without supplying the needed witnesses. These existing nodes repair the gap without adding a hypothesis or changing the statement.
2. Replaced the vague reduction square by a displayed square and explicit u,v composites, and expanded the mate calculation into a typed counit equation and common transpose; this makes the non-elementary comparison checkable from exactly the cited statements.
3. Removed the false cancellation inference about the unreduced PF_A. Both original projection maps are invertible by the finite theorem, with its pro-étale version cited explicitly, so the source's asserted equivalence is retained.
4. Retained `lem-sf-generating-class-determination` and explicitly respected its warning about equality of natural transformations; the unit cites that warning as part of its route. Regenerated the citation quotes directly from the cited statements, and aligned the split report with the repaired four steps. No new nodes or leaves were added.

The generic existing nodes `lem-sf-proetale-constructible-origin`, `lem-sf-comparison-tor-amplitude`, `lem-sf-flat-model`, `def-compact-support-direct-image-detailed`, and `lem-weil-finite-compact-projection-formula` are used as tools for site/domain checking, compactification notation, and the finite theorem's witnessed realization. They do not replace the unit route (mate comparison followed by the finite projection theorem); the unit's cited comparison, determination and finite-theorem route has no separate statement furnishing these domain checks. The maintainer may record any required tool-use approvals; no `tool_uses` field was written here.

STATEMENT-DISPUTED (imported wording, already repaired by the first worker): the displayed PF_{f,K,L} used an unbound f, and K_m,L_m were named without their coefficient-reduction definitions. The literal imported statement is not standalone. Its faithful correction introduces the separated finite-type f and K_m=K tensor^L_A B, L_m=L tensor^L_A B, with 1 <= m <= n, as in the unit's proof. This second reading retains that correction; no additional statement change was necessary.

Dry-run repair: the refreshed delivery baseline had changed the surrounding statement of `def-sf-pf`, so the full-statement quotation was no longer verbatim there. Narrowed that citation to its unchanged displayed projection-map formula, which is exactly the notation used in step 3.

Dry-run route repair: preflight requires the imported unit’s determination-warning citation to remain reachable. Restored `lem-sf-generating-class-determination` in step 3 with its verbatim statement quotation and an explicit account of how its warning is satisfied.
