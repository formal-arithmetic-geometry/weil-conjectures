## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-monoid-unit-pushout.json: existing statement, now split by specialization of a reviewed generalization; no Mathlib match.
- citations.json: verbatim statement quotations for both cited nodes.
- No new DAG nodes and no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the item id, GrothendieckGroup, integral/cancellative monoid and unit-pushout notions; no declaration states the item.

## Wanted literature

WANTED: Kato (1988), Logarithmic structures of Fontaine--Illusie, section 1, or Ogus, Lectures on Logarithmic Algebraic Geometry, I.1.3, for the general mixed integral-monoid pushout calculus. This request is inherited, not a claim that either document was read. ILO VIII 3.1.2, printed p.98, was read and gives the integral localization convention only, not this mixed-pushout assertion. Proof origin is agent.

## Findings and corrections

The unsplit item repeats conclusions of the previously reviewed lem-per-integral-monoid-unit-pushout. Reused that node rather than creating another copy or moving clauses into new nodes. Its additional embedding into the explicitly described group H is not needed. The statement and statement dependencies are unchanged. The phrase “monoid algebra construction” in the existing lemma is imprecise, but its following sentence explicitly defines the group completion by formally adjoining inverses; step 1 verifies agreement with our generators-and-relations construction. No statement dispute is needed.

The inherited blueprint.from.node is null, and blueprint_refs.py ancestor confirms None. Retained that provenance and the precise inherited place, without inventing a blueprint id. Searched the whole DAG by group completion, groupification, cancellative, GrothendieckGroup, and the blueprint via blueprint_refs.py search for integral monoid and pushout. Read latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md (3), and the chapter/unit records. The current blueprint has no equivalent monoid lemma; same_as is []. The generic algebra tool does not replace any geometric unit step. Its off-unit use is declared in split_report.tool_uses for the maintainer to review.

## Not duplicates

No new nodes. The existing lem-per-integral-monoid-unit-pushout is deliberately reused: its hypotheses agree and its conclusion strictly contains this item's conclusion.

## Review by Q94

I read ILO Expose VIII 3.1.1--3.1.2 on printed p.98, the full statements of def-trf-abelian-group-presentation and lem-per-integral-monoid-unit-pushout, the latter's reviewed proof, and the group-completion clause of def-trf-fs-log-blowup used there. ILO describes localization inside the group completion for an integral monoid; it does not prove the mixed pushout. No Stacks tag is falsely attributed to that assertion. No new node has a source to audit.

Step 1 uses only the actual quotient-of-free-integer-module definition in def-trf-abelian-group-presentation. Sending a basis generator to u(p) kills each defining relation; the induced map is unique on generators. This elementary verification shows that the two group-completion conventions agree, including their canonical maps from P. It does not assume a theorem about a particular unspecified completion.

Step 2 uses the statement, not internal proof constructions, of lem-per-integral-monoid-unit-pushout. I checked its commutativity and integrality assumptions against ours, its submonoid E and arbitrary monoid homomorphism f into an abelian group, and both defining quotient relations. Its statement explicitly gives integrality in the group completion, cancellation, the injection of G, the free multiplication action and both equations in the iff criterion with the same orientation. Neither finite generation, saturation nor injectivity of f is introduced. The generic lemma is in another unit and its use is declared, without setting top-level tool_uses.

For small cases, E={1} gives M=P times G, with the criterion reducing to equality of both coordinates; P=E=N and G=1 gives the trivial pushout, testing noninjective f; and P=N^2, E=N(1,0), f trivial gives M=N on the second coordinate. If P is the trivial monoid then M=G. These cases agree with integrality and freeness (a trivial G acts freely). The quotient relations also give [p,g]=[pe',f(e')^{-1}g], confirming the equation orientation independently. The existing lemma does not depend on this item, and the remote DAG checks will test the entire dependency graph.

I checked delivery-errors B--E: there are no new nodes with hidden proofs, missing definitions or duplicate clauses; no unsupported tag is used; the only substantive inference cites a statement that explicitly contains every conclusion; the convention step is elementary and written out; no unproved inline sublemma or step over 2000 characters occurs. All current searches were run via msearch.py and recorded exactly from searches.jsonl, with prior searches preserved. Read GrothendieckGroup.lean:36--50,77--95 and PushoutI.lean:192,588--601: these do not supply the mixed pushout. The second LeanFinder phrasing returned localization cancellation only. There is no Mathlib leaf or project attachment to claim.

## Unfinished work

None in the stage-1 split. The independent maintainer review and later Lean formalization remain their respective stages.
