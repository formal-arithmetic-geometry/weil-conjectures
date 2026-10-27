# Q82 stage-1 delivery

Item: lem-sfb-finite-etale-formal-monoid-coefficient-lift.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-etale-formal-monoid-coefficient-lift.json: statement unchanged, split by direct reuse of an existing exact theorem; Mathlib verdict no match.
- citations.json: one verbatim statement quotation for the one cited node in step 1.
- searches.jsonl: actual search-command log for this attempt.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag and by formal-monoid, MonoidAlgebra and finite-etale coefficient terminology found no declaration stating this theorem. In particular, the stale lean record on the existing lem-per node says its former Sheaf module was deleted; it is not evidence of a finished project proof. No compiler or Lake was run.

## WANTED

None. The Stacks sources used for this comparison are available locally.

## Findings and changes

The requested item duplicates the already split and reviewed node lem-per-finite-etale-formal-monoid-coefficient-lift, in sec-deligne-laumon-a1. That node has precisely the same hypotheses and all the same conclusions. Its statement omits only the requested item's final explanatory sentences defining local, complete, the repeated notation D[[S]], and kappa(K); these spell out the same meanings. In particular the older node also allows f=0, imposes no nonzerodivisor hypothesis, uses combined-adic monoid-ring completion rather than ordinary completion of coefficients alone, and asserts an A0-algebra isomorphism with the coefficientwise image of f. There is no weaker coefficient category or changed morphism.

Accordingly I created no auxiliary node and did not reproduce its eleven-step proof. This is the explicit duplicate-reuse exception in the brief, not moving an item's proof into a new node: the cited result pre-existed this delivery, has been independently reviewed, and serves another parent. The one assembly step invokes its statement. The original statement, source, statement dependencies, created record and blueprint ancestry remain intact. The off-unit use is declared in split_report.tool_uses: the cited theorem is a generic complete-local algebra tool and leaves the inherited alteration route unchanged.

The latest blueprint direct-images proof, clause (3), treats direct image by proper and open factors; the item's inherited detailed ancestry refines the open finiteness argument by alterations. I read literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/{_section.md,sk-thm-sf-ctf-stability-direct-images.proof.md}, and the chapter and unit records. The current blueprint does not itself state the formal monoid coefficient result. tools/blueprint_refs.py search 'formal monoid' returns zero imported blueprint nodes. The ancestor command returns None for this item's inherited created.item chain, so I retained the existing blueprint.from.node=null and its precise from.place rather than inventing an imported ancestor. The similarly named det-thm-sf-ctf-stability-direct-images is only the inherited textual place here, not an id to fabricate.

## Not duplicates

No new nodes. The exact pre-existing duplicate is lem-per-finite-etale-formal-monoid-coefficient-lift, so this delivery reuses it. The present item's existing identity is preserved for its current parent; a global merge/repointing would be a maintainer operation outside this worker's scope.

## Review by Q82

I read the item's complete statement and the existing lem-per-finite-etale-formal-monoid-coefficient-lift statement, all eleven proof steps and review record. For the sole new assembly step, its only cited statement explicitly supplies D, all the regular/complete/Noetherian/local/finite-etale properties, the specified residue field, the continuous A0-algebra isomorphism using coefficientwise f, maximal-ideal equality and the nonzero cotangent classes. Thus C4 holds by literal hypothesis and conclusion comparison, and citations.json quotes the entire exact statement verbatim. There is no unquoted comparison theorem hidden in the assembly step: the objects are the same completions of the same monoid rings at the same ideals, with the same coefficient ring and hypersurface. C1 is satisfied by this single exact theorem citation, not by citing only definitions or a proof internal to another node.

For the source verification I read Stacks more-algebra.tex, lemma-finite-etale-equivalence (09ZL) and lemma-complete-henselian (0ALJ), and algebra.tex, lemma-henselian-cat-finite-etale (04GK), lemma-regular-goes-up (07NF), lemma-when-finite-module-complete-over-complete-ring (031B), lemma-local-flat-ff (00HR) and lemma-faithfully-flat-universally-injective (05CK). These explain the existing theorem's two henselian equivalences, regularity ascent and preservation of cotangent classes. In particular 031B requires separatedness; the existing theorem uses the Noetherian finite-module-completion result 00MA rather than applying 031B without that hypothesis. Its finite-basis argument identifies D tensor_E E[[S]] with D[[S]] at each finite quotient; it does not commute arbitrary tensor products with inverse limits. Its full-faithfulness argument works over the complete local ring A0, with matching residue identifications, so the resulting isomorphism is the required A0-algebra map. Equality m_D=nD then identifies maximal-ideal and quotient-adic topologies.

I checked B1--B10: no new node needs a proof, definition or search; statement and TeX are retained; references use actual local Stacks labels; all newly recorded search queries were run by msearch.py, their returned hits read, and no Mathlib match is claimed. LeanSearch returned etale-algebra decomposition over fields, whose source Mathlib/RingTheory/Etale/Field.lean I opened; it does not prove this complete-local statement. Two LeanFinder phrasings returned standard-etale presentations and square-zero lifting, which do not identify this formal-monoid coefficient algebra. Loogle and the Mathlib grep returned no matches for the queried etale/completion combination. The prior recorded searches are retained as required.

For C5--C8 and D1--D5 I searched the whole DAG, not just the item's chapter, found and reused the exact existing node, and computed its statement/proof dependency closure: 409 nodes, none equal to this item. Thus the new edge introduces no cycle, no new relabelled clause and no new restatement of the whole item. The one off-unit exact theorem is declared as a tool use, with no route departure.

For E1--E7 I compared all hypotheses before specialization. Small cases: S={0} reduces to finite etale lifting over E/(f); E a field makes the cotangent clause vacuous; f=0 gives the unquotiented formal monoid theorem; E=Z_p, S=N, f=p allows nilpotent-free reduction and unramified coefficient extensions; S=N and f=t^2 permits a nonreduced hypersurface, and no reducedness is assumed. The proof never asks f to be nonzero or a regular element. Sharpness excludes sums of nonzero monoid elements equal to zero, which is precisely what the augmentation used in the existing proof requires. K nonzero local ensures the residue algebra is a field; no connected component or factor has been silently dropped. No statement dispute, mathematical correction, SGA source or new statement is needed.

No proof step exceeds 2000 characters. The delivery dry run will perform server preflight and the DAG/split checks; its outcome is recorded below once completed.

## Unfinished work

None in the requested one-level split. The cited pre-existing theorem is a natural-language DAG result, not a claim that a Lean proof is finished.
