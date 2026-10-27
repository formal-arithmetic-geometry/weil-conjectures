# Stage-1 report: lem-sf-normalized-factorization-transpose-coherence

## Files written

- dag/nodes/sec-six-functors/lem-sf-normalized-factorization-transpose-coherence.json: statement, split into six explicit steps; no exact Mathlib match for the combined assertion.
- citations.json: six entries, one for each step/node citation, quoting the statements verbatim.
- searches.jsonl: actual searches recorded by msearch.py; their results were read.
- report.md: this report.

No new nodes, no Mathlib leaves created, no Lean written or compiled.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id and for normalized factorization / factorization transpose found no declaration proving the item. Broader searches for conjugateEquiv, counit normalization and homEquiv_ofNatIsoLeft found categorical ingredients and derived-adjunction results, but none states all the item's clauses with its hypotheses. In particular the derived normalization uniqueness theorem imposes localization hypotheses and proves a different assertion.

## WANTED

None for this proof. The inherited brief mentions coord/dag-sync.md, absent in this read clone; this does not obstruct the source and delivery checks.

## Audit and changes

The original statement is unchanged. Its proof was empty. The existing source and blueprint ancestry are retained. The item needs cancellation and a few explicit transpositions, not further clause-shaped nodes. I searched the entire DAG for conjugation, adjunction transport and Tag 0B65, and searched imported blueprint nodes with blueprint_refs.py for conjugate, normalized factorization and coherent right adjoint. I read the candidate statements. Existing lem-sfb-adjunction-transport-left-iso gives precisely the transported Hom formula; existing lem-sfb-coherent-right-adjoint-comparisons gives the pro-etale transpose identity. Neither is recreated. The latter is declared as a generic tool use in split_report, as it belongs to another unit; no geometric unit route is changed.

The item-level Mathlib searches used all four prescribed modes. Loogle found homEquiv_ofNatIsoLeft_apply and its inverse formula. Grep located those at Basic.lean:509,515 and conjugateEquiv_counit / conjugateEquiv_comp at Mates.lean:285,350; I read the source. LeanSearch returned CatCommSq constructions and lifting results, while the first LeanFinder phrasing returned leftAdjointUniq and composition isomorphisms. A second LeanFinder phrasing returned CommSq.left_adjoint/right_adjoint and adjoint-lifting results. These do not state the item's faithful normalization squares plus normalized-counit assertion. Search results and queries already in the live item are retained as inherited evidence; only actual locally logged queries are appended.

## Not duplicates

No new nodes. The existing transport and coherent-comparison nodes are reused directly. The normalized comparison-square node lem-kun-adjunction-comparison-square and the equivalence-square inverse-mate theorem were read as alternatives; their different typing/equivalence setting is unnecessary for the present proof.

## Review by Q132

I read GOAL.md, the worker and stage-1 contracts, the three fixed/followed/free blueprint levels in SETUP.md, and both copies of delivery-errors.md sections B through E. I read the item's six-functor chapter and its recorded f-shriek-preservation unit, the current main-20261015 site-comparison proof, and the parent's use of this lemma. The source says locally closed exceptional comparison commutes with site pullback and uniqueness makes comparisons coherent. This item's categorical formulation supplies the factorization-normalization part of that claim. I also read Stacks categories.tex Tag 0037 (definition-adjoint and the ensuing discussion of unit, counit and the two Hom formulas), and Tag 0B65 (lemma-transformation-between-functors-and-adjoints), including its proof. The detailed six-step assembly is agent-written, as recorded; the blueprint alone is not credited as a human proof. No prohibited SGA source is used.

For step 1 I checked all four assumed squares with right-to-left composition. The two arrows to which injectivity is applied really have source F_e L and target E_e L. Cancelling B is legitimate because B is an isomorphism. No fullness, equivalence, or faithfulness on unlisted Hom sets enters.

For step 2 I opened lem-sfb-adjunction-transport-left-iso and verified that its statement sends f to adj(f composed with r_e). Thus h_0 r_e inverse becomes h_0 exactly. The square for h-prime follows by multiplying the specified Delta square by the inverses, and the q_p-prime inverse equation follows from q_p-prime r_p=q_p. These cancellations are written explicitly and are elementary relative to that cited formula.

For step 3 I opened lem-sfb-coherent-right-adjoint-comparisons and checked its Hom identity, the conjugate orientation, and its indexed hypotheses. The explicit two-element construction phi_ji=e_j e_i inverse satisfies every cocycle by cancellation and includes the reverse and identity comparisons; it does not assume those comparisons as extra input. The node's comparison is the conjugate of r_p inverse, hence exactly t, with target J-prime. This is the only non-elementary application beyond the transport/adjunction formulas. The tool is a generic categorical statement, with no finite-coefficient or geometric assumptions being imported.

For step 4 I opened lem-weil-pbc-adjunction-of-natural-bijection and checked its inverse formula adj inverse(b)=epsilon F(b), along with its definition of the counit as the inverse transpose of the identity. Together with the transport node this gives epsilon_e-prime=epsilon_e r_e inverse at RM, without assuming a counit identity absent from the cited transport statement. H=RM belongs to A_0 by the explicit hypothesis, so Delta_H and every square used exist. Cancelling Delta_H-prime identifies the pro-etale arrows, and the bijection then gives gamma-prime=t gamma. This is an explicit specialization of steps 2 and 3, with no hidden comparison lemma.

Step 5 only inverts gamma-prime=t gamma and cancels t; rho is the very same arbitrary isomorphism on both sides. For step 6 I read the entire statement of def-weil-pbc-adjunction-conjugate, especially its reversed composition, identity and inverse laws. The inverse of s_p r_p is r_p inverse s_p inverse, and its conjugate is u t, in the required order. The transport node's actual Hom formula proves successive transport equals composite transport. The proof spells out the composite squares, transformed lifts, gamma cocycle, theta cocycle and identities, covering every comparison in the statement. No citation uses another node's proof instead of its statement; citations.json quotes each cited statement verbatim.

I checked the terminal category, identity comparisons, empty A_0 (the H clause is then never instantiated), and identical left/right functors carrying different specified adjunctions. In the last case t can be nonidentity even when r_p is identity between underlying functors, exactly as conjugation with the two specified adjunctions requires; the proof does not replace t by identity except for an identity change of the adjunction datum itself. Arbitrary successive choices are handled by conjugation across the intermediate adjunction. All formulas type-check at the level of sources and targets, including h-prime with source F_p-prime C_S L and both normalized counits at C_T M. No statement dispute was found.

Every proof step is below 2000 characters (the longest is 1076). Elementary steps contain only cancellation, functoriality, substitution into cited formulas, or inverse identities. No new unsplit node contains a proof, no new definition is needed, and no new node duplicates or repackages a clause of the item. I preserved all non-split-owned item fields.

## Unfinished work

None in this one-level split. Independent maintainer review remains the delivery workflow's next step.
