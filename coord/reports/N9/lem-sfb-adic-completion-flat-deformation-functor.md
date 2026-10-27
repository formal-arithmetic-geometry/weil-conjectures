# Stage-1 delivery: lem-sfb-adic-completion-flat-deformation-functor

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adic-completion-flat-deformation-functor.json: item, statement, split in seven steps; not a Mathlib leaf. Statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-two-ideal-adic-completeness.json: new statement-only node, unsplit, no Mathlib match; the full generality of Stacks 0DYC, rather than a restatement about deformation algebras.
- citations.json: one verbatim statement quote per cited node per step.

## Attachments

None. Searching WeilConjectures by the item blueprint tag and by completion/deformation found no declaration stating the item. Existing general completion declarations are supporting inputs, not an attachment for the groupoid functor, base change and automatic completeness together. No Lean was written or compiled.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Corrections and scope

No statement dispute. The imported item had no proof, and its original statement and all five statement dependencies are retained. The existing Mathlib search results on the item were read: flat_of_isNoetherian supplies only one completion property, not the item. The new node's searches were actually run through msearch.py, logged in searches.jsonl, and read; both semantic phrasings, Loogle and source grep yield no two-ideal completeness theorem. The of_lift candidate assumes its target already complete and is a universal-property equality, not a completeness-lifting criterion.

The important base-change detail is that the extended old ideal L need not equal the new inverse-image ideal K. Step 4 proves K=L+m_A1 Q1 and K^(n+N) contained in L^n contained in K^n. No false equality of these ideals or unjustified tensor/limit interchange is used. A1 is finite as an A-module even though A to A1 need not be surjective: its finite k-spanning set also spans it over A. This supplies exactly the finite-module hypothesis of 00MA.

The unit and chapter records and the latest blueprint unit were read. This generic commutative-algebra prerequisite implements the parent's 0DYV input within the given alteration/deformation route, without replacing a unit step. The two non-Mathlib commutative-algebra inputs from the proper-base-change chapter are declared as generic tool uses in split_report. The inherited blueprint ancestry has from.node=null; blueprint_refs.py ancestor confirms None for this chain. That inherited ancestry was preserved, its exact place was extended for the new node, and whole-blueprint searches for completion, completeness, complete modulo, J-adically complete, nilpotent and adic completeness found no duplicate of the new criterion.

## Not duplicates

lem-sfb-two-ideal-adic-completeness vs lem-sfb-adic-completion-flat-deformation-functor: the new statement is the general two-ideal completeness criterion for a Noetherian ring, without an Artinian base, flatness, marking or deformation functor; the item uses it only after separately establishing all those properties.

lem-sfb-two-ideal-adic-completeness vs lem-sfb-isolated-affine-completion-deformation: the latter concerns smoothness and tangent spaces of a deformation functor for finitely many isolated points, not completeness for two ideals.

lem-sfb-two-ideal-adic-completeness vs lem-weil-pbc-power-series-complete-over-complete-base: that node concerns a power-series ring and its combined coefficient/variable ideal; its searches mention 0DYC as an alternative route, but its statement does not give the general two-ideal criterion.

The 05GH node lem-weil-pbc-completion-noetherian-quotient-noetherian is reused, not duplicated: it already proves Noetherianity of completion under a finitely generated ideal and Noetherian quotient, including the nilpotent-ideal case needed here. Likewise existing 0316, 05GG, 00MB, 00MA, Artinian nilpotence, flat base change and composition nodes are reused.

## Review by N9

I read examples-defos.tex Tag 0DYV (lemma-completion), including its proof at lines 1103–1122, and algebra.tex Tag 0DYC (lemma-complete-modulo-nilpotent), both statement and proof at lines 23215–23242. I checked the tags against tags/tags. For the sole new node I copied the full two-ideal criterion: R must be Noetherian, R must be I-complete, and R/I must be complete for the image of J; the conclusion is J-completeness of R. Its proof remains deferred as a statement-only node. It is more general than completeness of a deformation, so the split does not merely rename a clause of the item. Its source proof uses completion along I+J, finite generation over the complete ring, Nakayama and faithful flatness; these are future work under the new node, not assumptions concealed in the item's steps.

For step 1 I opened and read the statements of Artinian-local-noetherian-nilpotent, completion-noetherian-quotient-noetherian, adic-completion-noetherian, adic-completion-mod-ideal, noetherian-completion-flat and flat-ring-map-comp. The first supplies both finite generation of m_A (Noetherianity) and nilpotence; the second accepts the non-Noetherian ring Q before Noetherianity has been proved, since Q/H=B is Noetherian and H is finitely generated. The stabilization Q/H^n=Q makes its completion canonically Q. Only after this deduction do the Noetherian completion and flatness lemmas apply to J_Q. The completeness leaf requires finite generation of J_Q, now supplied by Q Noetherian. Flat composition has both maps flat. I also read the actual source of 05GH and its upstream declaration; no stronger property was taken from it.

For step 2 I read the full statement of completion-finite-module-tensor, including naturality and the formula for its canonical map. B=Q/H is cyclic, hence finite as a Q-module, with the correct induced J-adic filtration. Its bijection is the desired reduction map, and the displayed component formula verifies multiplicativity, the unit and the marking. Tensor associativity here is the elementary balancing identification of the two quotient tensor products.

For step 3 I verified the Artinian node applies to any C in Art_k. Successively expanding coefficients modulo m_C and stopping at m_C^N=0 gives the explicit finite monomial spanning set, including the case m_C=0. Thus A1 is finite over A for every allowed base map. The flat-module-base-change statement was read and gives the flatness of Q1 over A1, not flatness of A1 over A; no such hypothesis is needed. The residue-field compatibility in Art_k identifies the special fibre with B.

For step 4 the only external input is nilpotence from the Artinian node, used on A1. The calculation K=L+H1 follows from their images modulo H1. Expansion proves the two power inclusions, and I wrote the actual maps between quotient limits and their inverse, rather than citing a comparison theorem not present in a node. This step is elementary from that input and definitions.

For step 5 the finite-module completion statement again supplies exactly the comparison and its naturality, with Q1 finite by step 3. I checked its hypotheses with ring Q and ideal J_Q. The cofinality comparison converts completion along L to completion along K. The quotient formulas verify algebra structures, arrow functoriality, compatibility with the special-fibre marking, identity and composition of base maps. These formulas are not an appeal to an unnamed tensor/limit theorem.

For step 6 I checked all three hypotheses of the new node: Q is Noetherian by step 1, H-complete by stabilization, and Q/H=B is complete for the image J of J_Q by the additional hypothesis. For step 7 the finite geometric series explicitly lifts an inverse modulo H. The quotient by J_Q is a field, and everything outside J_Q is a unit; this proves locality and identifies the maximal ideal. Its completeness depends on step 6, so the phrase "if also" is read together with B being complete, as in the item.

I tested J=0 (J_Q=H is nilpotent and completion is Q), J=B (completion is the zero ring, a flat algebra), A=k (the original completion), B=0 (Q=H and nilpotence forces Q=0), and B local with J its maximal ideal. For the new criterion, I=0 gives precisely its assumed J-completeness; J=0 gives the discrete complete ring; I=R forces the zero ring; J=R forces R/I=0 and then R=0 by I-completeness, so no exception is hidden. The Noetherian hypothesis was not removed. There are no non-elementary steps over 2000 characters and no inline standard lemma left unnamed. I checked B–E of delivery-errors.md against the JSON: the new node has no proof, every notion is defined inline or by its cited definition, sources have verified tags and labels, statements rather than proofs of nodes are used, and citation quotes are verbatim. No SGA source is used.

## Unfinished work

None for this one-level split. The sole new statement remains unsplit as required and will receive its own future worker.
