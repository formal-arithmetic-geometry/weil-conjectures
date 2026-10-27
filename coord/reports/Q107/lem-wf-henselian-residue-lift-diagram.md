# Q107 stage-1 delivery: lem-wf-henselian-residue-lift-diagram

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-wf-henselian-residue-lift-diagram.json: statement, split into seven steps; no exact Mathlib match for the whole item.
- citations.json: one verbatim statement quotation for each node used in each step.
- report.md: this report. searches.jsonl retains the actual search-command results.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written or compiled.

## Attachments

None. Searched WeilConjectures for the blueprint tag, henselian finite-algebra equivalences, residue diagrams and Galois cofinality. The project has related henselian and pointed-etale-triple results, but no declaration found supplies every clause of this item. The upstream separable-closure declaration covers only the finite-subextension assertion, not this item.

## WANTED

None: all sources used are present locally.

## Findings and changes

The imported item had a statement but no proof or dependencies. Its statement is retained verbatim. Reused existing DAG nodes rather than creating variants of Tag 04GK, maximal-ideal contraction, finite Galois enclosure or colimit existence. The inherited ancestor/via chain is retained, with its place made specific to the current blueprint text. There is no statement dispute and no unit-route change. The finite-field and full-faithfulness lemmas from the proper-base-change unit are generic tools; their uses are declared in split_report.tool_uses.

Read the current ancestor proof in literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-i-real-boundary/lem-wf-boundary-stalk-invariants.proof.md, especially the finite-level strict henselian trait and the final Frobenius-equivariance paragraph. This item supplies the finite-lift diagram below that argument, not its sheaf-theoretic conclusion.

The whole-item searches were made through msearch.py with LeanSearch, two distinct LeanFinder phrasings, Loogle and source grep. Read their actual returned types and the relevant Mathlib source: HenselianLocalRing.TFAE is a root-lifting equivalence; StandardEtalePair.homEquiv and StandardEtalePresentation.lift_bijective concern a chosen standard-etale presentation; the etale-over-field product theorem is over a field. None is the coherent finite lift system and Galois cocone assertion. The inherited earlier search records were preserved and the new logged searches appended.

## Review by Q107

I read Stacks algebra.tex Tag 0BSL (remark-construct-sh-from-h) and the statement and proof of Tag 04GK (lemma-henselian-cat-finite-etale). The former gives precisely the intended finite local lifts and residue-compatible arrows; the latter supplies essential surjectivity and full faithfulness. I also read fields.tex Tags 09DT (lemma-normal-closure), 0BMG (lemma-normal-closure-inside-normal), and 0EXM (lemma-normal-closure-galois). These justify taking normal closures inside the specified separable closure, rather than replacing an intermediate field by an abstract unrelated extension. I corrected my draft tag for lemma-normal-closure-inside-normal to 0BMG after consulting the local tag table. Colimit existence follows the existing commutative-algebra colimit node, whose source is algebra.tex Section 07N7 and Lemma 00D6; its explicit directed-colimit construction and the colimit definition were read as well.

For step 1 I opened lem-weil-pbc-henselian-finite-etale-field-lift: its statement assumes a henselian local base and a finite separable residue extension and supplies the finite etale lift with the tensor fibre identification. Those hypotheses hold for every e. The two explicit inverse maps identify that tensor fibre with the quotient in this item's statement. Smallness is proved using subsets of the fixed field K, before choosing lifts over this set.

For step 2 I opened lem-weil-pbc-finite-algebra-local-radical. It really says every maximal ideal contains the extended base maximal ideal for a module-finite algebra over a local ring. Since the quotient here is the nonzero field e, that extended ideal is already maximal and is the only maximal ideal. The residue inclusion then gives the localness of the base map. I did not assume that a finite algebra with some chosen residue point is automatically local.

For steps 3 and 4 I opened lem-weil-pbc-henselian-finite-etale-map-bijective. Its statement is a bijection on all algebra homomorphisms between finite etale algebras over the same henselian local base, so both the arrows and the lifts of inverse residue isomorphisms are in its scope. Step 3 checks locality by the kernel of the injective residue inclusion. Step 4 computes reductions of identities and composites and invokes injectivity; lifting in both directions proves that the unique residue-compatible map between two lifts is an isomorphism.

For step 5 I opened lem-weil-pbc-separable-closure-exists-galois, whose second clause applies to any specified separable closure, and lem-weil-pbc-finite-set-in-finite-galois-subextension, whose ambient extension must be Galois. The first node supplies that missing hypothesis for K/k. Taking the finite union of bases of e and f then produces an actual intermediate finite Galois field containing both; containing a basis implies containing its whole k-linear span. This proves directedness and cofinality together and also proves directedness above any fixed e.

For step 6 I opened def-weil-pbc-category-colimit and used its actual cocone condition. The proof gives the extension formula a_e=a_g u_eg, checks independence using a common Galois upper bound, checks every transition, checks restriction, and proves uniqueness. Thus no general final-functor theorem or hidden comparison lemma is being assumed. This is the elementary argument specific to a directed cofinal subposet.

For step 7 I opened lem-weil-pbc-commutative-algebras-colimits-exist and checked its smallness hypothesis, already established in step 1, and its category, commutative H-algebras. The colimit definition then identifies the restricted universal cocone. The proof explicitly writes the compatible maps rho_e into K and checks that the comparison respects them, as well as the H-structure. It never substitutes a statement about just underlying sets for the algebra universal property.

I checked small cases: H a field (m=0), e=k, repeated inclusions e=f, K=k when k is separably closed, and an arbitrary target algebra T including the zero ring. All formulas still hold; J is nonempty because k/k is finite Galois, and the residue e is always a nonzero field. No Noetherian, domain, completeness, finite-residue-field or characteristic assumption was used. Each step is under 1000 characters, and none hides a separate non-elementary subclaim. All non-elementary inputs are the statements quoted in citations.json. No node was added that is elementary, a duplicate or a clause renamed as a lemma. No SGA source is used.

## Not duplicates

No new nodes. The existing field-lift and Hom-bijection nodes are reused separately; no new copy of the henselian finite etale equivalence is introduced. The existing finite-subset Galois-enclosure node is used with finite bases rather than creating a new cofinality lemma.

## Unfinished work

None in this one-level split. Independent maintainer review remains the project's normal next stage.
