## Files written

- dag/nodes/sec-trace-formula/lem-trf-reduced-finite-type-field-product-embedding.json: existing statement split; no exact Mathlib match. Its statement, statement dependencies, provenance and previous searches are retained.
- citations.json: one verbatim statement quotation for every node cited by every proof step.
- report.md: this report. searches.jsonl contains the actual searches executed by the prescribed msearch command.

No new nodes; no new Mathlib leaves. All seven distinct proof dependencies already exist as Mathlib leaves. No Lean files were written and no compiler, Lake or build tool was run.

## Attachments

None. Searches of the live WeilConjectures source by the exact blueprint id and by reduced-Noetherian, product-of-fields, embedding and localization concepts found no completed declaration stating this entire item. The existing reduced_noetherian_total_ring_fractions theorem describes the total fraction ring, not the requested finite-type k-algebra embedding, and was not claimed as an attachment.

## WANTED

None. All mathematical sources needed for the split are present locally.

## Findings and changes

The item was unsplit, with an empty proof and no repair note. The statement is correct as written. I preserved in particular the zero algebra, empty product, arbitrary ground field, and lack of an integrality assumption. There is no STATEMENT-DISPUTED correction.

I read algebra.tex Tag 034N (lemma-geometrically-reduced-any-reduced-base-change), its reference to the finite product of fields, and the underlying proofs of 00EW (lemma-reduced-ring-sub-product-fields), 00EU (lemma-minimal-prime-reduced-ring), 00FR (lemma-Noetherian-irreducible-components), 00FN (lemma-Noetherian-permanence), and 00E0 (lemma-Zariski-topology, especially (4) and (7)). The proof expands the minimal-prime localization construction of 00EW directly. This is the same algebraic ingredient of 034N, with its scalar maps made explicit; it does not need a second total-fraction-ring decomposition argument.

The chapter and unit and the current main-20261015 ancestor lem-trf-local-term-locality were read. This item is an auxiliary algebra lemma reached through the recorded separable-constants chain, not the unit's key node; no unit realization or chapter route was altered. Blueprint ancestor and via are retained. Whole-DAG and blueprint searches for minimal primes, products of fields, reduced finite algebras and embeddings found no blueprint node with the full statement. Existing results were reused instead of creating helper nodes.

The previous node's seven Mathlib search records remain untouched. Fresh searches were executed with leanfinder, loogle, leansearch and grep, and another semantic phrasing was tried. Noether normalization's exists_finite_inj_algHom_of_fg and exists_integral_inj_algHom_of_fg were read at NoetherNormalization.lean:268–294: they embed a polynomial algebra into B, the opposite direction. PrimeSpectrum.toPiLocalization_injective was read at Spectrum/Maximal/Localization.lean:164–174: its product runs over all primes, so it neither supplies a finite indexing set nor field factors. The etale-field-product theorem requires etaleness, absent here. Thus the item needs the assembly proof, although its ingredients are already leaves.

## Unfinished work

None in the stage-1 split. The maintainer's independent review remains the acceptance step.

## Review by Q112

I checked the split against delivery-errors B–E with the node statements and Stacks text open. There are no new nodes to check for hidden proofs, duplicated clauses, missing notions or source tags. The item's statement introduces its algebra, reducedness and finite generation explicitly and cites the existing field and field-extension notions. No statement hypothesis was added or removed. Sources are cited by their actual labels and tags, rather than unstable section numbers. All proof uses have quotations in citations.json, and proof_deps is their union.

Step 1 is the elementary zero-ring case: the empty product and the zero algebra each have one element and their scalar maps agree. This avoids imposing nontriviality on B or incorrectly making the empty product a field.

Step 2 uses exactly the Noetherianity clause of lem-wf-affine-noetherian-components, whose entire hypothesis is a finitely generated commutative algebra over any field. I read both its statement and its original blueprint file; neither assumes an algebraically closed or perfect field or a domain. The finite-minimal-prime node then applies to this Noetherian B and explicitly states the finite set of prime ideals minimal among primes. This supplies the finite enumeration, not any assertion smuggled from the proof of that node. Both facts are already Mathlib leaves, so their off-unit use is permitted as a generic algebra tool without a route replacement.

Step 3 uses def-weil-pbc-localization-at-prime for the canonical maps and lem-weil-pbc-minimal-prime-reduced-localization-field for the field assertion. The latter explicitly assumes just commutativity, minimality and reducedness, all in force. The composite scalar map makes each field into a k-algebra, exactly the equivalent formulation of field extension stated in def-pc-field-extension. No claim that B itself is a field or domain occurs. This follows the 00EU and 00EW source construction.

Step 4 is only the coordinatewise definition of j and a written verification of scalar compatibility, multiplication, addition and the unit inherited from its component ring maps. It uses objects already constructed in Step 3; it hides no independent algebra lemma.

Step 5 uses the fraction equality explicitly given in the statement of def-weil-pbc-localization-at-prime. Equality b/1=0/1 produces an annihilating denominator s outside the prime. Primality then implies b belongs to that prime. I did not cite the localization definition as if it alone asserted global injectivity; the denominator calculation is written out, and is elementary from its quoted equivalence.

Step 6 uses the I=0 clause of lem-weil-pbc-prime-contains-minimal-prime for every prime of B, then the radical-as-intersection formula in lem-weil-pbc-zero-locus-eq-iff-radical-eq. Its hypotheses are only commutativity and an ideal. Reducedness is used only after obtaining the actual positive-power nilpotence of b. Subtracting equal images then proves injectivity. This expands the intersection argument of 00EW via the exact two parts of 00E0 it needs, rather than citing a definition for an existence theorem.

Small cases checked: B=0 gives t=0; B=k gives the single localization k; B=k×k gives two field factors with diagonal scalar map; B=k[x,y]/(xy) has two minimal primes, with fraction-field localizations and zero common kernel although it is not a domain. For the nonreduced excluded algebra k[epsilon]/(epsilon^2), epsilon survives in B but dies in the minimal-prime field localization, confirming that reducedness is essential. No perfection or separability is invoked. No step exceeds 2000 characters (the longest is 431), and the total proof text is under 3000 characters; there is no long-step lemma hidden in prose, relabelling of the item or new dependency cycle.
