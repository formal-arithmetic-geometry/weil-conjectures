# lem-trf-tame-root-envelope — N0

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tame-root-envelope.json`: statement, status split; 11 proof steps using 20 existing nodes. Not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for every (step, cited node) pair.
- `report.md`: this report. `searches.jsonl` records the actual search-command responses; `write_split.py` is sandbox-only scratch work.

No new nodes and no new Mathlib leaves. The original statement, source record, statement dependencies, creation record and blueprint ancestry are retained. The item has no existing proof or sandbox report to recover. No released repair note exists.

## Attachments

None. Searches for the exact blueprint tag and the tame radical-envelope notion under `lean/WeilConjectures/` found no declaration covering the item. The DVR root-normalization files have additional discreteness hypotheses and different conclusions.

## Wanted literature

WANTED: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, section 2.1, especially Lemma 2.1.5 and the preceding ramification discussion, for lem-trf-tame-root-envelope. The source record's local PDF does not exist. I read the primary text at https://arxiv.org/html/0707.3953v3 .

WANTED: Gabber–Ramero, *Almost ring theory*, sixth release, arXiv:math/0201175v3, Corollary 6.2.14, Definition 6.2.16 and paragraphs 6.2.17–6.2.18, printed pp.161–162, for lem-trf-tame-root-envelope. I read https://arxiv.org/pdf/math/0201175v3 . The similarly titled author-hosted releaseLNM.pdf has different pagination (the published book); the arXiv v3 is the source matching the item's references.

No literature was downloaded or written to the shared repository. The proof is explicitly marked agent-written. It supplies a direct finite construction in place of leaving descent from the strict henselization implicit.

## Errors and changes

No statement dispute was found. In particular, the field may have nondiscrete value group and imperfect residue field. I did not replace it by a DVR theorem. No hypotheses or conclusions were changed.

The item was statement-only. Its parent `lem-trf-valued-finite-ramification-calculus` cites this item for tame base change, so invoking the parent's general permanence assertions here would be circular. Instead step 2 proves the necessary tower arithmetic explicitly, and the reverse implication uses the existing graded wild-kernel theorem, not the parent.

The finite root construction is substantive: the chosen elements of L initially have powers equal to a ground-field element times a unit. Adjoining residue roots in a finite etale extension and lifting in the compositum removes those units. The proof writes the equations and then bounds the dimension of the compositum from above and the radical field from below. It never assumes tame stability under base change while proving that stability's input.

The common source reference for a general tame radical description is not applied as though its separably closed residue hypothesis held over K. Our finite residue enlargement replaces that hypothesis for the finitely many roots actually used.

## Searches and reuse

I retained the original four Mathlib search records and read the fresh responses in `searches.jsonl`. Searches made through msearch.py in this sandbox were: LeanFinder for the complete-valued-field tame envelope; LeanSearch with a second henselian/radical phrasing; Loogle `IsKummerExtension` (unknown identifier, no hit); grep for `finrank.*dvd|dvd.*finrank|isGalois` in FieldTheory/KummerExtension (no hit at that directory argument); grep for `[Tt]ame|defectless|[Uu]nramified` in RingTheory/Valuation (no hits); and LeanFinder for the one-root cyclic Galois degree statement. The last search finds KummerExtension declarations, whose source I inspected: the named Galois/cyclic statements require irreducibility and primitive roots. They do not give this valued-field equivalence in one line. The existing `lem-sfb-multiradical-galois-degree` already states exactly the algebraic input required, including reducible binomials, so it is reused rather than re-created.

I searched the whole DAG by tame, unramified, residue extension, henselian valuation, radical, Kummer and the relevant source references. `tools/blueprint_refs.py search` was run for tame, strict hensel, Kummer, radical, ramification and finite etale, and `ancestor` confirms lem-trf-local-term-locality. No blueprint node states this equivalence. The matched transverse-tame local constancy and DVR nodes have different objects and hypotheses. The current blueprint ancestor's proof (1)–(2), chapter and unit records were read. This technical input stays below the unit's nearby-cycle/alteration branch and does not modify the geometric route.

## Not duplicates

No new node pairs: all twenty inputs are existing nodes. In particular, the finite-etale field lift, its map-lifting bijection, valuation local factors, Hensel lifting and multiradical Galois degree are cited in their existing forms.

## Review by N0

I read delivery-errors B–E against the unchanged statement and each proof step, and read the statement of every cited node. I checked Temkin's numerical tame criterion and Gabber–Ramero's prime-to-residue-characteristic radical calculation online. Locally I read Stacks algebra.tex, Tags 04GK (lemma-henselian-cat-finite-etale) and 04GG (lemma-characterize-henselian), and fields.tex, Tag 09I6 (section-Kummer, opening paragraph). There are no new-node sources to audit.

Step 1 uses the spectral-norm node for existence of an extending norm, absolute-value uniqueness for compatibility, finite-dimensional completeness for each finite field and the completion-factors statement specifically for henselianity of the complete valuation ring. The last node is applied to the identity finite separable extension; completeness identifies the completion with the original field. Algebraic-closure existence and the extension-of-embeddings theorem justify the common algebraic overfield; neither is smuggled in as a definition.

Step 2 uses the fundamental inequality to obtain positive finite e and f and d at least one. It writes out coset and basis multiplication to derive the tower formula. It uses separable permanence only for transitivity in a tower, exactly as that node states. Subextension separability is checked directly from the elementwise minimal-polynomial definition. No integrality of d or defect p-power theorem is needed to descend defectlessness.

Step 3 uses primitive-element existence for the given finite separable residue extension, the finite-etale field-lift statement for a residue realization, and the valuation-etale-factor statement for the valuation ring, fraction-field degree and the actual polynomial g with simple residue root. Hensel root lifting in L constructs the embedding. This uses L's completeness, not separability of L/K, which is not assumed in the item. Absolute-value uniqueness identifies the two valuation rings. The fundamental inequality then forces e(V/K)=1. I checked that the etale-factor node states the polynomial and rank conclusions, rather than taking them from its proof.

Step 4 is the finite group calculation on the actual value quotient. The positive orders n_i divide e and hence are invertible in every residue field at issue. The a_i are chosen by equality of values in Gamma_V, and u_i is an actual unit; no assertion is made that an arbitrary t_i already has its power in V.

Step 5 uses algebraic-closure existence and finite algebraic generation to construct the single finite field k'. The derivative computation proves that each root adjoined is separable; the simple-separable-extension and separable-permanence nodes give separability of the field towers. This verifies the hypothesis of the finite-etale field lift used next. None of these steps requires the original residue field to be perfect.

Step 6 applies the same finite-etale field lift and valuation local-factor statements over K itself, not merely over V. This makes U's valuation ring finite etale over K's without needing an uncited composition theorem. The finite-etale map-bijection statement applies because both V's and U's valuation rings are finite etale over K's. Its residue map lifts to an injective map of fraction fields. The algebraic embedding extension theorem puts U and L in a common overfield over the already embedded V. Norm uniqueness makes the maps isometric. Degree equals residue degree and the fundamental inequality imply Gamma_U=Gamma_V=Gamma_K.

Step 7 applies exactly the monic/simple-residue-root clause of the Hensel lemma, first in H and then in U. The displayed derivative is nonzero and the lifted z_i are units. The equations alpha_i=t_i/z_i and alpha_i^n_i=a_i are checked explicitly. For roots of unity, the separable-polynomial root-count statement gives n_i distinct residue roots; their distinct lifts exhaust the degree-n_i polynomial. Thus the actual U in the conclusion contains all required roots of unity.

Step 8 uses the fundamental inequality for the lower degree bound, with distinct cosets preserved because Gamma_U=Gamma_V. For the upper bound, the U-span of a V-basis of L is a finite-dimensional domain and a subalgebra; the cited finite-dimensional-domain statement makes that very span a field. Therefore it equals LU. Comparing dimensions gives the equality R=LU and the required embedding, rather than merely a map from some abstract root algebra.

Step 9 applies the valuation local-factor statement to U's already-local valuation ring, yielding its residue separability and degree equality, and the fundamental inequality supplies e=1. In each one-root extension the existing multiradical Galois-degree statement is applied with r=1 and n=n_i. Its hypotheses are exactly a_i nonzero, n_i invertible and all n_i-th roots of unity in the base. Its statement supplies both Galoisness and degree dividing n_i, even when the displayed binomial is reducible.

Step 10 applies the graded wild-kernel theorem only to those finite Galois extensions of complete fields. The finite-Galois fixed-field node supplies |Gal|=[R_i:R_(i-1)], so its p-subgroup must be trivial when the degree is prime to p. The wild-kernel node's stated fixed-field conclusion then supplies every numerical and residue clause. In residue characteristic zero it explicitly states that the subgroup is trivial. I checked that this input has no dependency on the parent ramification-calculus node.

Step 11 uses only the earlier tower bookkeeping, the fundamental inequality and the stated separability transitivity. The lower extension's residue separability is a restriction to its elements. The defect equality for the composite and two lower bounds force equality for L; no normality of L/K or perfection of its residue field is introduced.

I tested the identity extension, the empty radical list, e=1 with arbitrary finite separable residue degree (including degree divisible by p), n_i=1, a_i already an n_i-th power, residue characteristic zero, and a nondiscrete value group. A nontrivial immediate defect extension in positive residue characteristic cannot pass (a), and cannot enter the radical construction because the final degree comparison would force it trivial. In a purely inseparable extension (a) can hold only in the trivial case, consistently with the direct proof. No step exceeds 2000 characters or conceals a separate classification assertion. There is no new statement to weaken or repackage as one of the item's own clauses. No SGA source is used.

The cross-unit inputs listed in split_report.tool_uses are generic field theory, Kummer theory and henselian/etale algebra tools; they do not replace any step of the fixed geometric unit route. Top-level tool_uses is untouched.

## Unfinished work

None for this stage-1 split. The independent maintainer reviews the proof after delivery. Local archival copies requested above remain a literature-maintenance task.
