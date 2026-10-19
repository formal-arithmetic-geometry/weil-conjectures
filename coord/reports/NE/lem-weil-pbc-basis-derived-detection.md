# Worker report

## Files written
- dag/nodes/sec-proper-base-change/lem-weil-pbc-basis-derived-detection.json: split item; no exact Mathlib match.
- citations.json: verbatim statements for every step citation.
- report.md: this report. No new nodes and no new Mathlib leaves.

## Attachments
None. Searched the item tag and derived-detection/basis/cohomology-sheafification concepts in WeilConjectures of the read-only slopmaster2 source, and consulted master as reference only. No project declaration states this pro-etale-basis result. The general Mathlib isomorphism criterion alone does not prove detection by derived evaluation.

## WANTED
None.

## Statement clarification and imported faults
STATEMENT-DISPUTED: the literal wording “a morphism between ... complexes ... is an isomorphism” is false in the category of complexes. For X=Spec(k) and R=Z, the nonzero contractible complex [R_X --id--> R_X] maps to zero with isomorphic derived sections everywhere, but is not isomorphic to the zero complex. The source proof explicitly says “ordinary derived category”, so the corrected wording states the morphism in D^+(Mod(R_X)). This is the intended derived assertion, not an extra acyclicity or constructibility hypothesis. The commutative ring R is unrestricted, as in the imported statement's def-weil-pbc-derived-categories dependency; it need not be finite. This item asserts neither a condensed-module theorem nor a completed-coefficient comparison.

Replaced the etale-only def-weil-pbc-derived-categories citation by the already existing pro-etale-site, abstract derived-category, module-sheaf and bounded-subcategory definitions. The original proof hid enough injectives, representation of a derived morphism by a chain map, the cone criterion, and the sheafification/basis inference. The new proof explicitly cites or derives them. No imported provenance or flags were removed.

## Unfinished work
None for this one-level split. Existing cited nodes remain their own tasks; no proof or review of those nodes is claimed here.

## Not duplicates
No new nodes. DAG and blueprint concept searches for sheafification, derived detection, injective representatives, and cone acyclicity led to reuse of the existing nodes. In particular, no 0BKV node was created: the kernel-image calculation is an elementary consequence of the existing exact sheafification theorem.

## Review by NE
I read the chapter and sk-thm-properbasechange unit, the item's master blueprint proof, the current statements of every citation (copied verbatim into citations.json), and the relevant Stacks source: derived.tex 013K, 070I, 070J, 05RT; sites-modules.tex lemma-sheafification-exact (03EI); and sites-cohomology.tex lemma-sheafification-cohomology (0BKV). The proof keeps the imported cone/injective/evaluation/sheafification/basis route. It is not the unit's key node, so no unit binding is changed.

Step 1 uses lem-pur-ringed-site-grothendieck-abelian precisely for Mod(R_X) on a small site, lem-sp-grothendieck-enough-injectives precisely for enough injectives, lem-weil-pbc-dplus-injective-representative for bounded-below injective representatives and their K-injectivity, and lem-weil-pbc-kinjective-hom-derived for a chain-map representative of the given derived morphism. The small skeleton and commutative coefficient hypotheses are explicit; no theorem about the etale site is applied to the pro-etale site. The Grothendieck theorem is a generic off-unit tool, recorded in split_report.tool_uses.

Step 2 uses the localization/restriction-injectives statement exactly for derived evaluation versus sections on W_proet. Injective terms in step 1 justify termwise computation and its functorial chain map. The existing general derived-plus-iso-on-cohomology theorem applies to R_X(W)-modules and gives all integer degrees, including negative degrees. Step 3 uses the displayed cone construction in the abstract derived-category definition and the generic cone-acyclic criterion, first in the section-module category. Evaluation commutes with the finite sum and matrix by the sectionwise construction; it is not assumed exact on sheaves. The cone criterion is a second generic off-unit tool, recorded in split_report.tool_uses.

Step 4 uses the ringed-site exact module sheafification theorem (not the definition of sheafification as if it implied exactness). Computing the presheaf kernel and image objectwise and then preserving their quotient is the explicit two-line calculation of 0BKV. The cone need not be injective for this calculation. The source of the reused exactness node lists 03CX/03CN/03CO; the actual exactness lemma in the local source is 03EI, and the step cites that correct tag without modifying the reused node. Crucially, cohomology sheaf sections are not identified with presheaf cohomology values.

Step 5 uses only the basis theorem's actual covering clause and the actual module-sheafification adjunction. To avoid silently using an unquoted equivalence or commutation theorem, I wrote out why every map from P_n into any sheaf is zero: restrict to a basis cover, then use sheaf separation. Applying the adjunction to identity and zero of P_n^# proves it is zero. This uses neither pro-etale geometric stalks nor an assumption that basis objects have no higher cohomology. Step 6 applies the same cone criterion in the sheaf category and the defining inversion property of localization. The transfer back to u is conjugation by the two chosen isomorphisms.

Checked B–E against these files: there are no new nodes, no unverifiable search claims, no hidden new clause nodes, no proof sketches masquerading as statements, and no uncited non-elementary inference. Every proof dependency is exactly a step citation. Searches were run through msearch.py; LeanSearch returned unavailable and is recorded that way. The second semantic phrasing found the general localization criterion, which is insufficient for the whole item. Small cases checked: zero objects and the zero ring give trivial detection; an empty scheme has only zero module sheaves by the empty-cover axiom; shifted single complexes and negative degrees are included. The contractible nonzero complex example diagnoses precisely why the original categorical ambiguity had to be corrected. No new mathematical statement was introduced for separate edge-case testing.

## Second reading by NE

- Statement: checked the affine $X$, unrestricted commutative $R$, chosen small pro-etale skeleton, module category, bounded-below derived category, basis, and derived evaluation clauses against the imported blueprint node and the definitions cited in the statement; the contractible-complex test confirms that the corrected $D^+$ formulation is necessary and faithful to the source's “ordinary derived category” intent.
- Step 1: checked the Grothendieck and enough-injectives hypotheses for the small ringed pro-etale site, and that the two representative complexes are bounded below and K-injective before invoking the chain-map representative; all four cited statements supply exactly these facts.
- Step 2: checked that restriction preserves injectives under the stated weakly etale basis map and that the derived-plus-isomorphism criterion applies in the section-module category; the conclusion is degreewise and includes negative degrees as required.
- Step 3: checked the cone terms and differential against the abstract derived-category definition, and that evaluation preserves the displayed finite sums and maps; cone acyclicity is applied only in the module category, with no hidden exactness claim.
- Step 4: checked the objectwise kernel/image calculation against exact module sheafification (03EI); it yields the sheafified presheaf cohomology, without identifying sheaf sections with presheaf values.
- Step 5: checked basis covers and sheaf separation from the basis lemma, then the sheafification adjunction; the argument that every map from $P_n$ is zero is explicit and does not assume basis acyclicity.
- Step 6: checked the cone criterion in the sheaf category and localization's inversion of quasi-isomorphisms; conjugation by the chosen representative isomorphisms gives precisely the stated $u$ conclusion.
- New nodes: none; there was therefore no new-node statement or Mathlib leaf to audit. Existing dependency nodes were read at their current statements and citations.json was checked for verbatim support.
- Changes made: filled the required blueprint ancestry and exact proof place, recorded the imported blueprint match in `same_as`, and retained the worker's corrected derived-category statement and six explicit proof steps.
