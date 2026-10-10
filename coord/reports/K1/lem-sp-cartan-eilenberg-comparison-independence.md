1. Files written:

   - `dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-comparison-homotopy.json`: statement-only auxiliary lemma, Mathlib searches no match.
   - `dag/nodes/sec-abelian-varieties/lem-sp-filtered-homotopy-spectral-sequence.json`: statement-only auxiliary lemma, Mathlib searches no match.
   - `dag/nodes/sec-abelian-varieties/lem-sp-cartan-eilenberg-comparison-independence.json`: four-step split, Mathlib searches no match.
   - `citations.json`: verbatim statement citations for every proof dependency.

2. Attachments: none.

3. WANTED: none.

4. Problems found: the imported item had no proof and its source paragraph only said that the construction was functorial. I retained its mathematical statement and made the hidden comparison-homotopy and filtered-spectral-sequence invariance explicit as two new statement-only nodes. I checked the whole DAG and blueprint for those statements; neither is duplicated. The item must not cite `thm-sp-grothendieck` itself because that theorem cites this item, so the final step uses the independent double-complex spectral-sequence, Cartan--Eilenberg, and derived-functor statements instead.

## Review by K1

I read the item, `thm-sp-grothendieck.json`, `lem-sp-cartan-eilenberg-exists.json`, `lem-weil-pbc-cartesian-eilenberg-functorial.json`, `thm-sp-double-complex-spectral-sequences.json`, `def-sp-double-complex-total.json`, `def-sp-filtration.json`, `def-sp-convergence.json`, and `def-sp-left-exact-additive.json`. Step 1 uses the existence statement for the columns and the boundary/cycle/cohomology resolution pieces, the functorial CE-lift statement for the augmentation equation, and the total-complex definition for preservation of the resolution-degree filtration. Step 2 uses the new homotopy node and checks its hypotheses against exactly those CE resolution clauses and the common lifted map. Step 3 uses the new filtered-homotopy node; the filtration and convergence citations state the filtered-complex and abutment structures it acts on. Step 4 uses the existing functoriality of the two double-complex spectral sequences, the CE row properties, and the definition of right derived functors to identify the page and abutment maps; identity and composition follow directly from the augmentation equation and composition of double-complex morphisms.

For edge cases, I checked an identity morphism (the identity CE map gives the identity on every page), a zero morphism (both comparison maps are nullhomotopic over zero), and a complex concentrated in degree zero (the statement reduces to ordinary injective-resolution comparison and its cohomology map). I also checked that no proof step cites the ancestor Grothendieck theorem, avoiding a dependency cycle. The Mathlib searches were run for the item and both new nodes with LeanFinder, Loogle, grep, and unavailable LeanSearch; only single-resolution homotopy declarations appeared, so all three nodes remain non-Mathlib statements.

5. What I could not finish: nothing before the required dry run.

## Not duplicates

lem-sp-cartan-eilenberg-comparison-homotopy vs lem-sp-cartan-eilenberg-comparison-independence: the new node states filtered chain-homotopy uniqueness of two CE comparison lifts, while the item states equality of spectral-sequence maps, composition, and page/abutment compatibility.
lem-sp-cartan-eilenberg-comparison-homotopy vs lem-sp-cartan-eilenberg-properties: the new node compares two morphisms of CE double complexes, while the existing node states structural injectivity and resolution properties of one CE resolution.
lem-sp-cartan-eilenberg-comparison-homotopy vs lem-sp-cart-eilenberg-left-exact-cohomology: the new node gives homotopy uniqueness of comparison lifts, while the existing node states that a left exact functor commutes with cohomology for a CE row.
lem-sp-cartan-eilenberg-comparison-homotopy vs lem-sp-cartan-eilenberg-exists: the new node is a uniqueness/comparison statement for two already-given CE resolutions, while the existing node is an existence theorem.
lem-sp-cartan-eilenberg-comparison-homotopy vs lem-weil-pbc-cartesian-eilenberg-functorial: the new node compares two lifts and proves they are homotopic, while the existing node only constructs one lift for a given complex map.
lem-sp-cartan-eilenberg-comparison-homotopy vs lem-weil-pbc-horseshoe-morphism-lift-exact-source: the new node assembles compatible row homotopies for CE double complexes, while the existing node gives a middle chain map for one short exact sequence of resolutions.

## Second reading by K1

Repair review: I corrected the two defects identified by reviewer R-cci2340. The comparison-homotopy node now requires a homotopy that shifts the resolution filtration from $F^q$ to $F^{q-1}$, and the filtered spectral-sequence node has the same one-step-shift hypothesis, so its conclusion starts at $E_2$. Step 2 now cites `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` for the fact that independently chosen injective-resolution lifts of $f$ are homotopic, then applies the CE homotopy node to homotopic underlying maps. The CE homotopy node now lists `lem-sp-cartan-eilenberg-exists` in `stmt_deps`.

I also repaired the indexing convention: Step 1 explicitly says that the existence node uses columns $I^{p,\bullet}$ resolving $K^p$, while the functoriality node transposes to $C^{p,q}=I^{q,p}$, making its second-degree filtration the resolution-degree filtration used here. The homotopy statement now assumes $K^p=L^p=0$ for $p<0$, as required by the existence node, rather than merely saying bounded below. The citations file was updated with verbatim quotes for the new lift-uniqueness and one-step filtration statements, and the split report records the additional off-unit tool use.

- Step 1 checked against Stacks Tags 015H, 015I, and 015K and the cited CE construction, lift, and total-complex statements; verdict: the filtered comparison map is constructed with the identity exact functor made explicit.
- Step 2 checked against the exact-functor specialization of the CE comparison-lift statement and the row clauses of `lem-sp-cartan-eilenberg-exists`; verdict: corrected to apply the homotopy node to the identity functor on the target category and the two $F(J_\bullet)$ complexes.
- Step 3 checked against the first-quadrant CE bounds, the filtered-complex construction in homology.tex, and convergence; verdict: boundedness and the abutment-filtration conclusion are now stated explicitly.
- Step 4 checked against functoriality of the double-complex spectral sequences, the CE row properties, and the derived-functor definition; verdict: identity and composition compare compatible and independently chosen lifts via Steps 2--3, so no unsupported direct composition is used.
- New node `lem-sp-cartan-eilenberg-comparison-homotopy` checked against Definition 015H, Lemma 015I, and Remark 015K; verdict: repaired to name both abelian categories, enough injectives, augmentations, and compatible row homotopies.
- New node `lem-sp-filtered-homotopy-spectral-sequence` checked against homology.tex filtered-complex spectral-sequence functoriality and the homotopy definitions; verdict: repaired to define bounded filtrations and a filtration-preserving chain homotopy, with the exact $E_r$ and abutment conclusion.

Changes made: tightened both auxiliary statements for self-contained hypotheses and exact TeX; repaired Step 2's functor specialization, Step 3's boundedness justification, and Step 4's identity/composition argument; updated verbatim citations accordingly. Small cases checked: identity and zero maps, a complex concentrated in degree zero, and the zero complex; all reduce to the stated homotopy or identity conclusions.

Additional second-reading repairs: replaced the homotopy node's undefined row-homotopy assertion by the total-complex homotopy equation actually used in Step 2, updated its citation quote, and recorded exact Stacks labels 012O and 012U for the filtered spectral-sequence source.
