## Worker report

Item: lem-finrepair-composition-c. Stage 1 only; no Lean files written and no compiler or Lake invoked.

Files written: dag/nodes/sec-smooth-purity/lem-finrepair-composition-c.json, citations.json, report.md. New nodes: none. Mathlib leaves: none. The item statement is unchanged. Its single imported paragraph is expanded into four proof steps. No attachments, no WANTED sources, and nothing unfinished in this one-level split.

I read the chapter sec-smooth-purity and unit sk-prop-sf-cbc. This is not the unit's key statement, so no unit realization fields are changed. The split follows the item's prescribed relative-Leray/constructible-Serre argument; the two off-unit statements are declared as generic tools in split_report.tool_uses.

Attachment search: the exact blueprint id and finrepair were absent from WeilConjectures in the read-only slopmaster2 source and from dag/lean_names_upstream.json. Searches for constructibility preservation and composition found derived-finiteness statements, but none states this conditional degreewise composition assertion. In particular SixFunctors/Etale/Derived/Stability/DirectImage.lean's boundedConstructible_rightDerivedLowerStar_of_finite concerns bounded complexes and uses the stronger finiteness theorem, rather than stating this item. Master source was treated only as reference material.

Mathlib searches were all made through msearch.py and are recorded verbatim in the node and searches.jsonl. The first LeanFinder phrasing returned underived sheaf-pushforward composition (including Scheme.Modules.pushforwardComp), not higher direct images. The second phrasing returned topological constructibility and Grothendieck-abelian/derived-category infrastructure, not the assertion. LeanSearch was unavailable (HTTP Internal Server Error). The first Loogle query used an unknown identifier and is explicitly recorded as invalid; the repaired query returned constructible subsets of topological spaces, not constructible sheaves. The source grep found zero hits. No false claim of Mathlib absence based on the unavailable service is made.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for composition and constructibility found the item itself and unrelated finite-pushforward lemmas. The existing lem-weil-pbc-grothendieck-spectral-sequence and thm-constructible-serre already supply every non-elementary fact, so no node for spectral-sequence stability, image closure or finite-filtration induction is created.

## Review by NV

I read the item's master blueprint file, the coefficient/property-C definition, and the complete statements of lem-weil-pbc-grothendieck-spectral-sequence and thm-constructible-serre. I checked the sources in the local Stacks files: sites-cohomology.tex Tag 0734 (lemma-relative-Leray), derived.tex Tag 015N (lemma-grothendieck-spectral-sequence), and etale-cohomology.tex Tag 03RZ (lemma-constructible-abelian). The tags-to-label mapping confirms these labels. The item is the composition consequence of these results; Stacks does not state this predicate by name, hence proof_origin stays agent, as for the blueprint.

Step 1 uses exactly def-finrepair-property-c: the first quantifier applies to F and yields a constructible sheaf on Y; the second then applies to that sheaf for every nonnegative a. This substitution is elementary. The schemes and finite commutative coefficient ring remain those of that definition; in particular I have not changed to pro-etale or discrete non-torsion coefficients.

Step 2 uses the statement of lem-weil-pbc-grothendieck-spectral-sequence, not its proof. I checked that it covers Lambda-module sheaves, arbitrary scheme morphisms, arbitrary F, the first-quadrant page formula, the bidegree, and the finite filtration with the precise associated-graded isomorphisms. Thus no hypothesis that f_*F is g_*-acyclic is silently inserted, and no uniform vanishing hypothesis is needed.

Step 3 uses the kernel and cokernel clauses of thm-constructible-serre, and the square-zero/page-cohomology clause of the spectral-sequence statement. The induction is simultaneous for every bidegree, so both the incoming source and outgoing target are available in the induction hypothesis. The incoming differential factors through the kernel because its composite with the outgoing differential is zero; its cokernel there is precisely page cohomology. This avoids the false shortcut that an arbitrary subsheaf of a constructible sheaf must be constructible. The finite commutative ring hypothesis of the closure node holds; the Stacks Noetherian-ring hypothesis holds since a finite ring has only finitely many ideals. Terms outside the quadrant are zero, and zero is finite locally constant on the one-stratum partition. Constructibility is invariant under isomorphism directly from that definition.

Step 4 uses the explicit stabilization and filtration clauses in the spectral-sequence node, and the extension clause of thm-constructible-serre. For each (p,n-p) I use r > max(p,n-p+1); this is exactly the cited bound, not an invented global bound. The finite filtration has F^(n+1)=0 and F^0=H^n; each quotient is the previously established constructible stable term. The descending induction has a stated base and actual short exact sequences, so it proves the abutment rather than merely calling it constructible. The final universal quantifiers are the definition of property C.

Edge cases checked: n=0 has a single graded quotient and the base F^1=0; n=1 has two successive extensions and the same stabilization bounds apply. F=0 and empty schemes have zero pages and abutments, so the argument still works. Identity morphisms also fit the same argument. The proof works without any degree bound uniform in F, f or g. No statement dispute or source correction was necessary.

Against B--E: there are no new nodes that could be non-self-contained, duplicate, merely a clause of the item or an unsearched Mathlib leaf. All imported metadata is retained; proof_deps is the exact union of uses. Every step has a source and every used statement is backed by a verbatim quote in citations.json. The repair to the imported proof is its explicit two inductions and the kernel-factorization calculation; no argument is hidden behind 'stabilizes' or 'extensions'. The only off-unit edges are the original blueprint's generic tools, with their purpose stated above. Independent second reading remains for the next worker.


## Second reading by NV

Item statement: compared verbatim with lem-finrepair-composition-c.md and expanded its predicate using def-finrepair-property-c and sbc-def-coefficient-conventions; PASS, finite commutative coefficients with invertible annihilator and the same scheme domain, no vanishing hypothesis added.

Step 1: checked the two universal quantifiers of def-finrepair-property-c against the blueprint proof's first sentence; PASS, the intermediate sheaf is a permissible input to the second hypothesis, and this substitution is elementary.

Step 2: checked the full statement of lem-weil-pbc-grothendieck-spectral-sequence and sites-cohomology.tex Tag 0734, label lemma-relative-Leray, with derived.tex Tag 015N, label lemma-grothendieck-spectral-sequence; PASS, module-valued relative Leray applies to arbitrary scheme morphisms and the chosen sheaf, and explicitly supplies the needed filtration and page structure. No assertion is taken from the dependency's proof instead of its statement.

Step 3: checked thm-constructible-serre against etale-cohomology.tex Tag 03RZ, label lemma-constructible-abelian (3), and checked the page formula in the spectral-sequence node; PASS, finite Lambda is Noetherian (every ideal is a finite set and thus finitely generated), and both arguments of each kernel/cokernel are constructible by simultaneous page induction. The incoming differential lands in the kernel by square-zero. Zero and invariance under isomorphism follow from the explicit finite-local-constancy definition: restriction of an isomorphism preserves the same strata and constant finite modules.

Step 4: checked the stabilization bound and filtration clauses of lem-weil-pbc-grothendieck-spectral-sequence, the extension clause of thm-constructible-serre, and the quantifiers of def-finrepair-property-c; PASS, r > max(p,n-p+1) kills incoming and outgoing differentials and implies r >= 2. The base of descending induction is zero and each induction step is the displayed short exact sequence. For n=0 there is one quotient, for n=1 there are two; zero sheaves, the empty scheme (use the empty partition), and schemes over a field introduce no exception. No uniform degree bound is asserted.

New nodes: none; B1--B7 and node-by-node duplicate/Mathlib-leaf checks have no new statements to check. Independently searched the DAG for Tags 0734, 015N, 03RZ and inspected prop-weil-pbc-composition-stability: it concerns proper morphisms and injective acyclicity/base change, not property C. The existing relative-Leray and constructible-closure nodes suffice; the page and filtration inductions do not warrant new nodes.

Independent attachment/search check: searched the read-only slopmaster2 source and upstream name index for the item id, finrepair, and constructibility/composition vocabulary. Read SixFunctors/Etale/Derived/Stability/DirectImage.lean: its boundedConstructible_rightDerivedLowerStar statement has a different bounded-complex conclusion and a sorry proof, so supplies no finished attachment. The independent Loogle query "spectral", "sequence" returned 12 spectral-object kernel/cokernel short-complex declarations, not this item; its actual output remains in searches.jsonl and the verdict is now recorded on the item. No new Mathlib leaf is justified.

Changes:
- Retained the worker requests in split_report.tool_uses after checking tools/review_split.py lines 99--101: this is explicitly a permitted request field, distinct from the maintainer-owned top-level tool_uses. An initial dry run after removing the requests rejected both route edges; restoring them corrects that second-reader mistake. No maintainer authorization has been written. Both requested tools are prescribed by the blueprint and have no unit-local replacement.
- Added the independent Mathlib search record and this reading. All four mathematical steps and the item's statement were retained; all seven citations were checked against the complete current dependency statements and remain verbatim and applicable.

The first worker's Review by NV and its permitted generic-tool requests are preserved as requested. No statement dispute was found, and no Lean, compiler, Lake, live-project or live-launcher writes were performed.
