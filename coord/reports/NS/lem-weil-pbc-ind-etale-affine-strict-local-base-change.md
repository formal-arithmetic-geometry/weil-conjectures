## Worker report

Files written: dag/nodes/sec-proper-base-change/lem-weil-pbc-ind-etale-affine-strict-local-base-change.json — statement, split, no Mathlib match; report.md; citations.json; sandbox search logs and supporting script. No new node files.

Attachment candidate: Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing belongs to thm-weil-pbc-weak-etale-strict-local (existing dependency; transitive sorry audit left to the attachment checker).

WANTED: none.

Original faults: the item was unsplit with an empty proof. Its statement, statement dependencies and blueprint ancestry were sound. No unused statement dependency was removed and no statement changed.

Unfinished work: none in this one-level split. Existing cited nodes remain separate obligations; this report does not claim to have proved their open dependencies.

Item: lem-weil-pbc-ind-etale-affine-strict-local-base-change. Stage 1 only.

The unchanged statement is proved in four steps with zero new nodes and zero new Mathlib leaves. The original node had no proof. The split obtains isomorphisms H_A→H_B and H_C→H_D by ind-etale stability and Olivier's local theorem, then writes an inverse to the prescribed comparison using the second pullback projection. The proof is marked agent-written: this is the ind-etale specialization of 0GIP using the approach of 094Z, rather than a reproduction of 0GIP's more general quasi-finite filtered-colimit argument.

I read algebra.tex Tag 0GIP (lemma-base-change-strict-henselization-quasi-finite), including case (2) and its omitted residue-field detail; etale-cohomology.tex Tag 0GJS (lemma-locally-acyclic-quasi-finite-base-change), the displayed strict-local ring comparison; Tag 04HX (lemma-describe-etale-local-ring), the affine pointed-neighbourhood presentation; more-algebra.tex Tag 092Z (theorem-olivier); more-morphisms.tex Tag 094Z (lemma-weakly-etale-strictly-henselian-local-rings); and schemes.tex Tag 01I4 (lemma-fibre-product-affine-schemes). The explicit 0GIP construction takes relative separable closures in the ambient field, so the lack of algebraicity of Xi is intentional and correct. No statement dispute or source error was found.

The chapter and unit were read: sec-proper-base-change and sk-thm-properbasechange. The item's existing blueprint ancestry concerns the constructibility clause of thm-weil-pbc-direct-image-finiteness-proper via the strict-local input to 0GJU. No chapter or unit record changes. Blueprint searches for strict hensel, ind-etale, base change strict, strict-localization, and henselization.*base produced no equivalent blueprint statement; same_as remains []. The original from.place was already specific and is preserved.

## Existing material and searches

I searched project Lean by the exact item tag, strict henselization, strict localization, and related ind-etale notions. No declaration under WeilConjectures gives this item's entire comparison with both compatibilities. The source's IndWeaklyEtale.lean localization theorem concerns localization above a strictly henselian base, not the stated square. Master is reference material only; no master sorry declaration is treated as complete.

A potential attachment for an existing dependency, not this item: Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing belongs to thm-weil-pbc-weak-etale-strict-local, WeilConjectures/RingTheory/ProEtale/HenselianLocalRing.lean:245. I read its local-ring and local-hom hypotheses and its proof calling bijective_of_henselianLocalRing. This is reported for later audit, not certified transitively closed here, and that dependency file was not edited.

Mathlib searches were run through msearch.py and their full stdout is in the item's mathlib_searches. Two semantic phrasings found StandardEtalePair and etale base-change declarations, neither of which mentions strict henselization or proves the requested square. Loogle for StrictHenselization and the source grep returned no hits. LeanSearch returned Internal Server Error and is recorded unavailable. No candidate is promoted to a Mathlib leaf.

Whole-DAG source/tag and concept searches found the already existing affine spectrum fibre-product, strict-local functoriality, affine-chart ind-etaleness, ind-etale stability and Olivier nodes. They are reused. In particular the relative clause of lem-weil-pbc-ind-etale-stability already states that any A-algebra map between two ind-etale A-algebras is ind-etale; there is no need for a new strict-henselization-continuity lemma or a clause-restating base-change node.

## New nodes

None. Consequently B1–B9 and the new-node small-case and duplicate checks introduce no new obligations. All non-elementary arguments are applications of existing statements, not newly relabelled clauses.

## Not duplicates

No new nodes.

## Review by NS

I checked the unchanged statement against 0GIP case (2) and 0GJS's displayed comparison: the base maps are arbitrary ring maps with the sole ind-etale condition on B, the point is valued in one algebraically closed field, and the spectrum of the canonical ring comparison has the direction written in the item. The last compatibility clauses are consequences of that very comparison, not of an independently chosen isomorphism.

Step 1 uses lem-weil-pbc-fibre-product-affine-spectra for exactly the tensor-ring description and both projections, and lem-weil-pbc-strict-henselization-functoriality clauses 1–3 for the local rings, the local maps, residue inclusions and uniqueness. I checked that uniqueness applies to the composites: both are local, both agree on the original A-structure, and their residue maps are the same composed inclusion inside Xi. The remaining formation of the pair uses the universal property in def-pc-fibre-product. Those finite diagram checks justify elementary: true, after the cited statements have been applied.

Step 2 uses lem-weil-pbc-strict-henselization-affine-chart-ind-etale with S each of the four whole affine schemes, the identity affine-open chart and the defining spectrum isomorphism. Thus its chart and structural-map hypotheses hold, even though A and C need not be local or noetherian. I opened lem-weil-pbc-ind-etale-stability and verified its actual statement supplies all four operations used: composition, base change, the relative A-algebra-map assertion, and ind-etale implies weakly etale. Both H_A and H_B are ind-etale over A; both H_C and H_D are ind-etale over C. No relative-map assertion is applied to k or l. This is non-elementary and cites the statements that give it. The geometric point forces these four rings to exist; a zero ring without a point supplies no instance of the hypotheses.

Step 3 uses the functoriality statement's explicit strict henselian locality and locality of h and m. I read 092Z's theorem and the statement of thm-weil-pbc-weak-etale-strict-local: its codomain need only be local, its source must be strictly henselian, and the map must be local and weakly etale. Step 2 and the functoriality node give every hypothesis for both applications. This proves two simpler map isomorphisms; it does not cite a new node restating the item.

Step 4 uses only def-pc-fibre-product and the structural compatibility already stated in the functoriality node. I checked the explicit inverse s to p_C on each projection: the pullback equation gives its first projection, and its second projection is the identity. The equality p_C c=z then gives the inverse z^{-1}p_C of c. Both original structural composites are stated by functoriality, and the uniqueness clause for Y establishes equality of maps to Y. The proof does not silently identify an arbitrary isomorphism with the canonical map. This is a few-line universal-property calculation, hence elementary.

I tested the argument with B=A (all maps reduce to the identity comparison), B=A×A (the chosen geometric point selects a component), an infinite filtered ind-etale presentation (the stability node has no finite-generation restriction), arbitrary nonreduced C, and Xi with positive transcendence degree over an image residue field. The proof remains valid: it uses neither reducedness nor finiteness of C, and residue inclusions are relative separable closures rather than an identification with the whole Xi. If Y is empty there is no geometric point and no false assertion about a strict-local zero ring.

I checked B–E against the files: no unsplit new node carries a proof, no invented notion is introduced, the statement is unchanged, TeX has single logical backslashes, all citations exist, and proof_deps is the union of uses. citations.json contains the full verbatim statement for every cited node at each step. I traced each cited theorem's dependency closure and found no path back to the item. The affine-chart and functoriality nodes from sk-thm-p1 are declared as generic tool uses; the affine fibre-product node is on the unit's existing sk-thm-reduction route. No unit route is replaced. I corrected the initial temptation to invoke general quasi-finite strict-henselization continuity without a node: the delivered argument instead uses the existing relative ind-etale-map theorem and writes all inverse and compatibility calculations explicitly. No live project, live launcher, Lean file or compiler was touched by this worker.

## Validation

The delivery dry run printed OK (not pushed), with preflight passed. No push was made. The sandbox is left for a separate second reader.

## Second reading by NS

I reread the item against Algebra Tag 0GIP case (2), including the displayed strict-henselization tensor comparison and its hypotheses; the statement agrees hypothesis by hypothesis, including arbitrary $A\to C$, ind-etale $A\to B$, and the geometric point. I checked the four proof steps against the cited node statements and the affine fibre-product and universal-property definitions: steps 1 and 4 are elementary ring/scheme pullback calculations, while steps 2 and 3 use exactly the affine-chart ind-etale, ind-etale stability, functoriality, and weakly-etale strict-local isomorphism statements cited. The map orientations in steps 3--4 were checked (a ring map $H_A\to H_B$ induces the scheme map in the required reverse direction), and the inverse to the second projection is a valid fibre-product construction. I checked the edge cases $B=A$, a product algebra, empty fibre products (no geometric point), and nonfinite/nonreduced $C$; no extra finiteness or algebraicity hypothesis is used.

There are no new nodes, so B1--B7, duplicate checks, and new-node Mathlib searches are vacuous. I verified every citation quote is verbatim, every cited node exists, and no proof-dependency cycle is introduced. No mathematical or metadata repair was necessary; this section records the independent second reading before delivery.
