# Q19 stage-1 report

Item: lem-sfb-semihereditary-topological-coefficients-admissible.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semihereditary-topological-coefficients-admissible.json: split, four proof steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-semihereditary-finite-free-submodule.json: statement, unsplit; no exact Mathlib match. A finitely generated submodule of finite free R^n is projective under the semihereditary hypothesis.
- dag/nodes/sec-six-functors-basics/lem-sfb-semihereditary-torsionless-flat.json: statement, unsplit; no exact Mathlib match. Chase's theorem for an arbitrary module embedding in an unrestricted product of scalar copies.
- citations.json: one literal quotation from the cited statement for every use in every proof step.

There are two new nodes, zero new Mathlib leaves. The existing leaf lem-weil-pbc-finite-projective-finitely-presented is reused. Searches and local reading material are also preserved in this sandbox.

## Attachments

None. Searches for the item id, semihereditary/semi-hereditary, torsionless, flat continuous functions and regular coherent coefficients in lean/WeilConjectures found no declaration proving this item. Uses of Module.finitePresentation_of_projective in project files prove other assertions; they do not supply the topological flatness clause. The existing DAG leaf already records that Mathlib theorem, at Mathlib/Algebra/Module/FinitePresentation.lean:161, whose source I read.

## Wanted

WANTED: T. Y. Lam, Lectures on modules and rings (1999), Definition 4.64 and Theorem 4.67, for lem-sfb-semihereditary-torsionless-flat. The book is not listed or present among the available literature. HRS Lemma 6.10 explicitly states this theorem and applies it, so it is the available source for the statement-only node; no claim to have read Lam is made. No literature or coordination file was changed.

## Source and route audit

I read Hemo–Richarz–Scholbach, Constructible sheaves on schemes, arXiv:2305.18131v1, the paragraph before Definition 6.1, Definition 6.1, Lemma 6.7(1) and its proof, and Lemma 6.10 and its full proof (printed pp. 15–18). The latter explicitly proves flatness for ANY profinite set, not just extremally disconnected sets. Its embedding uses ALL continuous functions; no finite image, bounded image, finite coefficient extension, completeness or local compactness is imposed. The imported statement is correct; there is no STATEMENT-DISPUTED correction.

The old item had no proof, not a false proof. HRS's sentence that semihereditary rings are regular coherent suppresses the explicit finite-resolution argument demanded by this item's statement. I extracted the general finite-submodule lemma, rather than moving the whole regular-coherence clause into a child. The other new node is precisely the general algebraic theorem used in HRS's proof, not the continuous-function conclusion of the item.

I read the inherited chapter and unit records, the three levels in SETUP, and the latest blueprint cocycle statement/proof. The inherited ancestry is det-sf-comp-coherence-cocycle through the Noetherian scalar-model heart route; the current cocycle proof is an assembly from refinement isomorphisms. This split only supplies its already imported coefficient-support lemma and does not alter the unit route, chapter or unit records. The inherited blueprint ancestry and non-unspecified place are preserved and made precise in the split report and new nodes. Whole-blueprint searches for semihereditary, torsionless, projective submodule, finite free submodule and finitely generated submodule found no blueprint statement of either new fact.

## New-node arguments retained for later workers

For the finite-free-submodule node, induct on n. At n=0, K=0. For K contained in R^n, project onto the last coordinate. Its image J is a finitely generated ideal, hence projective. The surjection K to J splits by projectivity. Its kernel K' is therefore a direct summand of the finitely generated module K, hence finitely generated: project a finite generating list of K onto K'. It embeds in R^(n-1). Induction makes K' projective, and K is isomorphic to K' direct sum J, which is projective by lifting separately on the two summands. This is a real general inductive lemma, not an elementary restatement of the finite-resolution conclusion. Its node remains statement-only as required.

For the torsionless-flat node, the available source is exactly the last sentence of HRS Lemma 6.10's proof, citing Chase via Lam Theorem 4.67. The statement spells out torsionless as an actual embedding into a full product, so it requires no unstated definition node and no domain hypothesis. Future splitting can use the finite-projective tensor/product comparison: for every finitely generated ideal I, I is finite projective, so I tensor the evaluation embedding stays injective and I tensor a product of R identifies with the product of I; coordinatewise ideal inclusion is injective. The finitely generated ideal flatness criterion then gives flatness. This sketch is in this report only, not in the unsplit statement; it is not a claim that the child's dependencies have already been split.

## Mathlib and duplicate searches

All Mathlib queries added to nodes were run through msearch.py and are recorded in searches.jsonl with the exact tool and text. LeanFinder, LeanSearch, Loogle and source grep were available. I read their returned signatures. Two distinct semantic formulations were tried for both new concepts. Free/projective flatness does not show arbitrary torsionless modules are flat; Dedekind/Bézout/valuation-domain criteria have extra domain hypotheses; invertible-submodule projectivity has invertibility hypotheses. These are not one-line specializations to arbitrary semihereditary rings. The item itself was searched with new queries, while its inherited search evidence was retained.

Whole-DAG searches included the item notions, finite projective finite presentation, finite generated submodules, torsionless, Chase and the source places. This found the existing finite-projective/finitely-presented Mathlib leaf, which I reused rather than creating another node. I read the statements of candidate coherent-product flatness, coherent-ring kernel/cokernel finiteness, and scalar-model finite-flat-resolution nodes; they assume coherence, Noetherianity or a DVR and do not assert either new statement.

## Not duplicates

lem-sfb-semihereditary-finite-free-submodule vs lem-weil-pbc-finite-projective-finitely-presented: the new node proves projectivity of finite submodules of R^n from projectivity of finite ideals; the existing node assumes projectivity and concludes finite presentation, so it cannot replace it.
lem-sfb-semihereditary-torsionless-flat vs lem-trf-coherent-product-flat: the latter proves flatness of products over a coherent ring, not of arbitrary submodules of products; the new node uses the stronger semihereditary condition and an embedding of the module.
lem-sfb-semihereditary-finite-free-submodule vs lem-sfb-semihereditary-topological-coefficients-admissible: the new node is a purely algebraic finite-submodule lemma, with no topology, condensed ring, regular coherence or flatness conclusion. The item still constructs the finite resolution.
lem-sfb-semihereditary-torsionless-flat vs lem-sfb-semihereditary-topological-coefficients-admissible: the new node concerns any module with a specified product embedding; the item must construct and verify this embedding for continuous functions and separately prove its scalar finiteness clauses.

## Review by Q19

I checked delivery-errors B–E against the actual statements and sources. New nodes introduce R, n, K, M, A and every hypothesis independently, use single TeX escapes, name the definition nodes they need, and have empty proofs/proof dependencies. Neither new statement quotes a source instead of defining its meaning. The sources are HRS's exact lemma/proof places; no unsupported Stacks tag is presented as the theorem, and no prohibited SGA route is used. No attachment or Mathlib-leaf claim is made from a sorried project declaration.

Step 1 cites lem-weil-pbc-finite-projective-finitely-presented. I opened the file: its full statement is precisely that a finitely generated projective module is finitely presented. The hypothesis of the item supplies projectivity for I and I is explicitly finitely generated, so there is no missing Noetherianity assumption. I also read Mathlib's declaration and Stacks Tag 00NX, algebra.tex lemma-finite-projective, implications (2) to (3) to (1); they agree.

Step 2 cites def-sc-finitely-presented-module, which actually supplies the finite exact presentation, not just a name for finite generation. The m matrix-column images generate K, and the new finite-free-submodule statement applies to K contained in R^n under exactly the item's semihereditary hypothesis. def-weil-pbc-projective-module explicitly includes the direct-summand-of-free characterization, so taking identity maps proves that R^n is projective. The step itself constructs the length-one resolution; it does not merely apply a new node restating that clause. There is no Noetherian hypothesis, no false claim that an arbitrary submodule is finitely generated, and no use of a lemma's proof as if its construction were in the statement.

Step 3 cites def-sfb-continuous-map-condensed-ring, whose statement gives C(P,R) and pointwise operations. The evaluation map is R-linear for the constant scalar action, and equality in the full product implies equality of functions. Thus the new torsionless-flat statement applies verbatim with A equal to the underlying set of P. def-weil-pbc-flat-ring-map defines ring-map flatness using the corresponding module action; this is exactly the constant-function action just checked. The non-elementary Chase theorem has its own cited node; neither the flatness definition nor flatness of the ambient product is substituted for that theorem.

Step 4 cites the continuous-function definition again and def-zl-t-admissible-coefficient-models. I read its full first paragraph, which gives exactly the two scalar finiteness clauses and flatness for extremally disconnected profinite sets. A continuous function on the point is uniquely determined by its value. The two-term resolution from step 2 represents N[0] by its evident augmentation, with kernel and cokernel computed by the exact sequence; the degree-zero perfect condition in the cited definition explicitly expresses such a resolution. Passing from all profinite sets to the extremally disconnected ones is restriction of the quantifier. I marked only this assembly elementary. Every step is below 2000 characters; total proof text is 1847 characters.

I tested the statements on n=0, K=0, N=0, R the zero ring, P empty and P a point. Empty evaluation has zero domain, so the product embedding is still injective and the zero module is flat; flatness here is not claimed faithful. In the new torsionless lemma A empty forces M=0. A semihereditary ring need not be a domain (finite products of fields work), so no torsion-free-domain criterion is silently used. Conversely Z/4 is not a counterexample: its ideal (2) is not projective, so it does not satisfy the hypothesis. All constructions use finitely generated projectives, not necessarily free kernels, and work without a global dimension assertion for arbitrary modules. The unchanged T1 assumption is harmless even though evaluation injectivity itself does not need it.

citations.json was generated from the exact statement strings, including the entire defining paragraph used for t-admissibility. I checked that every uses entry occurs there and its quote is a literal substring of that node's statement. Proof dependencies are exactly the union of step uses. The preliminary server check_dag and review_split passed. No mathematical task remains in this one-level split; the two explicitly unsplit dependencies are left for future workers.

## Unfinished work

No unfinished part of this item's one-level split. The two new statement-only nodes intentionally remain unsplit. The unavailable Lam book is identified above; the available HRS source gives the theorem used here.
