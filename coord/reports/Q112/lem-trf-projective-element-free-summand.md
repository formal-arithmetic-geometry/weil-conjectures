# Repair report for lem-trf-projective-element-free-summand

## Files written

- dag/nodes/sec-trace-formula/lem-trf-projective-element-free-summand.json: unchanged statement; four-step assembly, status split.
- dag/nodes/sec-trace-formula/lem-trf-minimal-support-fixed-vector-coordinates.json: statement, unsplit; no Mathlib match, proof empty.
- dag/nodes/sec-trace-formula/lem-trf-local-irredundant-relation-matrix.json: statement, unsplit; no Mathlib match, proof empty.
- dag/nodes/sec-trace-formula/lem-trf-finite-block-basis-replacement.json: statement, unsplit; no Mathlib match, proof empty.
- citations.json: verbatim statement quotations for every use in the parent proof.
- report.md: review and preserved argument allocation.

## Attachments

None. The project-source tag and notion searches found no exact finished theorem under lean/WeilConjectures. The exact declaration Module.projective_element_mem_free_summand in lean/Sheaf/SecTraceFormula/ProjectiveElementFreeSummand.lean still ends in sorry. The finite-projective splitting theorem under WeilConjectures/Mathlib/Algebra/Category/ModuleCat/Projective.lean requires finite generation and does not assert this item.

## WANTED

None. Read the local algebra.tex proof of Tag 0592, lemma-projective-freeness-criteria, in full, including its final matrix paragraph.

## What was wrong and what changed

The return specifically requires spreading the 4195-character argument across at least two new independent statement-only nodes, preserving the item statement and limiting its proof to 3000 characters. The sandbox initially contained only dispatcher marker files, no node, report or search log, so I copied the current returned item from the read-only repository. Its seven steps match the return lengths. I changed only split-owned fields, retained its source, Lean metadata, blueprint ancestry and existing Mathlib searches, and added three independently stated arguments. No statement dispute or route correction is needed. Parent proof length: 1572 characters. No parent step exceeds 2000 characters.

## Work allocation and complete retained arguments

The new nodes are independently usable algebra lemmas, not clauses asserting that an element of a local projective module lies in a free summand. The coordinate lemma needs only a free module and a fixed vector of an endomorphism. The matrix lemma involves no module at all. The block replacement lemma needs neither locality, projectivity, a distinguished vector nor minimal support. Their mathematical work sizes are roughly the original steps 2-3 (1017 characters), steps 4-5 (1451), and step 6 plus the ambient part of step 7 (about 1100).

### Original step 1: Parent assembly step 1 (embedding and zero case)

By the direct-summand characterization in [def-weil-pbc-projective-module], realize $P$ as a submodule of a free module $F$ with an $R$-linear retraction $\pi:F\to P$, $\pi|_P=1_P$. Put $Q=\ker\pi$; then $f=\pi(f)+(f-\pi(f))$ gives $F=P\oplus Q$. Choose a basis of $F$ as in [def-weil-pbc-free-module]. If $x=0$, take $G=0$, whose basis is empty, and $H=P$. Henceforth assume $x\ne0$.

### Original step 2: lem-trf-minimal-support-fixed-vector-coordinates

Among all bases of this fixed ambient module $F$, choose one $\mathcal B$ for which the finite support of $x$ has least cardinality $n$, using [def-weil-pbc-free-module] and the least-element property of $\mathbb N$. Enumerate this support by $e_1,\ldots,e_n$, so $x=\sum_i a_i e_i$. For every $j$, $a_j$ is not an $R$-linear combination of the other $a_i$. Indeed, if $a_j=\sum_{i\ne j}a_i c_i$, replace $e_i$ by $e_i+c_i e_j$ for $i\ne j$ in this finite support, and fix $e_j$ and the remaining basis vectors. The inverse replacement subtracts $c_i e_j$, so this is still a basis. In this basis $x=\sum_{i\ne j}a_i(e_i+c_i e_j)$, with support at most $n-1$, contrary to the choice of $n$.

### Original step 3: lem-trf-minimal-support-fixed-vector-coordinates

Put $y_i=\pi(e_i)\in P$. Split the basis coordinates of each $y_i$ as $y_i=\sum_{j=1}^n b_{ij}e_j+t_i$, with $t_i$ in the span of $\mathcal B\setminus\{e_1,\ldots,e_n\}$, using [def-weil-pbc-free-module]. Since $\pi(x)=x$, we have $x=\sum_i a_i y_i$. Comparing the $e_j$-coordinates gives $a_j=\sum_i a_i b_{ij}$ for every $j$.

### Original step 4: lem-trf-local-irredundant-relation-matrix

Let $\mathfrak m$ be the unique maximal ideal of $R$. By [lem-weil-pbc-local-ring-unit-criterion], the nonunits are exactly the elements of $\mathfrak m$. The relations in step 3 imply $1-b_{jj}$ is a nonunit: if it were a unit, $(1-b_{jj})a_j=\sum_{i\ne j}a_i b_{ij}$ would express $a_j$ using the other coefficients, contradicting step 2. Thus $1-b_{jj}\in\mathfrak m$, so $b_{jj}\notin\mathfrak m$ (otherwise their sum $1$ lies in this proper ideal), and $b_{jj}$ is a unit. Likewise for $i\ne j$, if $b_{ij}$ were a unit, the equality $b_{ij}a_i=(1-b_{jj})a_j-\sum_{k\ne i,j}a_k b_{kj}$ would express $a_i$ using the other coefficients. Hence every off-diagonal $b_{ij}$ belongs to $\mathfrak m$.

### Original step 5: lem-trf-local-irredundant-relation-matrix

Let $A=(b_{ij})$. In the Leibniz formula [def-weil-pbc-matrix-determinant], the identity permutation contributes the unit $u=\prod_i b_{ii}$. Every other permutation moves some index, so its product has an off-diagonal factor in $\mathfrak m$; its signed product is in $\mathfrak m$. Therefore $\det A=u+v$ with $v\in\mathfrak m$. If $\det A$ belonged to $\mathfrak m$, then $u=(\det A)-v$ would too, contradicting the unit criterion [lem-weil-pbc-local-ring-unit-criterion]. Thus $\det A$ is a unit. The adjugate identities [lem-weil-pbc-matrix-adjugate-identity] show explicitly that $(\det A)^{-1}\operatorname{adj}(A)$ is a two-sided inverse of $A$. This writes out the local matrix argument at the end of Tag 0592 without introducing a new lemma.

### Original step 6: lem-trf-finite-block-basis-replacement

Let $E$ be the span of $e_1,\ldots,e_n$ and $T$ the span of the remaining original basis vectors; thus $F=E\oplus T$ by [def-weil-pbc-free-module]. Define $U:F\to F$ by $U(e_i)=y_i$ and by fixing the other basis vectors. On a finite-coordinate vector $c=(c_i)$ and $t\in T$, its formula is $U(c,t)=(Cc,Dc+t)$, where $(Cc)_j=\sum_i b_{ij}c_i$ and $Dc=\sum_i c_i t_i$. The operator $C$ is the transpose of $A$ and has inverse the transpose of the inverse from step 5 (transpose reverses products by the entrywise formula). Consequently $(c,t)\mapsto(C^{-1}c,t-DC^{-1}c)$ is an inverse of $U$, as direct substitution verifies both composites. It follows from uniqueness of expansions in the old basis that $y_1,\ldots,y_n$ together with the remaining original basis vectors form a basis of $F$.

### Original step 7: lem-trf-finite-block-basis-replacement (ambient basis/free summand); parent assembly step 4 (intersection complement and containment)

Let $G=\sum_i R y_i=U(E)$, which is contained in $P$, and keep $T$ from step 6. The new basis [def-weil-pbc-free-module] gives $F=G\oplus T$ and makes $G$ finite free with basis $y_1,\ldots,y_n$. For each $p\in P$, write uniquely $p=g+t$ in this decomposition of $F$. Since $g\in G\subseteq P$, also $t=p-g\in P\cap T$. Conversely $G\cap(P\cap T)=0$, so $H=P\cap T$ gives $P=G\oplus H$. Finally $x=\sum_i a_i y_i\in G$ by step 3. Together with the zero case of step 1, these are all clauses of the item, without any finite-generation hypothesis on $P$.

The coordinate node's future proof chooses a least support cardinality, performs precisely the invertible shear with subtraction as its inverse, then uses unique coordinates of pi(x)=x. The matrix node's future proof retains both nonunit contradictions, the proper-ideal argument for the diagonal, every permutation term of the determinant calculation, and the explicit adjugate inverse. Existing inputs for that worker are lem-weil-pbc-local-ring-unit-criterion (00E9), def-weil-pbc-matrix-determinant (Leibniz formula) and lem-weil-pbc-matrix-adjugate-identity (07DQ); they are not proof dependencies of a statement-only child. The block node's future proof retains C=B transpose, inverse V transpose, D(c)=sum c_i t_i, and the two inverse block formulas U(c,t)=(Cc,Dc+t) and U^{-1}(c,t)=(C^{-1}c,t-DC^{-1}c). Its basis and ambient complement conclusions follow from these inverse composites and unique basis expansions. All of this argument is preserved verbatim above. The elementary transfer H=P intersect T remains explicitly written in the parent.

## Mathlib and duplicate searches

All new searches ran through the prescribed msearch.py command and are recorded exactly in searches.jsonl and the new nodes. Each node has LeanFinder in two phrasings, LeanSearch, Loogle and a source grep; all services returned successfully. Read the actual hits. For minimal support, Basis.mem_span_repr_support and repr_support_subset_of_mem_span in LinearAlgebra/Basis/Basic.lean:50,54 concern only a fixed basis. Vector-space/PID basis selections add hypotheses. For the local matrix, Matrix.isUnit_iff_isUnit_det (LinearAlgebra/Matrix/NonsingularInverse.lean:127) and invertibleOfIsUnitDet (:443) require the unit determinant and do not prove it from irredundancy. For replacement, Basis.invertibleToMatrix (Matrix/Basis.lean:260) assumes two existing finite bases; Basis.is_basis_iff_det (Determinant.lean:634) assumes the whole basis index is finite. Basis scaling/reindexing/map lemmas do not construct the required block automorphism. These are useful future proof tools, not one-line specializations of the complete new statements.

Searched the whole DAG by tag 0592, lemma-projective-freeness-criteria, minimal support, irredundancy, replacement/basis, block/basis and diagonal/nonunit concepts; also parsed whole-DAG statements to distinguish statement matches from incidental proof text. Ran blueprint_refs.py ancestor and searches for minimal support, basis replacement, irredundant, 0592, invertible matrix and basis. The first four had no blueprint statement match; the last two returned geometric/sheaf notions, not these module lemmas. The same_as fields stay empty and the exact inherited blueprint place and via chain are retained.

## Not duplicates

lem-trf-minimal-support-fixed-vector-coordinates vs lem-weil-l-adic-extension-integers-dvr-core: the existing statement concerns Core valuation-ring properties for a finite p-adic extension; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-coef-spatial-mapping-interchange: the existing statement concerns Interchanging the spatial arguments of coherent transformation spaces; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-coef-infinity-fixed-boundary-functor-kan: the existing statement concerns Fixed-boundary functor objects with all vertices fixed are Kan; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-sf-perfect-over-derived-complete-ring: the existing statement concerns Perfect complexes over a derived-complete ring are derived complete; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-coef-infinity-core-kan-fibration: the existing statement concerns Isofibrations induce Kan fibrations on cores; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-trf-projective-over-local-free: 0593 asserts the entire arbitrary projective module is free and depends on the item; this child is a smaller algebra input and does not use 0593.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-trf-etale-closed-complement-sets: the existing statement concerns Closed immersion on small etale sheaves of sets; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-trf-projective-element-free-summand: the item asserts existence of a free summand inside a local projective module; this child instead states minimal-support coordinates of a vector fixed by an endomorphism, under the separate hypotheses printed in its own statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-trf-lci-adjunction-top-ext: the existing statement concerns Top Ext consequence of normalized derived Koszul adjunction; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-pc-affine-perfect-graded-hom-descent: the existing statement concerns Descent of degree-minus-one graded maps on bounded finitely presented complexes; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-sc-p1-proj-sheafification-exact: the existing statement concerns Exactness of sheafification on Proj; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-sfb-integral-lattice-cubical-contraction: the existing statement concerns Integral cubical lattice chains retract onto the augmentation; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-sc-picard-affine-structure-projective-homology: the existing statement concerns Picard affine structure projective homology; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-sc-picard-affine-structure-projective-model: the existing statement concerns PicardAffineStructureProjectiveModel; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-sc-picard-affine-structure-projective-representation: the existing statement concerns Picard affine structure projective representation; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs def-weil-pbc-bounded-constructible-tower: the existing statement concerns Uniformly bounded constructible tower; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-pur-condensed-exceptional-reconstruction: the existing statement concerns Condensed exceptional inverse image of a reconstructed finite-level system; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-weil-l-adic-extension-integers-dvr-core: the existing statement concerns Core valuation-ring properties for a finite p-adic extension; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-coef-spatial-mapping-interchange: the existing statement concerns Interchanging the spatial arguments of coherent transformation spaces; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-coef-infinity-fixed-boundary-functor-kan: the existing statement concerns Fixed-boundary functor objects with all vertices fixed are Kan; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-sf-perfect-over-derived-complete-ring: the existing statement concerns Perfect complexes over a derived-complete ring are derived complete; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-coef-infinity-core-kan-fibration: the existing statement concerns Isofibrations induce Kan fibrations on cores; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-trf-projective-over-local-free: 0593 asserts the entire arbitrary projective module is free and depends on the item; this child is a smaller algebra input and does not use 0593.

lem-trf-local-irredundant-relation-matrix vs lem-trf-etale-closed-complement-sets: the existing statement concerns Closed immersion on small etale sheaves of sets; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-trf-projective-element-free-summand: the item asserts existence of a free summand inside a local projective module; this child instead states a local relation matrix fixing an irredundant tuple is invertible, under the separate hypotheses printed in its own statement.

lem-trf-local-irredundant-relation-matrix vs lem-trf-lci-adjunction-top-ext: the existing statement concerns Top Ext consequence of normalized derived Koszul adjunction; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-pc-affine-perfect-graded-hom-descent: the existing statement concerns Descent of degree-minus-one graded maps on bounded finitely presented complexes; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-sc-p1-proj-sheafification-exact: the existing statement concerns Exactness of sheafification on Proj; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-sfb-integral-lattice-cubical-contraction: the existing statement concerns Integral cubical lattice chains retract onto the augmentation; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-sc-picard-affine-structure-projective-homology: the existing statement concerns Picard affine structure projective homology; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-sc-picard-affine-structure-projective-model: the existing statement concerns PicardAffineStructureProjectiveModel; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-sc-picard-affine-structure-projective-representation: the existing statement concerns Picard affine structure projective representation; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs def-weil-pbc-bounded-constructible-tower: the existing statement concerns Uniformly bounded constructible tower; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-local-irredundant-relation-matrix vs lem-pur-condensed-exceptional-reconstruction: the existing statement concerns Condensed exceptional inverse image of a reconstructed finite-level system; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-weil-l-adic-extension-integers-dvr-core: the existing statement concerns Core valuation-ring properties for a finite p-adic extension; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-coef-spatial-mapping-interchange: the existing statement concerns Interchanging the spatial arguments of coherent transformation spaces; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-coef-infinity-fixed-boundary-functor-kan: the existing statement concerns Fixed-boundary functor objects with all vertices fixed are Kan; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-sf-perfect-over-derived-complete-ring: the existing statement concerns Perfect complexes over a derived-complete ring are derived complete; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-coef-infinity-core-kan-fibration: the existing statement concerns Isofibrations induce Kan fibrations on cores; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-trf-projective-over-local-free: 0593 asserts the entire arbitrary projective module is free and depends on the item; this child is a smaller algebra input and does not use 0593.

lem-trf-finite-block-basis-replacement vs lem-trf-etale-closed-complement-sets: the existing statement concerns Closed immersion on small etale sheaves of sets; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-trf-projective-element-free-summand: the item asserts existence of a free summand inside a local projective module; this child instead states replacing a finite block in an arbitrary module basis, under the separate hypotheses printed in its own statement.

lem-trf-finite-block-basis-replacement vs lem-trf-lci-adjunction-top-ext: the existing statement concerns Top Ext consequence of normalized derived Koszul adjunction; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-pc-affine-perfect-graded-hom-descent: the existing statement concerns Descent of degree-minus-one graded maps on bounded finitely presented complexes; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-sc-p1-proj-sheafification-exact: the existing statement concerns Exactness of sheafification on Proj; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-sfb-integral-lattice-cubical-contraction: the existing statement concerns Integral cubical lattice chains retract onto the augmentation; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-sc-picard-affine-structure-projective-homology: the existing statement concerns Picard affine structure projective homology; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-sc-picard-affine-structure-projective-model: the existing statement concerns PicardAffineStructureProjectiveModel; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-sc-picard-affine-structure-projective-representation: the existing statement concerns Picard affine structure projective representation; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs def-weil-pbc-bounded-constructible-tower: the existing statement concerns Uniformly bounded constructible tower; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-finite-block-basis-replacement vs lem-pur-condensed-exceptional-reconstruction: the existing statement concerns Condensed exceptional inverse image of a reconstructed finite-level system; its 0592 text is incidental to its proof/search metadata, not this child statement.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-trf-flat-ml-minimal-support: the existing lemma constructs a least tensor-supporting submodule for a flat Mittag-Leffler module, not a basis minimizing vector support or a matrix/basis replacement criterion.

lem-trf-local-irredundant-relation-matrix vs lem-trf-flat-ml-minimal-support: the existing lemma constructs a least tensor-supporting submodule for a flat Mittag-Leffler module, not a basis minimizing vector support or a matrix/basis replacement criterion.

lem-trf-finite-block-basis-replacement vs lem-trf-flat-ml-minimal-support: the existing lemma constructs a least tensor-supporting submodule for a flat Mittag-Leffler module, not a basis minimizing vector support or a matrix/basis replacement criterion.

lem-trf-finite-block-basis-replacement vs lem-weil-pbc-triangular-change-of-basis: the existing lemma assumes a finite whole basis and a triangular matrix; the new lemma permits an arbitrary invertible finite block and arbitrary tails in an infinite complementary span.

lem-trf-minimal-support-fixed-vector-coordinates vs lem-a1-relative-affinization-compatible-charts: the current existing statement constructs compatible scheme morphisms into relative-affinization charts for a quasi-compact, quasi-separated morphism; it states none of the coordinate, local-matrix or basis-block assertions here. Its 0592 occurrence is incidental metadata, not its source or statement.

lem-trf-local-irredundant-relation-matrix vs lem-a1-relative-affinization-compatible-charts: the current existing statement constructs compatible scheme morphisms into relative-affinization charts for a quasi-compact, quasi-separated morphism; it states none of the coordinate, local-matrix or basis-block assertions here. Its 0592 occurrence is incidental metadata, not its source or statement.

lem-trf-finite-block-basis-replacement vs lem-a1-relative-affinization-compatible-charts: the current existing statement constructs compatible scheme morphisms into relative-affinization charts for a quasi-compact, quasi-separated morphism; it states none of the coordinate, local-matrix or basis-block assertions here. Its 0592 occurrence is incidental metadata, not its source or statement.

## Review by Q112

I read algebra.tex Tag 0592 (lemma-projective-freeness-criteria) from its statement through all three proof paragraphs for the parent and each of the three extracted lemmas. The division follows its actual arguments. I also opened the statements of the free-module and projective-module definitions, local-unit criterion, determinant and adjugate identity. I checked the ancestor/unit/chapter records: these are algebra inputs on the existing flattening route, not changes to the curve unit or its chapter. No SGA source is used.

Parent step 1 uses exactly the projective definition's split embedding/retraction equivalence and the free definition's allowance of an empty basis; their statements really include these clauses. The projection is regarded as an endomorphism through the inclusion of P in F. Identifying P with its split image is legitimate: the split map is injective and the basis/direct-sum data transport along that isomorphism. The displayed formula checks the ambient direct sum directly.

Parent step 2 uses the entire statement of the new coordinate lemma, including the irredundancy, tails, coefficient relation, and expression x=sum a_i y_i. Its commutative-ring, free-module, nonzero-vector and fixed-endomorphism hypotheses are all in force. In particular the matrix relation is supplied by the cited statement, not merely by its future proof.

Parent step 3 uses the local-matrix statement's explicit inverse conclusion, with the same row convention a_j=sum_i a_i b_ij. R is still local and irredundancy came from step 2. The replacement lemma then uses exactly this B, the same finite distinct original basis vectors and the tails in their complementary span; its statement explicitly supplies the basis of G and F=G direct sum T. No finite generation of the whole ambient module or of P has been smuggled into either application.

Parent step 4 uses only the already obtained direct sum and elementary submodule arithmetic: G is contained in P since its generators are, and each t=p-g lies in P intersect T. Uniqueness is inherited from F. The free definition says exactly that the furnished basis makes G free. Every parent citation has a full verbatim statement quotation in citations.json. No step uses a cited proof instead of its statement, and all non-elementary work is isolated in the three cited new statements. No cyclic use of the stronger projective-over-local theorem occurs.

I tested the statements on zero and rank-one cases, empty block, finite and infinite ambient rank, and nonreduced local rings. The coordinate lemma explicitly assumes x nonzero, so n>=1 and nonzero coefficients cause no failure at x=0; that case remains in the parent. The matrix lemma allows n=0, when all entry clauses are vacuous and the empty determinant is 1. For n=1 a nonzero a may have an annihilator, but (1-b)a=0 still forces 1-b to be a nonunit, hence b a unit; cancellation is never used. Over dual numbers, a=epsilon and b=1+epsilon illustrates this case. An irredundant two-generator ideal in a local ring can have nontrivial relations; the argument uses only division by proposed unit coefficients, never domain assumptions. The replacement lemma at n=0 is the identity, at n=1 is a unit scaling plus any complementary tail, and for infinite rank all vectors and tails still have finite basis support. A zero commutative ring makes the coordinate lemma vacuous (x nonzero is impossible); the replacement lemma remains true for indexed zero-module bases.

I checked delivery-errors B--E point by point against these files: children have self-contained statements and empty proof/proof_deps, notions have definition citations or inline definitions, source tags/labels are exact, search queries actually ran, no statement is weakened, and no child restates the parent. The return is repaired by three new work items rather than by text shortening. The original seven arguments above remain available to their future workers. The parent now contains only the short assembly.

## Repair of live-DAG promotion return (2026-10-22)

The maintainer returned the previous delivery because the side completion had not been promoted into the live DAG. I retained the delivered three-node split, report, citations and search log, and compared every sandbox node with the current read-only DAG before preparing this delivery against its current server base. The live parent still contains the original seven-step proof; the three child IDs are absent from the live DAG. The released stage-1 repair note explicitly requires this re-split despite the parent's historical reviewed record.

The comparison found only the intended parent differences: proof, proof_deps and split_report. The parent's statement, stmt_deps, source, blueprint ancestry, proof origin, searches and Lean metadata agree with the current DAG. Thus no changed hypothesis or definition requires altering the retained mathematical split. I updated this report and the split summary to record the live-base repair; the delivery tool rebuilds the branch on its freshly fetched current base, rather than re-pushing the old side-project commit. The initial dry run for this repair completed successfully at cf57fde6e25 before these reporting updates.

I reopened all six existing inputs involved in the statements or retained arguments: def-weil-pbc-projective-module, def-weil-pbc-free-module, def-weil-matrix, def-weil-pbc-matrix-determinant, lem-weil-pbc-local-ring-unit-criterion and lem-weil-pbc-matrix-adjugate-identity. They are present and unmerged. The two parent definition quotations still agree verbatim with their live statements; the other definitions still supply the child statement notions, including the empty determinant. The unit and chapter records and the blueprint ancestor still agree with the inherited route. I re-read algebra.tex lines 20640–20680 (Tag 0592), including minimal support, the basis shear, projection coefficients and the local-matrix argument.

For step 1 I verified again that the live projective definition supplies the split embedding/retraction and the free definition allows an empty basis. For step 2 the child explicitly supplies all coefficient equations and irredundancy under the nonzero and fixed-vector hypotheses. For step 3 the matrix child's inverse conclusion is the hypothesis of the block replacement child, which explicitly returns both the basis of G and the ambient complement T. For step 4 the intersection H=P intersect T is checked by t=p-g and uniqueness in the ambient decomposition, and the live free definition supplies the final freeness conclusion. All six citation entries were checked for exact inclusion in the current cited statements, including the three retained child statements.

The retained searches.jsonl was read in full; it has two semantic phrasings and the other prescribed tools for each new node, all successful. Their questions and statements have not changed, so no searches were repeated or invented. The current exact local Lean declaration still ends in sorry, and the project-source searches still give no finished attachment. The parent remains 1572 characters with step lengths 393, 360, 409 and 410. I reconsidered the zero-vector, empty-block and rank-one cases and the row/column convention in the inverse block calculation: none changes on this base. No mathematical correction, statement weakening or additional child is needed for the promotion return. Final server dry run and direct push are required after this report update.

## Unfinished work

The three new nodes are deliberately unsplit and proof-free, as required by the re-split decision. No Lean is written and no compiler or build tool was run. Validation and direct delivery follow the required server checks.

## Continued promotion repair: current-base revalidation

After the interrupted session, I retained all node files, the original seven arguments, citations and logged searches. The new initial server dry run exited successfully with `OK (not pushed)` at `7aa2c5873c4`. This supersedes the earlier receipt at `e9724a460f4` as evidence that the retained split passes on the newly fetched server base; the final delivery must rebuild against that base, not reuse the returned side-project head.

I compared all four delivered nodes with the present read clone: the three children remain absent, and the parent differs only in proof, proof_deps and split_report. Its unchanged statement, source, statement dependencies, blueprint fields and Lean metadata still match. I reopened all six existing inputs listed above, the unit and chapter, and the complete Tag 0592 proof. Each remains compatible with the retained argument. In particular, the projective definition still states the splitting equivalence used in step 1, and the free definition explicitly allows an empty basis. All six citation entries still match verbatim and cover every proof use. No changed cited statement requires replacement or a new hypothesis.

I rechecked the child hypotheses and small cases: the coordinate child requires a nonzero fixed vector, the matrix child receives exactly its irredundant coefficient relations over the local ring, and its two-sided inverse supplies the block child's matrix hypothesis. The intersection complement in step 4 uses only the ambient unique decomposition. The unchanged 1572-character assembly and three independent statement-only children retain the required division of work. The exact local Lean theorem still has sorry, while the project-source searches supply no finished attachment. The unchanged search questions justify retaining the original successful search records. This repair changes the delivery base and records its renewed review; it does not alter the accepted mathematics.

## Current live-base repair review (2026-10-23)

The initial required dry run completed with `OK (not pushed)` at `c0288b307c9`. I compared the retained four node files against the current shared read clone: all three child IDs are still absent, and the parent still has the old seven-step proof. The only differing parent fields are proof, proof_deps and split_report. Its statement and statement dependencies, source, blueprint, searches, Lean metadata and other retained fields agree with the current node. The released stage-1 repair note still explicitly requires at least two statement-only children and an assembly of at most 3000 characters, so its historical reviewed record does not close this repair.

I re-read the current statements of all six existing algebra inputs: the projective and free definitions used by parent steps 1 and 4, the matrix and determinant definitions used in the children, and the local-unit and adjugate identities used in the retained future proof arguments. In particular the projective statement still explicitly supplies the splitting into a free module, the free statement permits an empty basis, the determinant statement includes size zero, and the local-unit statement requires precisely the unique-maximal-ideal hypothesis available to the matrix child. None forces a mathematical change to the approved split. I read the chapter/unit records and the full Tag 0592 proof again, including the last matrix paragraph. The blueprint ancestor search still returns lem-trf-local-term-locality.

For step 1, the splitting supplies an injective map into F and a retraction, and the formula f=pi(f)+(f-pi(f)) verifies the claimed ambient decomposition. For step 2, the coordinate child's own statement supplies irredundancy, all tails, and both displayed relations for the nonzero fixed vector; the retraction fixes x. For step 3, the local matrix child receives exactly its irredundant tuple and row-vector relation, and its two-sided inverse satisfies the basis-block child's hypothesis with the identical coefficient convention. For step 4, t=p-g lies in P intersect T because G is already contained in P, and uniqueness follows from the ambient direct sum. These arguments do not use any cited node's proof in place of its statement. All six citations.json entries were checked against the current statements and cover every proof use.

I retained and read all fifteen logged search results rather than repeating unchanged questions. The recorded support lemmas concern a fixed basis, the finite determinant/basis criteria require a finite whole basis or two existing bases, and matrix inversion from a unit determinant does not supply the irredundant local-tuple conclusion. Reading these candidate declarations in the pinned Mathlib confirms the earlier nonmatch verdicts. A renewed DAG search found one additional incidental 0592 hit, lem-a1-relative-affinization-compatible-charts; I opened its statement and added the three missing pairwise explanations under Not duplicates. Blueprint searches for irredundancy and basis replacement again found no matching imported statement. The exact local theorem in Sheaf/SecTraceFormula/ProjectiveElementFreeSummand.lean still ends in sorry; the project-source searches find no exact finished attachment.

I reconsidered the zero-vector branch, n=0 and n=1 for the matrix and block statements, and arbitrary ambient rank. The matrix proof divides only by a coefficient hypothetically assumed to be a unit, never by a nonzero element, so it also works with zero divisors. The block inverse uses the transpose matrix because (Cc)_j=sum_i b_ij c_i; its two composites preserve both the finite coordinates and the unrestricted complementary tails. The children remain statement-only and independent of locality/projectivity wherever their statements do not require those hypotheses. The parent proof has 1572 characters, with step lengths 393, 360, 409 and 410. The new changes for this repair are the current-base report, the newly needed duplicate comparisons, and the dated split-report revalidation; the accepted mathematical arguments and all original seven proof arguments above are retained. The required delivery tool rebuilds the branch on the freshly fetched server base. A final dry run must exit successfully before the direct push.
