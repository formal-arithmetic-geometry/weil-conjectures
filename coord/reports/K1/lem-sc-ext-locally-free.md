files written:
- `dag/nodes/sec-picard-framework/lem-sc-ext-locally-free.json` (repaired split)
- `dag/nodes/sec-picard-framework/lem-sc-ext-evaluation.json` (unsplit, no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-ext-tensor-exact.json` (unsplit, no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-ext-derived-composite.json` (unsplit, no Mathlib match)
- `citations.json` (one verbatim statement quote per proof citation)

attachments:
- `AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H` belongs to `lem-sc-ext-locally-free`; it has `sorry` in `WeilConjectures/AlgebraicGeometry/Modules/Ext.lean:77-79`.

WANTED:
- The Stacks and blueprint source files are absent from this checkout's `literature/` tree; I used the imported blueprint proof clauses, the reviewed `lem-weil-pbc-module-tensor-hom-adjunction` node (which records Modules 01CN, `lemma-internal-hom`), and the cited nodes' full statements. A fresh source-text check remains for the maintainer.

what was wrong in the node, blueprint, or earlier delivery:
- The old step 3 had no module tensor-Hom adjunction. The DAG already has `lem-weil-pbc-module-tensor-hom-adjunction`, so the repair cites it, plus sectionwise tensor symmetry and sheafification, instead of duplicating its statement as another unsplit node.
- The old sheaf-Hom citations used a node for the group of morphisms. The sheaf itself, and its global-sections identification, are stated by `def-pur-sheaf-hom`.
- The old step 4 did not establish enough injectives for the module category. The derived-composite support statement now asks this only of its source and middle categories.
- The old step 2 called global sections left exact by citing the definition of left exactness. It now checks preservation of kernels and finite products using sectionwise kernels.
- The old support statements silently treated finite locally free as constant rank. Both now give the open-cover condition with ranks varying among opens. The parent item keeps the paper's unqualified phrase and no longer cites the constant-rank definition as its meaning.

what I could not finish, and why:
- The three support lemmas remain unsplit, as stage 1 requires. The absent literature source tree prevents a fresh TeX read; the existing reviewed 01CN node supplies the required adjunction statement and its exact source locator.

## Source error

The blueprint's parenthetical assertion that right deriving an exact functor followed by a left exact functor gives the composite of derived functors lacks an acyclicity hypothesis. Take $T$ to be restriction of scalars from $\mathbf F_2$-vector spaces to abelian groups and $U=\operatorname{Hom}_{\mathbf Z}(\mathbf Z/2,-)$. Then $T$ is exact and every vector space is injective, so $R^1(U\circ T)=0$, while $R^1U(T(\mathbf F_2))=\operatorname{Ext}^1_{\mathbf Z}(\mathbf Z/2,\mathbf Z/2)=\mathbf Z/2$. The support statement now requires $T(I)$ to be $U$-acyclic for injective $I$. Separately, `def-sc-ext-sheaf` defines Ext using a contravariant first-variable right derivative; the proof needs the second-variable computation, supplied by `lem-weil-pbc-ext-via-injective-resolution`. The parent target's statement was not weakened.

## Review by K1

I checked the item's imported blueprint proof clauses, its unit, the cited DAG statements, and the existing reviewed Modules 01CN node. That node states the Hom bijection for sheaves of modules over a ringed space, natural in the variable needed here; its recorded source is `modules.tex`, `lemma-internal-hom`, Tag 01CN. The source files themselves are not present locally. For the evaluation and tensor-exact support nodes, I checked the blueprint's evaluation and exactness clauses against the open-cover hypotheses written in those statements. For the derived-composite support node, I checked the algebraic requirement that $T(I)$ be $U$-acyclic and that only its source and middle categories need enough injectives. All three new statements have only statements, no proof steps.

Step 1 uses the evaluation node for the sheaf-level isomorphism, `def-pur-sheaf-hom` for its global sections being ordinary module Hom, `def-sc-ext-sheaf` for degree-zero Ext, and `pqf-def-cohomology` for degree-zero cohomology. Step 2 computes the dual on each member of a finite free open cover; the sheaf-Hom definition and constant-rank definition support this local calculation, while ranks may vary from one open to another. The tensor-exact node applies to that dual. The evaluation and sheaf-Hom nodes identify the composite functor. The module-category node says kernels are sectionwise, which is the reason global sections preserves them; the left-exactness definition supplies the criterion.

Step 3 uses the already-reviewed module tensor-Hom adjunction on the ringed space $X$. The tensor-commutativity node swaps its factors sectionwise; the tensor-product definition sheafifies the swap. The sheaf-Hom node identifies the right adjoint, and evaluation identifies it with $T$. Exactness of tensor by $\mathcal F$ and the right-adjoint theorem then give injectivity of $T(I)$; the derived-functor and acyclicity definitions yield its $\Gamma$-acyclicity. Step 4 cites the scheme-module enough-injectives theorem for both instances of $\operatorname{Mod}(\mathcal O_X)$, the derived-composite support statement, the cohomology definition, and the injective-resolution Ext theorem. The latter explicitly assumes enough injectives for its derived-functor conclusion. Step 5 checks the unit object using the sheaf-Hom and tensor definitions.

I checked the small cases $\mathcal F=0$ and $\mathcal F=\mathcal O_X$; both evaluation and exactness specialize correctly. On a disconnected scheme, a finite locally free module of different ranks on the components still satisfies both support statements, which the former constant-rank wording did not cover. Every `citations.json` quote is an exact substring of the cited node's statement, and `proof_deps` is the union of the five steps' citations.
