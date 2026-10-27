# Worker report: lem-sfb-cartan-containing-normalizer-smooth

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cartan-containing-normalizer-smooth.json: item, statement unchanged, eight proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-lie-normalizer-centralizer-invariants.json: new statement-only general group-invariant tangent identities, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-group-tangent-dimension-smoothness.json: new statement-only tangent-dimension smoothness criterion, no Mathlib match.
- citations.json: verbatim statement evidence for every cited node in every numbered step.
- searches.jsonl: actual msearch.py log; no searches fabricated or inferred from a failed service.

## Attachments

None. The project-source search for the item tag and its normalizer/Cartan wording returned no declaration. I also searched the actual normalizer and centralizer terminology in WeilConjectures and read GroupScheme/GeneralLinear/ClosedSubgroup/LieSubalgebra.lean, including its scope and characteristic-zero comparison results. Those results do not prove this assertion in arbitrary characteristic, and abstract subgroup normalizer declarations do not represent the required functor on algebras. No Mathlib declaration is offered as a project attachment.

## WANTED

None. Milne's iAG2017 PDF is present. I extracted its text only into this item's sandbox and read the relevant pages.

## What was wrong or incomplete

The item had no proof, proof dependencies, or proof-origin record. Its statement agrees with Milne Lemma 17.47 and Proposition 1.83. No statement dispute or change is needed. The inherited blueprint ancestry has from.node=null; blueprint_refs.py ancestor reports None as well. I preserve that inherited value and complete via list, rather than invent an ancestor id. The current latest blueprint was read at sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially clause (3). This is a supporting Milne input below the inherited alteration/Borel-normalizer route, not a replacement of the unit's six-functor argument.

The proof must use invariants under the entire group functor. Replacing them by invariants of its Lie algebra would be wrong in positive characteristic. The draft explicitly avoids that substitution. Smoothness of a scheme normalizer cannot be inferred just from a statement about ordinary field-valued subgroup normalizers. Both transporter containments are needed for normalizer equality, and universal points, including over nonreduced rings, are used to identify the constructed functor.

## What remains

No part of this one-level split is intentionally omitted. The two new general inputs remain unsplit, with no proof or proof dependencies, as required. Their later workers must prove Proposition 10.34's identities and Proposition 1.37's criterion; neither new node states the item's torus-containment conclusion.

## Not duplicates

lem-sfb-lie-normalizer-centralizer-invariants vs lem-ag-lie-centre: the existing node concerns the centre of a connected matrix group over Q_lbar and its Lie centre. The new node concerns arbitrary closed subgroup functors and full group invariants of a quotient in arbitrary characteristic, with smooth H and explicit representability hypotheses.

lem-sfb-lie-normalizer-centralizer-invariants vs lem-sfb-torus-centralizer-smooth-connected: the existing node supplies representability, smoothness and connectedness for torus centralizers, not their tangent invariant subspace nor the tangent space of a subgroup normalizer.

lem-sfb-lie-normalizer-centralizer-invariants vs lem-sfb-cocharacter-limit-smooth-structure: that node concerns one cocharacter's positive and zero weights and its particular limit subgroups in a smooth connected ambient group. It does not identify the normalizer quotient for an arbitrary smooth subgroup H.

lem-sfb-group-tangent-dimension-smoothness vs lem-ag-smooth-lie-local-dimension: that node assumes smoothness and states the equality with local ring dimension. The new node supplies the inequality without smoothness and the converse equality-implies-smoothness criterion.

lem-sfb-group-tangent-dimension-smoothness vs lem-ag-group-identity-local-dimension: that node identifies local and global Krull dimensions, not tangent dimension or the smoothness criterion.

lem-sfb-group-tangent-dimension-smoothness vs lem-wf-same-lie-closed-subgroup: that node is restricted to matrix groups over Q_lbar and cannot detect nonsmooth group schemes in positive characteristic.

lem-sfb-group-tangent-dimension-smoothness vs lem-sfb-locally-algebraic-group-identity-component: the existing node constructs the neutral component and states smoothness of its reduction; it does not characterize when the original possibly nonreduced group is smooth by its tangent dimension.

The searches before creation included the entire DAG's titles and statements, exact source places Proposition 10.34/Proposition 1.37, and normalizer, torus, tangent and invariant terminology. Whole-blueprint searches were run for normalizer, normalizer invariants, torus representation, group tangent dimension, smooth tangent and centralizer Lie. No blueprint node states either new input. Existing G_m weight decomposition, closed-factorization, component and dimension-drop nodes were retained rather than duplicated. Neither new source cites a Stacks tag shared with another node.

## Mathlib searches and reading

For each new node I ran leanfinder twice with distinct phrasings, Loogle, LeanSearch and Mathlib grep, including a focused AlgebraicGeometry grep and a whole-Mathlib grep. Their exact query text, actual summaries and verdicts are in the node files and searches.jsonl. All these services returned answers. Normalizer searches found abstract subgroup normalizers, LieSubalgebra.normalizer and its Cartan/zero-root self-normalizer theorems; none compares scheme tangent spaces with invariants of a rational algebraic-group action. I read Mathlib/Algebra/Lie/Normalizer.lean, in particular its definitions and Lie-module scope, to reject these hits. Tangent searches found manifold GroupLieAlgebra and IsStandardSmoothOfRelativeDimension cotangent-rank results. I read the StandardSmoothCotangent source and the returned signatures; those require standard smoothness and do not supply the converse smoothness criterion for a possibly nonreduced affine group scheme. Thus no new Mathlib leaf is claimed. The item itself already records two semantic phrasings and grep/Loogle/LeanSearch from its creation; I read these recorded results and retained them unchanged.

## Review by Q18

I read Milne Lemma 17.47, printed p.366, in full, together with Proposition 1.83 (p.31), Proposition 10.34 and its proof (pp.197–198), Theorem 12.12 and Remark 12.13 (pp.234–235), Example 12.15 (p.236), Propositions 1.34–1.37 (pp.16–18), and Proposition 10.15 (pp.190–191). The item is the smooth subgroup variety H of 17.47 containing the Cartan centralizer C_G(T); it does not require H to be connected. The new Lie-input statement is the smooth-H specialization of 10.34 with C and N assumed represented. The new dimension-input statement is 1.37 over the algebraically closed field actually in force. Neither asserts representability, existence of maximal tori, or characteristic-zero differentiation criteria that its cited source would not provide.

For step 1 I opened the affine fibre-product statement and the closed-immersion and proper-morphism definitions. They give the tensor coordinate ring, the closed diagonal, and the separatedness definition used. This verifies separated finite-type X,Y,S before applying the next step's factorization theorem; I do not assume a general closed source is proper.

For step 2 I opened lem-sfb-constant-source-closed-factorization-locus. Its statement allows every separated finite-type constant source, closed W and family Y times S to X, and gives the exact all-test-schemes factorization property. Here H,G,G and H fit these hypotheses. Both conjugation families are morphisms from the group laws. The intersection is the explicit sum of ideals in the affine parameter ring; the affine-spectrum and closed-immersion definitions give the exact test criterion. Finite type of a quotient is immediate from the images of ring generators. No representability assertion is extracted from a proof of a cited node.

For step 3 the cited affine-spectrum, closed-immersion and subgroup-scheme definitions provide precisely the ring-map factorization criterion and interpretation as a represented subgroup functor. I checked both containments, the universal H_A point over A tensor O(H), and closure under multiplication/inverse. This checks the functor for arbitrary A and A', not only reduced tests or rational points. The identity lies in N, including in dimension zero.

For step 4 I opened the statement of lem-sfb-torus-centralizer-smooth-connected: its hypotheses are smooth geometrically connected G and any torus T; algebraic closedness makes connected G geometrically connected here. Its conclusion supplies the closed centralizer representing the same all-algebra functor. The new Lie node says exactly Lie(C)=g^T and n/h=(g/h)^H, as well as injectivity of tangent maps and stability of h. Smooth H is explicitly assumed in that node and in the item. T is contained in C because it is commutative on every algebra. No assertion about ordinary Lie-algebra invariants is used.

For step 5 I read lem-sfb-gm-representation-weight-basis, which is over any field, includes V=0, and supplies decomposition for a regular G_m action on a finite-dimensional space. Restrict the rational action furnished by the preceding node to successive coordinate factors. Commutativity preserves previously obtained weight spaces; the elementary induction on the finite rank is written out. For a stable subspace, the universal Laurent tuple and coefficient independence show that its weight components remain in the subspace. Thus I did not introduce another node duplicating the existing rank-one decomposition, nor use an uncited exactness-of-invariants theorem. Step 6 is the explicit quotient of those finite direct sums: its zero-weight quotient vanishes since h contains g^T. Restriction along T to H then forces the H-fixed subspace to vanish, and the displayed identity of step 4 gives n=h.

For step 7 the new tangent-dimension criterion applies to H and to N, both now known affine and finite type. H is smooth by hypothesis; no smoothness of N is assumed until equality in the dimension sandwich proves it. Monotonicity of topological dimension for a closed inclusion is the chain argument in the step, using the definitions cited. This is the place the converse direction of 1.37 is essential and cannot be replaced by the smooth-only existing Lie-dimension node.

For step 8 I opened all five cited statements. The translate-components node gives open/closed components and isomorphisms from the neutral component to each component; a chain lies in one member of a finite clopen decomposition, so their dimensions are exactly those used. The locally-algebraic neutral-component node gives geometric irreducibility and an integral reduced component. The affine-dimension-drop node explicitly allows any base field and applies to the reduced affine variety N^0_red, not just Q_lbar matrix groups; equal topological dimensions therefore force equality of supports. The smooth-geometrically-reduced node makes H and N reduced over F, and reducedness restricts to the open components. Clause (3) of the reduced-induced-closed-subscheme node identifies reduced closed structures with the same support. These last two citations ensure the conclusion is equality of subgroup schemes, not merely equality of their rational points or underlying topological components.

I tested the statements on H=G, G=T a torus, T of rank zero (then C_G(T)=G and H=G), and the trivial group, where both dimensions and both Lie spaces vanish. For the general tangent criterion, mu_p in characteristic p has dimension zero and a one-dimensional tangent space, so equality is correctly excluded and no false smoothness follows. Finite etale nonconnected groups have zero tangent space and dimension zero and are smooth, so the criterion does not force connectedness. In the Lie input H=1 gives n/h=g and invariants g, H=G gives zero quotient, and the centralizer K=1 gives g^K=g. Positive-characteristic nonzero weights divisible by p remain nontrivial Laurent monomials; the proof never differentiates characters to detect them. The source's broad group-scheme tests are preserved throughout.

I checked delivery-errors B–E with these statements open: new nodes have self-contained hypotheses, definitions and source places, statement only and empty proof lists; no missing non-elementary theorem is hidden in a citation to a definition; no statement was weakened; no new node restates an item clause; generic off-unit tools are declared in split_report.tool_uses. All proof steps are shorter than 2000 characters. The long-step extraction rule therefore lists none, and I also checked their content for hidden comparisons: the simultaneous-weight and quotient arguments are written explicitly from the cited rank-one theorem. There was no earlier delivered split or returned report in this sandbox to discard or repair.
