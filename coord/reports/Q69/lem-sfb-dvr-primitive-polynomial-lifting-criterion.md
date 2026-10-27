## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dvr-primitive-polynomial-lifting-criterion.json: item, split into five steps; no change of mathematical statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-dvr-rational-module-finite-free-cover.json: statement, unsplit; Mathlib searches found no equivariant finite free cover theorem for affine flat group schemes over a DVR.
- citations.json: a verbatim statement quotation for every use in every numbered proof step.

## Attachments

None. Searched lean/WeilConjectures for the item id, primitive invariant vectors, reductivity and comodules. The GeneralLinear/Representation file concerns field representations and does not state this DVR criterion. No Lean was written or compiled.

## Wanted literature

WANTED: literature/alper-adequate-moduli-spaces.pdf, Definition 9.2.2, Remarks 9.2.3--9.2.4(i), Lemma 9.2.5 and Remark 9.2.7, pp.521--523, for the item and lem-sfb-dvr-rational-module-finite-free-cover. Read the publisher's online PDF https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf without downloading it into the repository. The local PDF is absent, so the explicit assembly has proof_origin.by = agent. The approximation source is locally available: literature/stacks-project/groupoids.tex, Tag 07TU, lemma-colimit-coherent; read its full statement and proof.

## Problems found and corrected

The item was statement-only. Its intended finite-free-to-arbitrary reduction needed a genuine finite free equivariant cover, not a free module with an arbitrarily chosen basis and action. That input is now the sole new node. The existing groupoid approximation theorem already supplies the other non-elementary input, so the initially considered rational finite-submodule node was not created. In particular its statement only promises a filtered diagram, not inclusions; the proof uses an arbitrary cocone map and an element mapping to a chosen preimage of 1, and never asserts the cocone map is injective.

The blueprint ancestor command returns null: the inherited created.item chain has no imported ancestor. Kept null, the existing detailed route place, and its via list; the new node prepends the item. Read the latest 20261024 blueprint, sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). It does not state this subsidiary representation lemma. Searches of the full imported blueprint for resolution property, finite free representation, finite subrepresentation, primitive polynomial, 9.2.4 and 07TU found no duplicate.

## Source error

Alper Lemma 9.2.5(7-double-prime) and Remark 9.2.7 print an injective map R→V where the dual of a surjection V-dual→R requires a primitive vector. The unrestricted formulation is false even for the trivial group: A=k[[t]], V=A, v=t. Multiplication by t is injective, but every positive-degree homogeneous polynomial evaluates into (t), never to 1. This item already corrects that issue by requiring v outside the maximal-ideal multiple of V. No further correction to the item's statement is required. Step 4 obtains this exact primitivity from a surjection, rather than assuming every injection splits.

## Unfinished work

Only the new statement-only resolution lemma remains to be split by a later stage-1 worker, as required by the one-level split contract. Its source is the separate dimension-one resolution-property theorem, not the invariant-polynomial criterion itself.

## Not duplicates

lem-sfb-dvr-rational-module-finite-free-cover vs lem-sfb-dvr-comodule-finite-free-lattice: the existing node assumes the given module is torsion-free and produces a free stable submodule containing chosen elements. The new node allows torsion and produces an equivariant surjection onto the given finite module; it cannot be obtained by applying the torsion-free submodule statement to that module.

lem-sfb-dvr-rational-module-finite-free-cover vs lem-sfb-flat-noetherian-groupoid-coherent-approximation: coherent approximation gives finite modules mapping to an arbitrary module, without a freeness assertion or a surjection onto a prescribed finite module. The new node is the additional DVR resolution input, and the item cites both results separately.

lem-sfb-dvr-rational-module-finite-free-cover vs lem-sfb-dvr-primitive-polynomial-lifting-criterion: the new node has no invariant-polynomial hypothesis and no conclusion about symmetric powers or lifting invariants. The item still proves the duality, primitive-vector and symmetric-evaluation argument explicitly.

## Review by Q69

I read Alper's publisher PDF at Definition 9.2.2, Remark 9.2.3 and Remark 9.2.4(i), and checked the new statement against the dimension-one resolution property: Spec(A) for a DVR is affine, separated, regular, Noetherian of dimension one; H is affine, flat and finitely presented. Thus every finite rational module admits an equivariant finite locally free cover. On the local base this is finite free. The statement includes torsion N and does not impose reductivity or smoothness. These hypotheses distinguish it from the existing lattice lemma. The zero case is realized by P=0; for trivial H and N=A/(t), the quotient A→A/(t) checks that allowing torsion is necessary and consistent. For H=G_m, a finite sum of weight-module generators gives the expected equivariant free cover; no averaging or characteristic restriction is involved.

Step 1 uses the DVR definition for Noetherianity and the finite-type-over-Noetherian statement for H. I opened the full statement of the groupoid approximation node: it requires U,R Noetherian and both maps flat, quasi-compact and quasi-separated. Here R=H and both maps are its affine flat structure morphism. The cited statement supplies a small filtered diagram of coherent equivariant modules, not a union of free submodules.

Step 2 uses the Spec module-sheaf construction, the affine pullback tensor formula, and the coherent-affine-section finiteness theorem. I opened all three statements: they provide respectively the sheaf and its localized sections, the natural pullback identification M tensor B, and finite generation of sections. The Hopf formula and its antipode inverse are written out, so equivariance is a coaction condition on every algebra test, not just on A-valued points. The comparison does not require M flat. This is an elementary substitution in the coaction/groupoid definitions, not an additional claimed theorem.

Step 3 applies the approximation node and the groupoid limits/colimits node, whose statement explicitly says the forgetful functor computes small colimits. The Spec principal-open section theorem and the nested-affine tensor theorem reconstruct the associated sheaf/section correspondence by localizations; that gives the underlying module colimit. The filtered-colimit-modules-elementwise statement then gives an element of one finite section module mapping to a chosen m with lambda(m)=1. The coherent-affine-section node gives the finiteness needed for the new cover lemma. I checked that no monomorphism of transition or cocone maps was used. This is precisely why no torsion-free hypothesis was introduced on M.

Step 4 cites only the new cover statement, and uses exactly its equivariant surjection P→N. The composite to A is surjective. Its dual vector a in P-dual is invariant by the displayed contragredient formula. If a belonged to mP-dual, its value on every z would belong to m, contradicting a(z)=1. Thus the hypothesis of this item really applies. This also checks the rank-zero edge: a surjection to nonzero A forces P to have positive rank. The coaction duality is used only on P, which is finite free, never on arbitrary M.

Step 5 cites the symmetric-algebra universal-property and grading statements, opened in full. They provide extension of the linear map and the spanning products in degree n. The bidual isomorphism is given on basis elements and equivariance is verified by a formula; the two evaluation maps agree on every product, so on f by linearity. This does not identify Sym(P-dual) with the linear dual of Sym(P), which would be problematic in positive characteristic. The result has the same positive degree n and maps to exactly 1.

I checked B--E against the files: the new node is self-contained, has no proof or proof dependencies, uses inline coaction and finite-generation definitions, and cites definition nodes for the scheme and DVR notions. Its five Mathlib searches were actually run via msearch.py, their complete output retained, and a second semantic formulation tried. The hits about flat/free modules and affine schemes lack the rational coaction and equivariant-surjection conclusion; none is a leaf. The item's searches likewise do not state the criterion. Searches for 07TU found an existing adequate generalization, which was reused. The source-error example, arbitrary torsion M, trivial and diagonalizable groups, zero N, and preservation of n≥1 were checked. Every proof step is below 2000 characters and contains one explicit part of the assembly. There is no unit-route replacement, no SGA citation, no changed target, and no repository write. citations.json quotes the actual cited statements, not their proofs.

The first dry run rejected the phrase referring to the item in step 4 (B2). I replaced it by the explicit name of the assumed primitive-fixed-vector polynomial property; no argument or hypothesis changed.
