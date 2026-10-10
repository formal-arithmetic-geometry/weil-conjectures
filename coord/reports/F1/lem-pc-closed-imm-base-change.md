# lem-pc-closed-imm-base-change

Files written: dag/nodes/sec-picard-framework/lem-pc-closed-imm-base-change.json (item split; no new nodes, no Mathlib leaves).

Attachments: none. The slopmaster2 docstring mentions this item at WeilConjectures/AlgebraicGeometry/Modules/Ample.lean:447, but IsVeryAmple.pullback_of_field at lines 448-453 has sorry and concerns very ampleness, not the complete statement of this item. Searches of the source for the tag and the closed-immersion/ideal terminology found no sorry-free declaration stating this item exactly.

WANTED: literature/stacks-project/schemes.tex, tags 01JU and 01JY, for this item. The checkout has no populated literature/stacks-project/; I read the official Stacks tag pages instead.

WANTED: literature/stacks-project/modules.tex, tag 02N4, for the flat-pullback step; and literature/stacks-project/morphisms.tex, tag 01U9, for the field-extension step. I read their official tag pages.

The imported node already had the maintainer's corrected image-form statement, but its proof still concluded the false equality for arbitrary base change. I replaced that proof. I also made the final specialization precise: it concerns a closed \(k\)-rational point and an extension \(K/k\), not an unspecified \(\kappa(x)\)-point. The blueprint markdown was not installed locally, so its imported statement and proof in the item were the blueprint text available for comparison. No part remains unfinished.

## Source error

The blueprint's argument says right exactness gives \(\mathcal I_{Z'}=g^*\mathcal I_Z\) for every \(g\). Take \(X=\operatorname{Spec}k[t]\), \(Z=V(t)\), and \(g:Z\to X\). Then \(Z'=Z\), its ideal in \(Z\) is zero, while \(g^*(t)\cong k\) as a module. Stacks 01JU (1) says the ideal is the image of the pullback map; 01JY only gives stability of the closed immersion. The repaired statement adds flatness to the equality claim.

## Review by F1

I read the item's imported blueprint statement and proof and the official Stacks pages for Schemes 01JU (lemma-fibre-product-immersion, part (1)), Schemes 01JY (lemma-base-change-immersion), Modules 02N4 (lemma-pullback-flat), and Morphisms 01U9 (lemma-base-change-flat). The item's three clauses match them: 01JU gives both the closed immersion and the image ideal; 02N4 makes the ideal inclusion remain injective for flat \(g\); 01U9 applies after \(K/k\) is flat. No new node was needed or written.

In step 1, lem-weil-pbc-closed-immersion-base-change gives the closed immersion; lem-weil-pbc-closed-immersion-affine-cover-criterion and def-sbc-closed-immersion-ideal-sheaf give \(Z|_U=\operatorname{Spec}(A/I)\) and its ideal \(I\). The open-fibre-product and affine-spectra Mathlib leaves give \(Z'|_V=\operatorname{Spec}((A/I)\otimes_A B)=\operatorname{Spec}(B/IB)\). From the sheaf-tensor definition of module pullback I wrote the affine map \(I\otimes_A B\to B\) explicitly; its image is \(IB\), which is the ideal of that quotient. The affine opens \(V\) cover \(X'\), so the local equalities glue. This derives the first clause of Stacks 01JU (1) without relying on the unsplit node from another unit that restates it.

In step 2, lem-weil-pbc-flat-morphism-affine-criterion says precisely that \(A\to B\) on such affine pairs is flat. The Mathlib leaf lem-weil-pbc-flat-tensor-exact then preserves the inclusion \(I\hookrightarrow A\) under tensoring with \(B\). Combined with step 1's calculation of the image, this proves that \(g^*\mathcal I_Z\) is the ideal itself. The algebraic identity \(B\otimes_A A/I=B/IB\) and the gluing of equal subsheaves on an open cover are the elementary parts.

In step 3, the Mathlib leaves lem-weil-pbc-module-over-field-flat and lem-weil-pbc-flat-ring-map-iff-flat-affine give flatness of \(\operatorname{Spec}K\to\operatorname{Spec}k\). The Mathlib leaf lem-weil-pbc-flat-morphism-base-change gives flatness of its pullback \(g:X_K\to X\). The fibre-product definition identifies the base change of the closed \(k\)-point with \(x_K:\operatorname{Spec}K\to X_K\); step 2 then applies. I checked the hypotheses explicitly: \(i=x\) is required to be a closed immersion, \(K/k\) is a field extension, and \(g\) is flat. Merely being an unspecified point would not justify the claimed \(\operatorname{Spec}K\) description.

The statement now introduces all objects, names the nodes defining closed immersion, ideal sheaf, fibre product, module pullback, flatness, field extension and base change, and uses JSON TeX escapes once. Searches across dag/nodes and tools/blueprint_refs.py search found the existing ideal-image node and the Mathlib leaves used in the direct proof; the only blueprint node with this full statement was the item itself, so same_as is empty. No new unsplit statement needs a Mathlib search or small-case test. I tested the arbitrary-base-change clause on the nonflat \(k[t]\to k\) example above and the flat clause on the identity map and a field extension. The edit corrects the false proof sentence and the ambiguous point clause; no earlier review return was supplied. The first dry run rejected cross-unit proof citations; I rewrote the steps using the affine computation and Mathlib leaves, leaving the statement unchanged.
