# Stage-1 report: lem-pur-supported-product-quotient-model

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-supported-product-quotient-model.json` — the item, split into seven proof steps; explicit correction of the uniqueness normalization. The Mathlib verdict is no match. No new nodes or Mathlib leaves.
- `citations.json` — one verbatim statement excerpt for every node cited by every proof step.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` found no item tag or declaration stating this quotient-to-pushforward comparison. The upstream checkout is reference material only; it was not treated as evidence of a finished proof.

## WANTED

None for this agent-written split. The item’s current blueprint source is present and was read. No external source was downloaded or introduced and no new node requires an additional source.

## Statement correction

STATEMENT-DISPUTED: normalization on ordinary modules alone does not imply uniqueness of a natural transformation of unbounded derived functors. For example take the etale site of an algebraically closed point, the identity closed immersion, and A = F_3. Both functors identify with the identity of D(F_3). Under the cohomology equivalence with graded vector spaces, multiplication by 2 on H^1 and by 1 on all other degrees is a natural automorphism that is the identity on every module in degree zero. Thus agreement of ordinary-module components does not determine the derived natural isomorphism. This alternative does not preserve the specified identity adjunction. I corrected the statement to require compatibility with the specified adjunctions, with identity on the common right adjoint, and identified the constructed isomorphism as the derived extension of the ordinary normalized isomorphism. This is the adjunction-preserving intent of the item’s title and last clause. The proof now establishes that precise uniqueness by injectivity of the adjunction bijection. No scheme hypothesis, coefficient restriction, or existence assertion was weakened.

## Other corrections and searches

The imported proof was empty. Its source points to paragraph 4 of `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-kunneth-supported.proof.md`. That paragraph transports supported products and counits through site comparison but does not write a quotient calculation. I read it, the ancestor node’s current proof, and the existing etale and pro-etale support-product definition statements. The supplied unit record is `sk-prop-a1-kummer`; I read it and the chapter record and retained all maintainer-owned bindings.

The first draft compressed tensoring the rank-one quotient and passage to derived categories too much. The final split replaces that compression with a functorial free-module presentation argument, an explicit application of K-flat preservation under constant ringed-topos pullback, and a Hom calculation on K-injectives. In particular an arbitrary coefficient module is not assumed flat, and no conservative system of geometric stalks is used on the pro-etale site.

I ran the required msearch.py searches: LeanFinder twice, Loogle (an invalid pattern followed by a valid replacement), grep twice, and LeanSearch. The exact query texts and returned log entries are in the item’s `mathlib_searches` and `searches.jsonl`. The inherited searches were retained. The hits are generic constant-sheaf, sheafification, module pullback, and scheme-module restriction adjunctions, not the closed-support comparison. I read the constant-sheaf definition and adjunction in Mathlib/CategoryTheory/Sites/ConstantSheaf.lean and the module-pullback source behind the hits. These interfaces do not constitute an attachment or an exact Mathlib match for this item.

## Not duplicates

No new node is created. I searched the entire DAG and blueprint for quotient support models, normalized closed pushforwards, open–closed exactness and constant tensor facts, and reused the existing nodes. The item’s nearest blueprint ancestor remains `lem-pur-kunneth-supported` via `lem-pur-support-site-comparison`; the searched `same_as` list remains empty.

## Review by Q57

For the item source I read the current blueprint paragraph 4 and the existing ancestor proof; for the needed pro-etale recollement interface I also read `sk-prop-sf-closed-unit/det-sf-open-closed-sequence-ring-sheaf.proof.md`. There is no new node whose source would need a separate review. The argument is marked `proof_origin.by = agent`, because the blueprint does not contain the full quotient argument.

Step 1 uses the statements that finite-type schemes over Noetherian bases are Noetherian and that opens of Noetherian schemes are Noetherian and quasi-compact. I verified that the base is the spectrum of a field, that X and Y are finite type and separated, that the finite product affine cover gives finite type for P, and that intersection with each affine open verifies quasi-compactness of each complementary open immersion. Separatedness, through the definition of the diagonal, supplies the ambient quasi-separatedness required by the pro-etale exact sequence. The affine diagonal equations for a product check the same property for P; no property of an arbitrary non-Noetherian scheme is assumed.

Step 2 cites the exact statements of `lem-weil-pbc-open-closed-short-exact` and `det-sf-open-closed-sequence-ring-sheaf`, including their specified unit and counit maps. Applying them to the rank-one constant ring module identifies the cokernel under its map from A_T. The normalized quotient maps in the two support-product definitions are those same units. The proof writes the two cokernel factorizations and cancels their epimorphisms, so it produces the normalized rank-one isomorphism rather than an unspecified isomorphism of sheaves.

Step 3 uses the tensor-Hom adjunction stated by `lem-pc-sheaf-modules-tensor-closed`, the constant-sheaf adjunction explicitly stated in the etale support definition (and its identical sheafification universal property in the other topology), and the two normalized C_a adjunctions stated by the support-product definitions. The exact statement of `lem-weil-pbc-left-adjoint-preserves-colimits` gives preservation of coproducts and cokernels. I checked the index sets are small in the item’s chosen module universe. The comparison on free modules commutes with each matrix column because it is a finite A-linear combination; no arbitrary infinite matrix sum is used.

Step 4 gives the free presentation, all its generators and relations, and the reason its kernel is generated by those relations. Functoriality makes the resulting isomorphism natural in every module, and the equality under the normalized quotient descends from generators. Tensoring the quotient is epimorphic by the same tensor-Hom adjunction from step 3. This is a written elementary cokernel argument using that cited interface; it does not hide a separate geometric projection formula. In particular it works for nonflat modules over a nonsemisimple finite ring.

Step 5 uses `lem-pc-kflat-resolution` with the one-point ringed site to obtain a flat-term K-flat A-module complex, and `lem-weil-pbc-ringed-pullback-preserves-kflat` to obtain the constant sheaf K-flat complex. The latter statement allows precisely a ringed-topos morphism with a constant coefficient structure map, with no scheme or ring flatness assumption. Both tensor definitions permit computing with the K-flat factor (using tensor symmetry). Exactness of C_a is explicitly in each support-product definition; `lem-weil-pbc-exact-functor-derived-factorization` consequently makes its termwise map on a quasi-isomorphism a quasi-isomorphism. I checked all complexes may be unbounded and that the cited statements are not merely D-plus results. The module comparison commutes with every differential by naturality, and with roofs by inversion of quasi-isomorphisms.

Step 6 reads the actual normalization clauses in both support-product definitions: their adjoints precomposed with e_a or q_a equal the constant adjoint followed by the inclusion of supported sections. That is exactly the ordinary Hom equality needed here. The termwise-adjunction node explicitly supplies the homotopy-category bijections. The K-injective preservation node applies because C_a is exact and its right adjoint is the ordinary support functor. The Hom-localization node applies to each K-injective target without boundedness restrictions. Therefore the Hom equality really descends to the derived adjunctions of the item, and the natural-bijection node gives the counit as the inverse image of the identity, proving the precise evaluation equality rather than appealing to an unspecified transport.

Step 7 proves uniqueness within the corrected, adjunction-preserving normalization by the injective Hom bijection. I tested the zero ring, empty support, full support and empty ambient scheme: the zero cases give zero functors with the unique comparison; full support gives the usual constant-sheaf/sections adjunction and its identity normalization. I tested the finite-ring nonflat coefficient case separately through the free presentation, where the proof uses right exactness rather than flatness. The F_3 point example above was the test that exposed the omitted derived uniqueness qualification. Every non-elementary input is the statement of a cited node, and the generic statements from other units are declared in `split_report.tool_uses`. No proof step exceeds 2000 characters.

I copied each citation excerpt directly from its node’s statement, preserving dollar delimiters and newlines, checked every excerpt is a literal substring and that the citation pairs equal exactly all step/node uses, and checked that `proof_deps` is their union. The first dry-run rejection concerned short or missing citation excerpts and was repaired. The subsequent dry run passed server preflight; a final dry run is run after this report and citation update.

## What could not be finished

Nothing remains unfinished at stage 1. No new statement obligation is deferred into another node. No Lean source was written and no compiler, Lake, or build tool was run.
