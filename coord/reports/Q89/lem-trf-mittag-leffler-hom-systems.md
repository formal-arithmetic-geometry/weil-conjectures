# Stage-1 delivery: lem-trf-mittag-leffler-hom-systems

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-mittag-leffler-hom-systems.json`: item, split into six proof steps; statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-finite-presentation-tensor-products.json`: statement-only supporting lemma, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and grep.
- `dag/nodes/sec-trace-formula/lem-trf-tensor-kernel-factorization.json`: statement-only supporting lemma, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and grep.
- `citations.json`: ten entries, one exact statement quote for every step/node citation.
- `searches.jsonl`: command-generated search results, retained verbatim. `write_delivery.py` is a sandbox-only preparation script.

Two new nodes, zero new Mathlib leaves. Existing Mathlib leaves are reused, not redelivered. No unit or chapter file is changed.

## Attachments

None. Searches of the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint id, Mittag/059M/059E/059X, piRightHom, domination, tensor kernels and splitting produced no project declaration stating the item or either new lemma. The upstream master reference likewise supplies no attachment. The unrelated upstream names for exactness of inverse limits do not state this module tensor-to-Hom bridge.

## WANTED

None: all mathematical sources used are locally available in `literature/stacks-project/algebra.tex`.

## Corrections and scope

The imported item had a correct statement but no proof. I retained all its hypotheses and its conclusion, including arbitrary small nonempty directed posets and arbitrary target modules N. Its inherited search results remain in place, and fresh Q89 searches were added. No STATEMENT-DISPUTED correction was necessary.

The direct-delivery brief supersedes the standing second-reader requirement. No agent was started, no Lean file was written, no compiler or Lake tool was run, and no shared repository or launcher was written. Blueprint ancestry and the unit binding were preserved; this is a supporting algebra argument below the already assigned unit, not a replacement of a unit step. The current main blueprint ancestor text was read; the inherited semistable-alteration ancestry is historical, while the immediate mathematical use is explicitly the sentence about Hom systems in Stacks Tag 059X.

## Source reading and the argument

The item follows Tag 059M (`proposition-ML-tensor`), proof of (2) implies (1), and Tag 059E (`proposition-ML-characterization`), (2) implies (3) implies (4). I read their full statements and these proof directions. I also read Tag 059L (`lemma-kernel-tensored-fp`): because the system in our item is already supplied, one can kill the universal kernel element at a stage of that very system using the existing tensor-colimit and zero-detection leaves. This removes the need for a separate new factorization-through-a-colimit lemma.

The first new node states exactly the forward implication of Tag 059K (`proposition-fp-tensor`). Its proof in the source uses a finite free presentation and tensor right exactness. This is a real general algebraic input; merely constructing `TensorProduct.piRightHom` is insufficient, and Mathlib's `piRight` assumes the PRODUCT INDEX finite. Our product index is an arbitrary set. I read `TensorProduct/Pi.lean:46-110` and `Algebra/Module/FinitePresentation.lean:292-360` to reject those candidate matches.

The second new node is the single factorization criterion obtained from Tag 059C (`lemma-domination-fp`) and Tag 059D (`lemma-domination`). I read both, and also the intermediate pushout lemma Tag 0AUM. Tag 059C says finitely presented tensor tests suffice; Tag 059D requires the cokernel of f finitely presented, and its conclusion is g = h f. Both directions and the orientation of the inclusion were checked. This node has no Mittag-Leffler module, colimit or inverse system in its hypotheses or conclusion, so it is not a renaming of a clause of the item. Its internal proof is left for its own future split, rather than inserted into its statement.

## Review by Q89

I reviewed every proof step against its sources and all seven distinct cited node statements, opened in full. The citations file copies the actual statements, not substitutes for missing assertions.

1. Step 1 uses only `def-sc-finitely-presented-module` to make a set of actual test modules: all finite matrices over R, with their quotient modules. Every finite presentation gives one of these quotients. Matrices and the pairs (t,z) form sets; this avoids a product over the class of all modules. The finite-matrix construction is written out and is elementary from the definition, so it does not become an artificial new node.
2. Step 2 uses `lem-trf-finite-presentation-tensor-products` only for the finitely presented source M_i, and `def-trf-mittag-leffler-module` only for injectivity of the comparison for M and the selected family. The latter definition really gives injectivity for every set-indexed family. `def-weil-pbc-module-tensor-product` supplies pure-tensor generation, induced maps and functoriality; checking a pure tensor proves the square commutes. I checked that no flatness of M or Q_alpha is being smuggled into the argument.
3. Step 3 uses `lem-weil-pbc-tensor-commutes-with-colimits` for the original colimit cocone with the fixed module T, not for a different or large index category. Its statement explicitly identifies the cocone maps u_s tensor identity and its transition maps. `lem-weil-pbc-filtered-colimit-modules-elementwise` then explicitly gives a later index j killing an element with zero colimit image. I checked the directed-poset clause in that statement and the source Tags 00DD and 00D7. Tensor functoriality from the definition supplies projection and isomorphism transport, with the identities on pure tensors written down. Every pair (t,v) appears among the coordinates, so the resulting j is uniform for all finitely presented test modules.
4. Step 4 uses only tensor functoriality and the finite-presentation definition. The identity u_i = u_k f_ik gives the first kernel inclusion in the correct direction. The finite presentation of the cokernel is not asserted for free: choose generators of M_i, lift their f_ik-images through a finite free presentation of M_k, and append these finitely many columns to its relation matrix. The quotient by precisely that image is M_k/f_ik(M_i). This two-line finite-presentation argument is elementary and is kept as a step rather than a new node.
5. Step 5 applies the new tensor-kernel factorization lemma with f = f_ik and g = f_ij. Its finite-cokernel hypothesis and its universal finite-test hypothesis were both verified in step 4; its statement really supplies h_k: M_k to M_j with f_ij = h_k f_ik. In particular the index chosen in step 3 is unchanged.
6. Step 6 is elementary composition of linear maps. For the less immediate image inclusion I explicitly compose a: M_j to N with h_k; the reverse inclusion composes b: M_k to N with f_jk. This gives equality of the actual precomposition images, and uses no finite-generation or countability assumption on N or I.

I checked delivery-errors B through E point by point: new statements introduce all objects and their finiteness conditions; source tags and labels were verified in `tags/tags`; new nodes have no proof or proof dependencies; new blueprint from/via fields point through this item; no supplied definition node is used as a theorem; no lemma is cited only for something in its proof; no cycle is introduced (the two new statements depend only on existing definition leaves). All proof steps are below 2000 characters, and the non-elementary inputs in the source are represented by cited statements. Existing tensor and colimit leaves are generic tools, both already Mathlib, so no off-unit non-leaf tool use is needed. No SGA source is used.

Small cases checked: over the zero ring all modules and maps in question are zero and the argument still works. For a singleton directed set, j=i and the two Hom images coincide. If M_i=0 or N=0, the asserted images are zero. No transition map is assumed injective or surjective. The test product can be infinite; that is exactly why finite PRODUCT-index tensor equivalences do not suffice. For the product lemma, P=0 and an empty family both give maps between zero modules; P=R gives the familiar identity comparison. For the factorization lemma, f=0 forces g=0 by testing Q=R, f=id gives h=g, and the test f=2:Z to Z, g=id is rejected by Q=Z/2, as it must be. In particular I did not reverse the kernel inclusion. The explicit cokernel presentation also works when its generator or relation list is empty.

## Not duplicates

No existing node uses Tags 059K, 059C or 059D for these module statements. Searches of the full DAG and `blueprint_refs.py search` by those tags, domination, tensor kernel, finitely presented modules and tensor products found no existing statement of either new node. The representative and cokernel statements found in sec-proper-base-change concern module SHEAVES; they do not state these tensor comparisons or factorization criteria. The existing colimit leaves were reused instead of duplicated. `def-trf-mittag-leffler-module` only defines injectivity for M and does not assert the finite-presentation comparison theorem. `lem-trf-ml-countable-colimit` adds countable generation and concludes countable extraction, not the present bridge.

## Unfinished

None for this one-level split. The two new supporting lemmas are intentionally statement-only items for subsequent stage-1 work.

## Validation

The required server dry run passed: `deliver.py Q89 lem-trf-mittag-leffler-hom-systems --no-push` exited 0 and printed `OK (not pushed) ... preflight passed`. This includes server preflight, DAG validation and split review. The delivery command performs the final push after validation.
