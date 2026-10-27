# Worker report: lem-trf-ml-quotient-product-vanishing

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ml-quotient-product-vanishing.json`: existing statement node, now split; statement unchanged. No exact Mathlib match.
- `citations.json`: verbatim statement quotes for all four step/node citation pairs.
- `report.md`: this report.
- `searches.jsonl`: five searches logged by the mandatory msearch command; inherited item searches retained separately in its JSON.

No new nodes, no new Mathlib leaves, no unit changes, no Lean files or compiler calls.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint id, Mittag-Leffler terminology and quotient-product terminology. The hits concern inverse towers, ideal-power completions, or specific local-factor quotients, not the tensor-comparison condition for an arbitrary Mittag-Leffler module and arbitrary family of submodules. In particular `ModuleCat.limit_flat_of_flat_quotients` in `RingTheory/LimitFlatModules.lean` needs a noetherian ring and a countable ideal-power quotient tower, and does not state this item. There is no declaration with the item's blueprint tag.

## WANTED

None. Both Stacks sources and the latest blueprint were available locally.

## Corrections and unresolved issues

The unsplit node had no proof. Its statement is correct as written, including the absence of flatness. I added the tensor-order identification explicitly because the existing Mittag-Leffler definition places M on the left, whereas beta places M on the right. I also expanded the coordinate calculation using individually chosen lifts; no simultaneous or compatible lifts are required. I preserved the source, chapter, unit, provenance and all inherited search records. Nothing remains unfinished in this split.

## Sources, searches and route

Read `literature/stacks-project/algebra.tex`, `lemma-minimal-contains` (Tag 0AS6), including its proof, and `proposition-ML-tensor` (Tag 059M), statement and the start of its proof. Verified both tag-label pairs against `literature/stacks-project/tags/tags`. The present item is exactly the elementary implication between the first two displayed maps in the proof of 0AS6. The later flat-kernel assertion of 0AS6 belongs to a different auxiliary and is not used here.

Read the chapter `sec-trace-formula` and unit `sk-i-curve-zero` records, and the latest blueprint file `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`. This is supporting algebra in the inherited projectivity/flatification branch below that blueprint node, not a replacement of its local-term proof. Read the parent `lem-trf-flat-ml-minimal-support`, whose Step 2 uses precisely this implication. The blueprint ancestor command confirmed `lem-trf-local-term-locality`; whole-blueprint searches for `Mittag` (only an inverse-system vanishing node) and `quotient-product` (none) found no equivalent blueprint statement.

All five fresh Mathlib searches were executed through the required msearch command and their results read. LeanFinder was tried with two different phrasings. Loogle and the Mathlib grep found `TensorProduct.piRightHom`; I read `LinearAlgebra/TensorProduct/Pi.lean` lines 34-105: the arbitrary comparison is defined at line 56 but the isomorphism `piRight` assumes Fintype. LeanSearch found `tensorQuotientEquiv` and `quotientTensorEquiv`; I read their actual statements at lines 105 and 131 of `TensorProduct/Quotient.lean`. These concern an individual quotient, not injectivity into an arbitrary product. The LeanFinder hits concern submodule-inclusion tensors, equational vanishing, flatness or completion, not the item. Read the vanishing definitions in `TensorProduct/Vanishing.lean` to distinguish that unrelated condition. No service was recorded as unavailable or as giving a match when it did not. The inherited searches remain intact.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to justify. The DAG search for Tag 0AS6 found the item, its parent, the flat finite-lift auxiliary and the flat Mittag-Leffler criterion. Those are distinct already-existing facts and none is recreated. Tensor symmetry, componentwise product operations and the composite identity are proved directly from the cited universal property and tensor functoriality rather than made into unnecessary nodes.

## Review by Q63

I reviewed the statement against the actual two displays and their intervening sentence in Stacks 0AS6. The source assumes flatness because it next identifies a tensor kernel with the tensor of an intersection, but neither the product comparison nor the implication isolated here uses that identification. The item's image formulation therefore works without flatness and avoids treating tensoring a submodule inclusion as an inclusion.

For Step 1 I opened `def-weil-pbc-module-tensor-product` and checked that its statement supplies the universal property and generation by pure tensors. It therefore justifies constructing the swap from the reversed bilinear map. The two composites fix each pure generator, so their identity assertions are immediate from that same statement. Commutativity is an explicit hypothesis of the item and ensures the reversed map is balanced. No uncited symmetry or coherence theorem is assumed.

For Step 2 I opened `def-trf-mittag-leffler-module`: it states injectivity for every set and every family of modules, with M in the left tensor factor. Each E/N_j is an R-module and J is a set, so this applies to precisely the required family. I then checked the displayed factorization on a pure tensor; generation from the tensor-definition node proves equality of maps. Each swap is invertible by Step 1 and the product inverse is literally its coordinatewise inverse. This proves injectivity in the right tensor order. Both cited statements say exactly what is used, and the other assertions are explicit universal-property or component calculations.

For Step 3 the tensor-definition node explicitly states preservation of zero, composition and identities for f tensor id. The quotient map kills the inclusion of its own submodule. The support hypothesis supplies a preimage for each fixed j, and applying the composite tensor map gives zero in that coordinate. Evaluating beta after q tensor id on pure generators identifies the coordinate as p_j tensor id. Product equality is componentwise; Step 2 then gives the conclusion. No right-exactness, flatness, tensor preservation of monomorphisms, or selection of a common lift is hidden here. All four citation pairs have full verbatim statement quotes in citations.json, so C4 is checked at the actual statements rather than proofs of the dependencies.

I tested J empty: P is the zero module, the target product is zero, the swap factorization and the vacuous coordinate argument still work. For a singleton family the proof reduces to p_j i_j = 0. With every N_j = E, P is zero; with N_j = 0 for any j, the hypothesis forces x = 0 because that support source is zero. Zero E, zero M and the zero ring cause no exception. A nonflat finite presented Mittag-Leffler module such as Z/2 over Z is also covered: the proof never requires the tensor of an inclusion to be injective.

Against B--E: there are no new statement-only nodes needing sources or novelty checks; the item introduces all objects, its two definition dependencies state the notions used, and the TeX is singly escaped in the decoded JSON. The proof is a calculation, not a relabelled clause or a citation to a tag in place of a proof. Every nontrivial input is a cited definition, with the elementary calculations fully written. There are no new edges outside the existing statement dependencies and no cycles can be introduced by the proof. The longest step is under 700 characters, so no long-step extraction is needed. There is no statement dispute, source correction or unreported hypothesis. The required server dry run is the remaining mechanical check before delivery.
