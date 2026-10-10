Files written:
- `dag/nodes/sec-curve-estimates/lem-exc-etale-field-gsets.json` (repaired item, split)
- `dag/nodes/sec-curve-estimates/lem-exc-etale-field-galois-classification.json` (strengthened statement-only node)
- `dag/nodes/sec-curve-estimates/lem-exc-etale-coproduct-etale.json` (new statement-only node, Mathlib no match)
- `citations.json`

Attachments:
- None. I searched the slopmaster2 source for the item id, its title, and the finite-etale equivalence declarations; no sorry-free declaration states this item exactly.

WANTED:
- None.

What was wrong and repaired:
- Deleted `lem-exc-etale-field-decomposition`, because it duplicated the existing `lem-weil-pbc-etale-fibre-discrete-separable-points` (specialized to `S=Spec K`).
- Deleted `lem-exc-etale-field-cover-detection`, because it merely restated the item's covering clause. Step 4 now gives the two directions directly, using geometric-point lifting, the existing fibre lemma, and the small-etale-site definition.
- Corrected the route to Tags 03QR and 03QS with Morphisms Tag 02GL; removed the incorrect 04HF/03SF proof-origin route.
- Added to the Galois classification the exact full-faithfulness bijection required by step 2 and replaced the ambiguous “inclusion” stabilizer phrase by the K-embedding formula `Gal(K^sep/sigma(L))`.
- Added the missing statement-only node `lem-exc-etale-coproduct-etale` for the etaleness of the coproduct in step 3. Each component uses the existing finite-separable-extension-etale leaf, and the fixed field `L_s=(K^sep)^{G_s}` is explicit.
- Restored the item's `stmt_deps` to the two definitions used in its statement; all theorem nodes occur only in `proof_deps`.
- Added `created.by` and `created.date` metadata where needed and rewrote all citation quotes to be verbatim substrings of the cited statements.

## Review by G1

I reread the item's source route in Pione Tag 03QR (Lemma `lemma-sheaves-point`) and Remark 03QS, and the Morphisms source for Tag 02GL. Step 1 uses the existing fibre-discrete-separable-points statement with `S=Spec K` for the finite separable component decomposition, and the strengthened classification statement for the open stabilizer; both statements say exactly those facts. Step 2 uses the same component decomposition and the new classification clause giving the bijection between K-morphisms of finite spectra and equivariant maps; I also wrote the elementary connected-component/orbit reduction explicitly. Step 3 uses the classification converse, the existing finite-separable-extension-etale statement, and the new coproduct-etale statement; the field is explicitly `L_s=(K^sep)^{G_s}`. Step 4 was rewritten as an argument: the forward direction cites geometric-point lifting, while the converse uses the existing fibre lemma to obtain finite separable residue fields and then the definition of a jointly-surjective covering in the small etale site.

For the new coproduct node I searched the whole DAG and blueprint, then recorded LeanSearch, LeanFinder, and Mathlib grep searches; no Mathlib theorem combines arbitrary coproducts with etaleness. I tested the repaired statements on the empty coproduct/empty G-set, a separably closed base field (trivial G), and a finite Galois extension (orbit `G/Gal(K^sep/L)`). I checked that every `uses` entry appears in `proof_deps`, every citation quote is verbatim, all new nodes have complete creation metadata, and the item statement dependencies contain only `def-pc-field-extension` and `def-weil-etale-morphism`.

What could not be finished:
- No Lean implementation is required for this natural-language stage-1 item.
