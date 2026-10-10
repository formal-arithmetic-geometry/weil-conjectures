1. Files written:

   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-source-morphism-separated.json` — item, Mathlib leaf; exact match by two Mathlib instances.

   - No new nodes.

2. Attachments: none.

3. WANTED: none.

4. The imported item was unsplit and had only a preliminary grep search. I checked its statement and source against Schemes Lemma Tags 01KN and 01KV. The statement is the affine-source separatedness assertion and its hypotheses are unchanged. Mathlib already states the result: `AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine` (Mathlib `AlgebraicGeometry/Morphisms/Separated.lean:354`) gives separatedness of an affine source scheme, and `AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated` (same file, lines 359–362) lifts source-scheme separatedness to any morphism. Thus no proof node or subsidiary node is needed.

5. I could not finish: nothing remains; the item is classified as a Mathlib leaf.

## Review by J1

I read the item node in `dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-source-morphism-separated.json`, the unit and chapter records, and the source metadata for Schemes Tags 01KN (affine schemes are separated) and 01KV (composition/separatedness permanence). I also read the relevant Mathlib source lines directly. The first instance requires exactly the item's affine-source hypothesis (`[IsAffine X]`) and concludes `X.IsSeparated`; the second requires exactly that source-scheme class and concludes `IsSeparated f`, so together they state the item with no extra hypotheses. LeanFinder returned both declarations, Loogle returned the affine instance, and a source grep found both declarations and their line numbers; LeanSearch was attempted but returned HTTP 500 and is recorded as unavailable. I searched the DAG and blueprint for the item/tag and found no duplicate statement. Since the item is a Mathlib leaf, it has no proof steps or citations; `citations.json` is therefore the empty list. The preliminary `status: unsplit`, single grep search, and null `mathlib_match` were corrected to the complete three-kind search record and the exact two-declaration Mathlib match.
