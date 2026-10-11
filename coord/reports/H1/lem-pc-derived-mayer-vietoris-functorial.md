Files written:

- `lem-pc-derived-mayer-vietoris-functorial.json`: repaired statement and proof split.
- `lem-pc-derived-functor-termwise-split-ses-triangle.json`: new unsplit statement-only auxiliary node.
- `citations.json`: updated verbatim citations.

Attachments: none.

WANTED: none.

The returned version incorrectly allowed an arbitrary K-injective complex in the Mayer--Vietoris boundary definition, although the right exactness argument requires injective terms. I corrected the item to require a K-injective resolution with injective terms, citing `prop-pur-kinjective-resolutions-exist`, and added the restriction theorem needed to identify the derived direct-image terms. I also added a genuine statement-only node for the missing fact that a right derived functor identifies the triangle of a termwise split short exact sequence of K-injective complexes with the triangle of the image sequence. For direct image, the proof now chooses a K-injective replacement `h_*I' -> J`; it no longer treats `h_*I'` as K-injective.

## Review by H1

I read the returned item, the Tag 08BV Mayer--Vietoris construction, Tag 0D5T composition/restriction comparison, and the existing statements for K-injective resolutions, restriction to opens, derived direct-image composition, and triangulated right derived functors. Step 1 now explicitly uses a K-injective complex with injective terms and verifies that restrictions remain K-injective before invoking short-exact-sequence naturality. Step 2 introduces a K-injective target `J` and a quasi-isomorphism from `h_*I'`; the component identifications use composition and open-restriction statements only after restricting the source complex. Step 3 records that the sequence is degreewise split because the terms are injective and cites the new statement-only node for the derived-functor image of its connecting triangle, then uses the existing naturality statement for the comparison morphism.

The new node is statement-only as required. I searched the DAG and blueprint for an existing termwise-split derived-functor triangle statement; none exists. LeanFinder, Loogle, grep, and LeanSearch searches were run for that node; LeanSearch was unavailable and is recorded as such. The small edge cases remain consistent: identity `h` gives the identity comparison, and an empty intersection gives the zero third term. The four reviewer points are addressed directly: injective terms are now a hypothesis; the missing image-triangle fact is a cited child node; `h_*I'` is replaced by `J`; and restriction of K-injectives is cited wherever the derived-direct-image model is identified.

## Not duplicates

lem-pc-derived-functor-termwise-split-ses-triangle vs lem-weil-pbc-exact-functor-ses-triangle-image: the existing node treats a short exact sequence of objects under an exact termwise functor; the new node treats a degreewise split short exact sequence of complexes under a generally non-exact right derived functor and identifies its connecting morphism.
lem-pc-derived-functor-termwise-split-ses-triangle vs lem-weil-pbc-complex-ses-triangle: the existing node only constructs and states naturality of the triangle in one derived category; the new node compares that triangle with the image sequence under a right derived functor.
lem-pc-derived-functor-termwise-split-ses-triangle vs lem-sf-derived-ses-triangle: the existing node concerns complexes concentrated in degree zero, while the new node concerns arbitrary K-injective cochain complexes and their termwise split sequences.

## Second reading by H1

- Item statement: checked against Stacks Tag 08BV and the relative comparison in Tag 0DJ9; the qcqs, quasi-compact-open, K-injective-with-injective-terms, and derived-category hypotheses are all present, and the identity and empty-intersection cases have the expected identity and zero terms.
- Step 1: checked the representative, restriction, and short-exact-sequence naturality claims against `prop-pur-kinjective-resolutions-exist`, `lem-sc-derived-k-injective-restrict-open`, `lem-sc-kinjective-quasi-iso-comparison`, and `lem-weil-pbc-complex-ses-triangle`; the restriction of the chain map supplies all three component maps and the boundary square.
- Step 2: checked against Tag 0DJ9 and the statements of `lem-pc-right-derived-functor-triangulated`, `lem-pc-derived-direct-image-composition`, `lem-pc-restrict-derived-direct-image-open`, and the K-injective restriction lemma; the target replacement is `J`, so no claim that `h_*I'` is K-injective is used.
- Step 3: checked the degreewise split sequence and the connecting-map comparison against Tag 08BV/0D5T and the new termwise-split derived-functor node; the cited node supplies precisely the image-triangle identification, while the existing short-exact triangle node supplies naturality.
- New node `lem-pc-derived-functor-termwise-split-ses-triangle`: statement-only, self-contained, definitions cited for every category/complex/functor notion, source given by document and lemma, and Mathlib searches recorded in `searches.jsonl`; it is strictly smaller than the item and not a duplicate of the existing exact-functor or complex-triangle nodes.

Changes made in this second reading: no mathematical edits were required after checking the corrected injective-term hypothesis, the `J` replacement in the direct-image step, and the added auxiliary image-triangle statement. The report was extended with this audit so the source, hypotheses, dependencies, edge cases, and non-duplication checks are explicit.
