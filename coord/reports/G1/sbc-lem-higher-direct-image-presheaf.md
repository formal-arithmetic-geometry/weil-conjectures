Files written: item `sbc-lem-higher-direct-image-presheaf` (split, 0 new nodes; Mathlib searches found no direct-image theorem).

Attachments: none.

WANTED: none.

The imported proof was only a sentence. I expanded it into the Stacks 03Q8/072W site argument and recorded the existing unrestricted site theorem and existing derived-complex theorem as dependencies. No new node was created because both ingredients already exist in the DAG. The derived-complex dependency is stated for qcqs morphisms; the source 03Q8 proof is the generic morphism-of-sites calculation, so the report flags this hypothesis transfer for the second reader.

## Review by G1

I read the target blueprint entry and the source declaration/docstring tagged `sbc-lem-higher-direct-image-presheaf` in `HigherDirectImage.lean`. I also read the full statements of `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf` (Stacks 072W) and `lem-weil-pbc-qcqs-higher-direct-image`. Step 1 uses the former's explicit identification of the higher direct image with the sheafification of the cohomology presheaf, together with the etale cohomology definition. Step 2 uses the latter's K-injective derived-complex description and the direct-image section formula. Step 3 uses the sheafification identification and exactness to pass from sectionwise cohomology to the cohomology sheaf. I checked that each cited node exists and that its quoted statement supplies the stated operation. The small cases q=0 and h an identity reduce to ordinary pushforward and local cohomology, respectively. Mathlib searches (LeanFinder, Loogle, grep) found only generic sheafification declarations and no higher-direct-image result.

## Second reading by G1

- Statement: checked against Stacks etale-cohomology.tex, Lemma 03Q8 (line 7510); the fibre-product orientation and both sheaf/complex clauses agree. The project uses its bounded-below derived direct-image interface for the complex clause.
- Step 1: checked against the full statement of `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf` and `def-weil-pbc-etale-cohomology`; verdict correct.
- Step 2: checked against `def-weil-pbc-direct-image`, `def-weil-pbc-kinjective-resolutions`, and the Stacks 072W proof; verdict repaired. The prior citation of the qcqs theorem was invalid because the item has no qcqs hypothesis.
- Step 3: checked against `lem-weil-pbc-sheafification-exact`, `lem-weil-pbc-exact-functor-complex-cohomology`, and the 072W cohomology-sheaf paragraph; verdict correct after repair.
- New nodes: none; no new-node statement or Mathlib leaf required.
- Mathlib searches: LeanFinder, Loogle, and grep were rerun with broader direct-image/cohomology queries; no exact theorem was found.

Changes: removed the unjustified qcqs tool citation, added the K-injective and exact-sheafification dependencies, corrected blueprint metadata (`same_as = []`), and rewrote the derived-complex step from the direct-image definition.
