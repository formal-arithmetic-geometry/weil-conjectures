1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-kflat-tensor-cone-two-out-of-three.json`: split item; two proof steps.
- `dag/nodes/sec-picard-framework/lem-pc-tensor-mapping-cone-iso.json`: statement, Mathlib leaf `CochainComplex.mappingCone.mapHomologicalComplexIso`.
- `dag/nodes/sec-picard-framework/lem-pc-acyclic-triangle-two-out-of-three.json`: statement, Mathlib leaf `HomotopyCategory.instIsTriangulatedIntUpSubcategoryAcyclic`.
- `citations.json`: verbatim statement quotes for every cited node in every step.

2. Attachments: none.

3. WANTED: none.

4. What was wrong or incomplete: the imported item had no proof and its previous Mathlib grep record incorrectly said that mapping cones had no Mathlib support. The searches show the precise cone comparison and acyclic triangulated-subcategory declarations. The nearby K-flat closure node already depends on this item, so it was not cited; doing so would be circular.

5. What I could not finish: no remaining split work.

## Not duplicates

`lem-pc-tensor-mapping-cone-iso` vs `lem-pc-kflat-cone-direct-sum`: the former is the general additive-functor cone comparison; the latter asserts closure of K-flat complexes under direct sums and cones.

`lem-pc-acyclic-triangle-two-out-of-three` vs `lem-sf-triangle-two-out-of-three`: the former concerns acyclic objects in the homotopy category; the latter concerns a natural transformation of exact functors being an isomorphism on a third triangle term.

`lem-pc-acyclic-triangle-two-out-of-three` vs `lem-pc-kflat-tensor-cone-two-out-of-three`: the new node is the general homotopy-category triangulated-subcategory fact, while the item specializes it after tensoring a particular cone by an acyclic sheaf complex.

`lem-pc-tensor-mapping-cone-iso` vs `lem-pc-kflat-tensor-cone-two-out-of-three`: the new node is the general additive-functor comparison isomorphism, while the item applies it to the sheaf tensor total-complex functor and also concludes acyclicity.

`lem-pc-tensor-mapping-cone-iso` vs `def-pc-acyclic-complex-modules`: the new node is a theorem about mapping cones under additive functors; the existing node is only the definition of an acyclic sheaf complex.

`lem-pc-tensor-mapping-cone-iso` vs `def-pc-kflat-complex`: the new node is a theorem about mapping cones under additive functors; the existing node defines K-flatness by testing tensor products against acyclic complexes.

## Review by F1

I read the item source entry for Stacks Cohomology Lemma 07A3 and the imported proof context in `lem-pc-kflat-cone-direct-sum`. I also read the Mathlib source for `CochainComplex.mappingCone.mapHomologicalComplexIso` (MappingCone.lean, lines 641-643) and `HomotopyCategory.instIsTriangulatedIntUpSubcategoryAcyclic` (Acyclic.lean, lines 40-43). The new node statements match those declarations: the first gives the cone comparison under an additive functor, and the second gives triangulated closure of acyclic complexes, hence two-out-of-three.

Step 1 uses the tensor-complex definition for the signed total differential and the cone-comparison leaf for the identification of the tensor of the cone with the cone of the tensor map. Step 2 uses the acyclic-complex definition, the abstract distinguished-triangle notion, the cone-comparison leaf from Step 1, and the acyclic triangulated-subcategory leaf; each cited statement supplies the fact named in that step. I checked that the item hypotheses provide a site, a sheaf of commutative rings, an acyclic complex, and a morphism with its mapping cone, and that the two-out-of-three conclusion is applied only to the resulting distinguished triangle. I corrected the stale imported Mathlib no-hit assertion, added the exact cone and acyclicity leaves, and marked the item split.

Mathlib searches were run for the item and both new nodes with LeanFinder, Loogle, and source grep. LeanSearch was unavailable for the item and is not used as evidence of a match. Small edge cases checked: a zero tensor complex makes the conclusion immediate, and a zero morphism gives the usual direct-sum cone where the triangulated two-out-of-three statement applies.

## Second reading by F1

- Item statement: checked against Stacks Tag 07A3, label `sites-cohomology-lemma-K-flat-two-out-of-three`, including the ringed-site, distinguished-triangle, and two-out-of-three hypotheses; verdict: agrees with the tensor-triangle clause used in the split.
- Step 1: checked the total-complex signs and direct-sum terms against `def-pc-tensor-complex-sheaves`, and the cone comparison against `lem-pc-tensor-mapping-cone-iso`; verdict: each cited statement supplies the named fact.
- Step 2: checked the cone triangle and acyclicity conclusion against `def-weil-abstract-derived-category`, `def-pc-acyclic-complex-modules`, and `lem-pc-acyclic-triangle-two-out-of-three`; verdict: the two-out-of-three application has the required hypotheses.
- `lem-pc-tensor-mapping-cone-iso`: checked self-contained site, ringed-site, complex, cone, and total-tensor definitions, TeX escaping, Tag 07A3/Definition 06YN source, and Mathlib declarations at MappingCone.lean 641-643; verdict: Mathlib leaf and no duplicate found.
- `lem-pc-acyclic-triangle-two-out-of-three`: checked the acyclic-complex definition, triangulated closure declaration at Acyclic.lean 40-43, source Tag 07A3, and zero/field cases; verdict: Mathlib leaf and no duplicate found.
- Edge cases: tested the zero complex, zero morphism, and a field coefficient sheaf; all conclusions reduce to the stated cone and acyclicity facts.

Changes made:

- Corrected the stale Mathlib no-hit record for mapping cones and recorded the exact `mapHomologicalComplexIso` search and source lines.
- Added the exact cone and acyclic-subcategory Mathlib leaves and their verbatim citation quotes.
- Recorded this second reading and reran delivery preflight successfully.
