Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-quasi-isos-saturated-triangulated.json` — statement, split proof, and citations.
- `dag/nodes/sec-smooth-purity/lem-pur-quasi-iso-cone-acyclic.json` — statement node attached to the sorry-free project declaration `CochainComplex.mappingCone.quasiIso_iff_acyclic`.
- `dag/nodes/sec-smooth-purity/lem-pur-acyclic-subcategory-triangulated.json` — Mathlib leaf for `HomotopyCategory.instIsTriangulatedIntUpSubcategoryAcyclic`.

Attachments:

- `CochainComplex.mappingCone.quasiIso_iff_acyclic` belongs to `lem-pur-quasi-iso-cone-acyclic`.

WANTED:

None.

## Review by C1

I read Stacks `derived.tex`, Lemma 05RT and the Situation 05S8 paragraph before editing the item. The item statement agrees with those clauses: 05RT supplies the saturated quasi-isomorphism localizer and cone criterion, while 05S8 supplies the localization and triangulated compatibility hypotheses. I also read the existing nodes `lem-pc-quasi-isomorphisms-multiplicative-system`, `def-weil-abstract-derived-category`, and `def-weil-triangulated-category`; their statements provide exactly the localization, derived-category, and triangulated-category interfaces cited in Step 1 and Step 5.

Step 1 uses the existing multiplicative-system node only for its stated left/right calculi of fractions and localization conclusion. Step 2 uses the new cone node, whose statement is exactly the quasi-isomorphism/cone-acyclic equivalence. Step 3 uses the generic acyclic-subcategory leaf and the same cone equivalence; the leaf states both triangulated closure and isomorphism closure, so it supports the two-out-of-three conclusion for distinguished triangles. Step 4 is elementary: applying each cohomology functor reduces two-out-of-three to isomorphisms, and applying it to a retract diagram shows retract closure. Step 5 uses the existing localization node and the two definition nodes for the final Situation 05S8 assembly.

For the attached cone declaration I checked `WeilConjectures/Mathlib/Algebra/Homology/HomotopyCategory/Acyclic.lean:24-37`; it has no `sorry` and its hypotheses are precisely an arbitrary abelian category and integer-indexed cochain complexes. For the Mathlib leaf I read `Mathlib/Algebra/Homology/HomotopyCategory/Acyclic.lean:35-46`; the instance gives a triangulated, isomorphism-closed acyclic subcategory for every abelian category. I searched the DAG and blueprint for both statements and found no duplicate; the nearest existing acyclicity node is restricted to sheaves of modules and therefore does not apply to the arbitrary abelian-category item.

I tested the statements on the zero morphism and identity morphism: the identity cone is contractible/acyclic and the zero map between non-acyclic complexes is not a quasi-isomorphism in general. The proof dependencies and verbatim quotes are recorded in `citations.json`. No source or statement error was found.

## Not duplicates

`lem-pur-quasi-iso-cone-acyclic` vs `lem-pur-quasi-isos-saturated-triangulated`: the child states only the cone characterization, while the item additionally asserts saturation, localization, and triangulated compatibility.
`lem-pur-quasi-iso-cone-acyclic` vs `def-weil-abstract-derived-category`: the child proves the cone characterization, while the definition specifies the derived category and cone triangles but does not assert the equivalence.
`lem-pur-quasi-iso-cone-acyclic` vs `lem-pc-quasi-isomorphisms-multiplicative-system`: the child states quasi-isomorphism iff cone acyclic; the existing leaf states calculi of fractions and localization.
`lem-pur-quasi-iso-cone-acyclic` vs `def-weil-derived-category-cohomology-functor`: the child states the cone criterion; the existing definition introduces cohomology and quasi-isomorphisms and their factorization, without a cone assertion.
`lem-pur-acyclic-subcategory-triangulated` vs `lem-pur-quasi-isos-saturated-triangulated`: the child states triangulated and isomorphism closure of acyclic complexes, while the item assembles that with saturation and localization.
`lem-pur-acyclic-subcategory-triangulated` vs `def-weil-abstract-derived-category`: the child gives closure of acyclic complexes in the homotopy category; the definition constructs the derived category and its triangulated structure.
`lem-pur-acyclic-subcategory-triangulated` vs `lem-pc-quasi-isomorphisms-multiplicative-system`: the child concerns acyclic objects and distinguished triangles; the existing leaf concerns morphism calculi and localization.
`lem-pur-acyclic-subcategory-triangulated` vs `def-weil-derived-category-cohomology-functor`: the child gives triangulated closure of acyclic objects; the existing definition gives cohomology and the definition of quasi-isomorphism.

End report:

1. Files written: the item and two child nodes listed above.
2. Attachments: one project declaration attached to the cone child.
3. WANTED: none.
4. The imported item had no proof; its missing dependencies were the generic cone criterion and generic acyclic triangulated-subcategory fact.
5. Nothing remains unfinished.

## Second reading by C1

- Item statement: checked against Stacks `derived.tex`, Lemma 05RT and Situation 05S8; all abelian-category, complex, localization, saturation, cone, and triangulation hypotheses are present. Small cases checked: zero and identity maps have acyclic cones and are quasi-isomorphisms; a zero map between complexes with nonzero cohomology is not generally a quasi-isomorphism.
- Step 1: checked against `lem-pc-quasi-isomorphisms-multiplicative-system`; its fraction calculi and localization conclusion are exactly used.
- Step 2: checked against `lem-pur-quasi-iso-cone-acyclic`; its cone equivalence is exactly used and its attached declaration is sorry-free.
- Step 3: checked against both cited statements; the revised wording uses acyclic objects in distinguished cone triangles to express two-out-of-three for the corresponding morphisms, with shifts and isomorphisms supplied by the acyclic-subcategory leaf.
- Step 4: checked against the explicit cohomology and quasi-isomorphism definitions in `def-weil-abstract-derived-category`; two-out-of-three and retracts of isomorphisms are elementary categorical arguments.
- Step 5: checked against the three cited localization and triangulation statements; each supplies the conclusion used.
- `lem-pur-quasi-iso-cone-acyclic`: B1-B7, Stacks 05RT, and `CochainComplex.mappingCone.quasiIso_iff_acyclic` checked; exact Mathlib leaf, no duplicate, and zero/identity cases pass.
- `lem-pur-acyclic-subcategory-triangulated`: B1-B7, Stacks 05RT and the cone-triangle section checked; exact Mathlib leaf with triangulated and isomorphism closure, no duplicate, and zero/identity cases pass.

Changes made: corrected the item node's `created.item` metadata and rewrote Step 3 to state morphism compatibility through distinguished cone triangles rather than calling quasi-isomorphisms objects. Step 3 citations remain verbatim.
