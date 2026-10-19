# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-linear-scalar-localization-triangulated.json`: statement node, now split; not a Mathlib leaf. Its seven steps verify the scalar-specific hypotheses of the existing triangulated-localization theorem.
- `citations.json`: verbatim statement quotes for every citation in all seven steps.
- No new nodes and no new Mathlib leaves. Search receipts are in `searches.jsonl`.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint tag and by scalar-localization notions found no declaration asserting this result. The item has `lean_audit.slopmaster2.state = none`. Upstream master is reference material, not evidence of completion.

## WANTED

None. The sources for all ingredients are available locally. The scalar-specific verification is an agent-written argument, not presented as a verbatim proof from Stacks.

## What was wrong or incomplete

The statement is correct and is unchanged. The imported source suggested applying 05R6 to the saturation of the scalar maps, but neither compatibility with triangulation nor identification of the abstract localization with the concrete Hom tensor construction was supplied. The split now verifies both. It uses the class of all arrows inverted by the concrete scalar functor, proves its calculus of fractions and compatibility, and proves directly that the concrete functor is its localization. It does not assume this class is compatible merely because it inverts scalar identities.

The whole-DAG search for 05R6/05R2, multiplicative systems, fractions, representable Hom exactness, five lemma, and module localization found every ingredient already present. In particular, `lem-pur-localization-triangles-05r6` already states the general result, so no restatement is created. Blueprint searches for localization, scalar localization and rationalization found coefficient-category definitions and scalar-extension lemmas, but no duplicate of the item. Its `same_as` is therefore `[]`. The ancestor tool gives `def-weil-rationalization-karoubi`; the item's source place now identifies the rationalization display and the triangulated-category sentence. The unit `sk-def-sf-operations` has no proof steps. This item is not its key statement, so no unit record is modified. No chapter or unit route is changed.

The source metadata of `def-pur-saturated-triangulated-localization` still mentions 04VB/04VD, although its statement and review correctly identify 04VC/05Q8. I use the statement's correct tags and do not edit that other node.

Mathlib searches were run through the prescribed command with two semantic phrasings, two Loogle queries, two grep queries and LeanSearch. The first Loogle namespace query returned an unknown-identifier error; the second found `MorphismProperty.IsCompatibleWithTriangulation`. LeanFinder found the general triangulated-localization construction; grep confirmed `pretriangulated`, `isTriangulated_functor`, `isTriangulated` and `distTriang_iff`, whose source I read. None supplies the scalar-specific calculus, compatibility or Hom tensor identification in one line. LeanSearch returned Internal Server Error and is recorded as unavailable. No search result was invented.

## What could not be finished

Nothing in the stage-1 split remains open. Existing cited nodes retain their own independent stage states; this delivery claims no Lean proof and performs no compiler or Lake operation. Delivery is reserved for the second reader.

## Review by NQ

I read the item together with the master blueprint's `def-weil-rationalization-karoubi.md`, the chapter and unit records, and Stacks `derived.tex` Tag 05R6 (`proposition-construct-localization`), including the distinguished-triangle definition and the TR4 argument. The item asks for raw scalar localization, not completion, and uses arbitrary commutative R and arbitrary varpi. Those hypotheses are preserved. I also read the MS5/MS6 definition 05R2 and the representable exactness argument 0149, the fraction and tensor-localization material in `algebra.tex` (07JZ/07K0 and 00DK), and the five lemma in `homology.tex` (05QB). There are no new nodes whose source or small cases need separate review.

Step 1 uses the actual four-clause statement of `lem-weil-linear-scalar-localization-category`: it supplies composition, the functor and shift, but makes no triangulation claim. `lem-weil-pbc-localization-module-tensor` supplies both the Hom tensor identification and naturality; `def-weil-pbc-module-localization-away` supplies the fraction relation and zero criterion. The biproduct equations are explicitly preserved by Q, so additivity is not inferred merely from having module-valued Hom sets.

Step 2 uses the definition's exact MS1/MS4/MS5 clauses and the fraction criterion. The two exponents annihilating the inverse errors are made a common exponent, giving both equations in the original category. This checks a hypothesis needed in each of the Ore squares rather than treating an equality after localization as an equality before localization. The shift inverse reflects invertibility without supposing any triangulation on the new category.

Step 3 checks both MS2 squares with their arrows typed as in `def-pur-saturated-triangulated-localization`. Its two MS3 equalizers use the zero criterion of the module-localization node. The scalar calculations are written as elementary steps, not new nodes.

Step 4 reads `lem-weil-pbc-hom-into-triangle-exact` clause (ii), with rotations from `def-weil-triangulated-category`, to obtain every consecutive exact pair in the five-term row. The cited tensor lemma identifies its localized maps naturally. Localization exactness is proved here by taking a representative y/varpi^n, annihilating its image by a power, and lifting the multiplied numerator. Thus no uncited flatness or exact-localization theorem is hidden in this step.

Step 5 uses TR3 from the triangulated-category definition to obtain c, and applies `lem-weil-pbc-five-lemma` only after step 4 has proved exactness at all three middle terms. All four exterior vertical arrows are isomorphisms; MS5 covers the shifted ones. Its conclusion is invertibility of postcomposition by Q(c). The explicit two choices A=Z' and A=Z prove that Q(c) itself is invertible; no uncited Yoneda theorem is used. The two commuting conditions for a triangle morphism are precisely those of MS6 in the cited definition. In particular I do not invoke an exact-functor criterion while exactness of Q is still what must be proved.

Step 6 uses the universal-property clause of the multiplicative-system definition and the category and fraction nodes. I checked it for arbitrary functors to an arbitrary category, not just linear or additive functors. The image of a scalar identity is denoted d_X rather than incorrectly equated with scalar multiplication on F(X). Equality of fractions is converted to equality of original arrows, after which F and cancellation apply. Naturality with the invertible scalar identities supplies composition and the natural-transformation extension. Uniqueness follows from the displayed fraction expression and identity-on-objects property.

Step 7 uses exactly the full statement of `lem-pur-localization-triangles-05r6`, with all its hypotheses established in earlier steps, and the induced shift clause of the scalar-category node. The theorem's distinguished triangles agree with the item's specified triangles. The category lemma is in this item's unit, and every off-unit statement cited is already a Mathlib leaf. No off-route non-leaf tool use is introduced.

For section E I tested varpi=1 (Q identifies with the original category and every fraction has denominator 1), varpi=0 and nilpotent varpi (the coefficient ring and all Hom modules become zero, giving the zero category with possibly many isomorphic objects), the zero ring, the zero category, and arbitrary torsion in Hom modules. Choosing positive annihilating powers handles the nilpotent cases; no denominator is canceled inside R or the original Hom modules. No regularity, nonzero element, Noetherian, boundedness, essential-smallness or idempotent-completeness hypothesis appears in the proof. The proof uses one representable Hom at a time, avoiding an unlicensed product over a large category. I checked B--E: statements and dependencies are self-contained, every substantive fact has a node whose statement supplies it, no clause is moved to a new node, no duplicate or cycle is introduced, and the original statement is kept. The corrections made during self-review were to supply the arbitrary-functor universal property and both Ore squares explicitly instead of merely referring to a saturation construction.

## Second reading by NQ

- Item statement: checked all hypotheses against Stacks 05R6 (`proposition-construct-localization`), 05R2 (`definition-localization`) and the blueprint rationalization display; correct scalar specialization, no change needed. Tested the zero category, zero ring, scalar 0, scalar 1, a nonzero scalar over a field, nilpotent scalars and torsion Hom modules. Exponents 0 and 1 obey the same fraction formulas; no nonzero-denominator assumption is used.
- Step 1: checked the scalar-category node's four clauses, the tensor-localization node's formula and naturality, and the fraction-definition node against algebra.tex `lemma-tensor-localization` (00DK) and `definition-localization-module` (07JZ); valid composition, zero object, biproducts and shift.
- Step 2: checked the multiplicative-system node's MS1, MS4 and MS5 against categories.tex `definition-multiplicative-system` (04VC), `definition-saturated-multiplicative-system` (05Q8), and derived.tex `definition-localization` (05R2); valid common exponent, two inverse equations, and invertibility under both shifts.
- Step 3: checked the same node's two MS2 squares and both MS3 clauses arrow by arrow, using the fraction-definition zero criterion; both constructions have the required types and equalities.
- Step 4: checked the Hom-exactness node's clauses (i)--(iii), TR2 in the triangulated-category definition, and tensor naturality against derived.tex `lemma-composition-zero` (0146), `lemma-representable-homological` (0149), and algebra.tex 00DK/07JZ; valid, with the harmless rotation signs now explained. The explicit localized lifting proves exactness without an uncited flatness theorem.
- Step 5: checked TR3 and MS6 against the two cited definitions and the five-lemma node's exact hypotheses against homology.tex `lemma-five-lemma` (05QB); valid. Added the elementary verification of the abelian-group hypothesis against `def-sp-abelian` and the four diagram squares. The two choices of test object prove the inverse identities without invoking Yoneda.
- Step 6: checked the multiplicative-system node's precise functor and natural-transformation universal properties, the category node and the fraction relation; the displayed formulas establish both bijections for arbitrary functors, including nonadditive ones. All computations use composition and invertible scalar identities only.
- Step 7: checked the full statement of the existing 05R6 node against `proposition-construct-localization`, including its distinguished-triangle class and triangulated conclusion, and checked the scalar-category shift clause; all hypotheses are established before application.
- New nodes: none. The sandbox contains only the modified item; no duplicate, clause restatement, new unsplit lemma or Mathlib leaf is introduced. Each proof citation was read in its actual node file; citations.json contains the verbatim statement for every use, including the added definition.

Changes and reasons:

- Replaced the item's section-number source reference and doubled source TeX with exact Stacks tags and labels, satisfying B5.
- Explained why rotation signs do not affect exactness in step 4.
- Made the commuting five-term diagram explicit in step 5 and supplied the elementary abelian-group verification, with its definition citation, closing the implicit hypothesis in the five-lemma application.
- Added the corresponding verbatim quote to citations.json. The first worker's review remains intact.

Independent Mathlib search: ran the prescribed msearch grep with `IsLocalization.*Linear|Linear.*IsLocalization|localization.*coefficients` in CategoryTheory. The sole hit, `CategoryTheory.Shift.linear_of_localization` (Shift/Linear.lean:33), was read and only establishes linearity of an already localized shift; it does not prove the scalar-specific triangulated result. Also read Localization/Triangulated.lean:199--242, whose general theorem still requires compatibility and a calculus of fractions. Read-only searches of the supplied slopmaster2 Lean tree by item id and scalar-localization words found no completed exact declaration. No Lean files, compiler, Lake, live project, or launcher tools were modified.
