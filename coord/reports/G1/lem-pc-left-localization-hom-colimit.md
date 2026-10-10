Files written:

- `dag/nodes/sec-picard-framework/lem-pc-left-localization-hom-colimit.json`: split item.
- `dag/nodes/sec-picard-framework/lem-pc-left-localization-fraction-representation.json`: statement-only Mathlib leaf, exact match.
- `dag/nodes/sec-picard-framework/lem-pc-left-localization-fraction-equality.json`: statement-only Mathlib leaf, exact match.

Attachments: none.

WANTED: none.

The source checkout contains no declaration tagged `(blueprint: lem-pc-left-localization-hom-colimit)` and no sorry-free declaration with the item statement. I read the item and its ancestor blueprint clause, and checked the neighboring right-localization split for the intended orientation. Step 1 uses the representation statement, which explicitly supplies a numerator, denominator, and localized fraction map. Step 2 uses the equality statement, which explicitly says equality is the common-refinement relation; this is exactly the filtered-colimit identification relation. The hypotheses are the category, multiplicative system/left-calculus assumptions, localization functor, and objects named in the item and the two Mathlib leaves. I ran leanfinder, loogle, grep, and leansearch searches for each new node; leansearch was unavailable and is recorded as such. No duplicate DAG node or blueprint node states either ingredient.

## Review by G1

I checked the item source at Derived Categories Lemma 0FND, line 9515 (fifth equality), and Categories Tag 05Q0. The first proof step only takes the existence of a left-fraction representative, and its cited node states that fact verbatim. The second step only takes the common-refinement equality criterion, and its cited node states that criterion verbatim. Both new nodes are self-contained statement-only leaves and point to the exact Mathlib declarations `CategoryTheory.Localization.exists_leftFraction` and `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq_iff_leftFractionRel`. I verified that the item’s proof dependencies are exactly the two cited nodes and that the citations quotes are verbatim.

What could not be finished: no project Lean declaration proves the item; the split therefore remains a DAG-level statement split as required for stage 1.

## Not duplicates

lem-pc-left-localization-fraction-representation vs lem-pc-left-localization-hom-colimit: the new node states only existence of a left-fraction representative, while the item states the bijection between a filtered colimit of Hom sets and localized Hom.

lem-pc-left-localization-fraction-equality vs lem-pc-left-localization-hom-colimit: the new node states only the equality/common-refinement criterion for two fractions, while the item states the full colimit bijection.

## Second reading by G1

- Item statement: checked against Categories Tag 05Q0, label `categories-remark-left-localization-morphisms-colimit`, and the fifth equality in Derived Categories Tag 0FND; the orientation `Hom(Q(Y),Q(X)) = colim_{s:X\to I} Hom(Y,I)` is correct.
- Step 1: checked against the definition of `X/S` and the displayed canonical map in Tag 05Q0; the map and its compatibility with transition triangles are elementary and are now written explicitly.
- Step 2: checked against the statement of `lem-pc-left-localization-fraction-representation` and Categories Tag 04VE; the source/target variables are instantiated in the correct order, giving surjectivity.
- Step 3: checked against the statement of `lem-pc-left-localization-fraction-equality` and Categories Tag 04VF; its common-refinement equalities are exactly the colimit identification relation, giving injectivity.
- Step 4: checked against the displayed formula in Tag 05Q0 and the identity-only case; the bijection conclusion and edge-case check are elementary.
- `lem-pc-left-localization-fraction-representation`: checked against Categories Tag 04VE and Mathlib `CategoryTheory.Localization.exists_leftFraction`; self-contained, statement-only, exact left-fraction specialization.
- `lem-pc-left-localization-fraction-equality`: checked against Categories Tag 04VF and Mathlib `CategoryTheory.MorphismProperty.LeftFraction.Localization.homMk_eq_iff_leftFractionRel`; self-contained, statement-only, exact equality-of-fractions specialization.

Changes made:

- Replaced the two compressed proof steps with four explicit steps defining the canonical map, proving surjectivity and injectivity, and concluding bijectivity.
- Corrected the representation step's fraction orientation by instantiating the Mathlib statement with source `Y` and target `X`.
- Corrected the supporting-node source references from Tag 05Q0 to the precise left-fraction lemma tags 04VE and 04VF.
- Updated `citations.json` to quote the statements at their corrected step numbers.
- Tested the identity-only multiplicative-system case; no false hypothesis or empty-object exception remains.
