Files written:

- `dag/nodes/sec-picard-framework/lem-pc-coherent-property-devissage.json`: repaired 01YI split with minimal-support induction and irreducible comparison.
- `dag/nodes/sec-picard-framework/lem-pc-coherent-property-irreducible.json`: new unsplit statement node for Stacks 01YH.
- `citations.json`: verbatim citations for every non-elementary dependency.

Attachments: none.

WANTED: none.

What was wrong in the returned material: the former steps applied hypothesis (2)(a)-(d) directly to every filtration quotient. Tag 01YI only provides one witness G for each integral support, so that inference was invalid. The repair follows the source route: choose a minimal bad irreducible closed subset using the Noetherian minimal-element lemma; prove proper-support modules by filtration; then apply the 01YH irreducible-support comparison lemma to the single witness G and contradict minimality.

## Not duplicates

`lem-pc-coherent-property-irreducible` vs `lem-weil-pbc-coherent-property-devissage-integral-subschemes`: the new node is the local 01YH irreducible-support criterion with one generic rank-one witness; the existing node is the broader 01YM criterion with ideal-closure and direct-summand hypotheses.

## Review by M1

I read the item source at Stacks Tag 01YI (`coherent.tex` line 3270) and the returned proof. I verified that its hypothesis (2) supplies only one coherent witness for each integral closed subscheme, which is why the old filtration-quotient argument failed. I read Tag 01YH (`coherent.tex` line 3179) and made it an explicit statement node: extension closure, the proper-support case, and one coherent module with support T and one-dimensional annihilated generic stalk imply the property for every coherent module supported in T.

Step 1 is the elementary isomorphism and finite-filtration induction from 01YI, including the zero-module case. Step 2 cites the existing filtration node and generic-ideal-stalk node; these say exactly that the quotients are pushforwards from integral schemes and that a nonzero ideal has full generic stalk. Step 3 cites the existing Noetherian minimal-closed-subset leaf and the filtration node, and checks that every proper-support quotient lies in a strictly smaller irreducible support. Step 4 cites the new 01YH statement; its hypotheses are supplied by the item's (2) and Step 3. Step 5 repeats the filtration node to conclude for arbitrary coherent modules.

I ran fresh LeanFinder, Loogle, and Mathlib grep searches for both the repaired item and the new 01YH node; the searches found only general Noetherian or module-support facts and no coherent-sheaf devissage theorem. The new node is therefore unsplit rather than a Mathlib leaf. The zero module and empty filtration remain covered by hypothesis (0).

## Source error

The Stacks statement of Tag 01YI omits the zero-module hypothesis, but that omission is false on the empty scheme: the property "false" satisfies the displayed exact-sequence and witness conditions vacuously while failing for the zero module. The item therefore retains hypothesis (0), with the counterexample recorded in its source field.

## Second reading by M1

- Item statement: checked against Tag 01YI, label `lemma-property`, coherent.tex line 3270, hypothesis by hypothesis; verdict: correct after the explicit necessary (0) source correction.
- Item step 1: checked against the finite-filtration paragraph of Tag 01YI; isomorphism invariance and the empty-filtration case follow from (0) and (1); verdict: elementary and correct.
- Item step 2: checked against Tag 01YF and the existing filtration and generic-ideal-stalk node statements; verdict: cited quotients, supports, and generic stalk facts match.
- Item step 3: checked against the minimal bad-support paragraph of Tag 01YI and the filtration node; verdict: minimality applies to every proper integral support and yields the stated proper-support conclusion.
- Item step 4: checked against Tag 01YH, line 3179; verdict: corrected citation now uses the exact integral-proper-subscheme hypothesis and all its assumptions are supplied by steps 2-3 and item hypothesis (2).
- Item step 5: checked against the conclusion of Tag 01YI; verdict: filtration induction correctly concludes the arbitrary coherent case, including zero.
- New node `lem-pc-coherent-property-irreducible`: checked against Tag 01YH statement and proof context; verdict: statement repaired to match the source's integral closed subscheme and quasi-coherent ideal clause, with all notions definition-linked and no Mathlib match.

Changes made: corrected the 01YH node's strengthened hypothesis (2) to the source-exact clause; updated the step-4 verbatim citation; added this second-reading record and the required source-error explanation. Fresh LeanFinder, Loogle, and Mathlib grep searches remain recorded in `searches.jsonl`/the node.
