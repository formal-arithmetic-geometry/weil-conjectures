# Stage 1 report

Files written:

- `lem-weil-pbc-spread-finite-separable-extension.json`: split statement; 2 existing DAG leaves and 1 new Mathlib leaf used.
- `lem-weil-pbc-finite-separable-primitive-element.json`: Mathlib leaf for the primitive-element theorem.
- `citations.json`: verbatim citations for every non-elementary proof use.

Attachments: none.

WANTED: none.

The source item has no declaration in `WeilConjectures/` carrying the blueprint tag. The split follows the blueprint's finite-algebra calculation. Step 1 chooses a primitive element and identifies the generic quotient with the field extension. Step 2 clears denominators and localizes at the discriminant, proving finiteness, domain, and fraction-field assertions directly. Step 3 invokes the existing standard-etale leaf and proves surjectivity from the generic point and the open-and-closed image argument.

## Review by H1

I read the item source in the blueprint parent proof and checked the exact statements of `lem-weil-pbc-minimal-polynomial-quotient-field-iso` and `lem-weil-pbc-standard-etale-monic-derivative`. Step 1 uses only the primitive-element statement and the quotient-isomorphism statement, which explicitly provide the chosen generator and the field identification. Step 2 is elementary denominator clearing and the standard monic-quotient basis calculation; the embedding into `K'` proves the quotient is a domain and localization gives the fraction field. Step 3 uses the cited standard-etale statement for etaleness; finite plus etale gives an open-and-closed image, and the generic point lies in the image because the algebra is a domain with fraction field `K'`, so surjectivity follows on integral `Spec(S)`. I tested the construction on `K'=K` (take `f=T-alpha` and obtain `A'=S`) and on a quadratic separable extension (invert its discriminant). The new primitive-element node was searched in the DAG and blueprint first, then searched with LeanFinder, Loogle, grep, and LeanSearch; LeanFinder found `Field.exists_primitive_element`, Loogle and grep found no direct hit under the submitted queries, and LeanSearch was unavailable. The item searches were run with all four required tools and recorded in the node.

No source or statement error was found.

## Not duplicates

lem-weil-pbc-finite-separable-primitive-element vs lem-weil-pbc-simple-algebraic-extension-power-basis: the new node asserts existence of a single generator for an arbitrary finite separable extension, while the existing node assumes a chosen algebraic element and gives the power basis of the already generated simple extension.

lem-weil-pbc-finite-separable-primitive-element vs lem-weil-pbc-minimal-polynomial-quotient-field-iso: the new node supplies the primitive element for the whole finite separable extension, while the existing node identifies the quotient by the minimal polynomial after an element has already been chosen.

## Second reading by H1

- Item statement: checked against the parent blueprint finite-algebra calculation and its use in `lem-weil-pbc-generic-finite-algebra-splitting`; hypotheses and the finite-etale-surjective conclusion agree.
- Step 1: checked against the primitive-element leaf and minimal-polynomial quotient leaf; both statements provide exactly the generator and quotient identification used.
- Step 2: checked against the denominator-clearing calculation for Tag 00UB; monicity gives the finite free basis, separability gives a nonzero discriminant to invert, and localization identifies the fraction field.
- Step 3: checked against the standard-etale leaf (Tags 00UB/00UC); its etaleness clause applies to the localized derivative, and the generic-point plus finite-closed image argument gives surjectivity.
- New node `lem-weil-pbc-finite-separable-primitive-element`: checked against Fields Tag 09GN and Mathlib `Field.exists_primitive_element`; finite was made explicit as finite-dimensional and all notions have definition dependencies.
- No new item node beyond the primitive-element Mathlib leaf; existing quotient and standard-etale leaves were searched by id and key terms and reused.
- Edge cases checked: `K'=K` with a linear polynomial, a quadratic separable extension after discriminant localization, and the zero-degree/empty cases (excluded by the field-extension and positive minimal-degree hypotheses).

Changes made: made finite-dimensionality and separable-algebraic hypotheses explicit with definition dependencies in the item and primitive-element node; updated the verbatim citation; recorded this second-reading audit.
