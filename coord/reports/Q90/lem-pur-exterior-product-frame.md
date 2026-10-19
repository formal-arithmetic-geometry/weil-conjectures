# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-exterior-product-frame.json`: repaired the four-step split; added the smooth-product permanence dependency and the normalized quotient-adjunction comparison.
- `citations.json`: added verbatim citations for `lem-sbc-smooth-relative-dimension-permanence` (step 1) and `lem-pur-supported-product-quotient-model` (step 4).

No new nodes were created; all cited facts are existing DAG statements.

## Attachments

None. No sorry-free declaration in the reference source states this item exactly.

## WANTED

None.

## Problems found and repaired

The returned review identified a C3/E5 gap in step 4: the former text asserted that the adjunction-defined pro-etale exterior product agrees with the supported cup product without a statement-level normalization. The current DAG contains `lem-pur-supported-product-quotient-model`, whose statement identifies the quotient adjunctions and derived counits with the normalized `C_a` adjunctions, preserves the quotient generators, and identifies the pro-etale quotient map `q_a`. I added this node to step 4 and wrote the missing generator check: both the exterior-product comparison and the inverse of the cup coefficient multiplication map agree after precomposition with `q_h`, hence agree by the quotient factorization. The step then explicitly identifies the adjoint-of-counits construction with the composite defining supported cup.

The review also identified a C1 omission: the frame class of the product requires smoothness of both $P=U_1\\times_kU_2$ and $Q=Z_1\\times_kZ_2$. Step 1 now cites `lem-sbc-smooth-relative-dimension-permanence` for base change and composition of smooth relative dimensions, while recording the elementary pure-codimension dimension subtraction.

## Review by Q90

I reread the item statement and the complete source proof `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-regular/sk-thm-regular.proof.md`, Step 5, together with the statements of every cited node: `def-pur-frame-class`, `def-pur-supported-exterior-product`, `def-pur-supported-cup`, `def-pur-proetale-supported-exterior-product`, `lem-pur-supported-cup-functoriality`, `lem-pur-supported-product-quotient-model`, and `lem-sbc-smooth-relative-dimension-permanence`. Step 1 now verifies the smoothness hypotheses for the product ambient and support using the permanence statement, then uses the affine kernel formula for the product ideal. Step 2 uses the cited functoriality clauses for pullback, localization boundaries, and Kummer classes, with the frame definition supplying the factors. Step 3 uses the cited bilinearity, associativity, graded commutativity, and twist multiplication; all factors have degree two, so the block sign is one. Step 4 uses the quotient-model statement's normalized adjunctions, counits, and quotient generators, and checks the two coefficient maps on the generator `q_h`; it then applies the exact supported-cup composite from `def-pur-supported-cup` and the pro-etale exterior-product definition. I checked the empty tuple, one-factor products, full-support factors, and the coordinate frame on affine space. Every citation quote is verbatim, every step's uses occur in `proof_deps`, and no step exceeds 2000 characters.

## What could not be finished

Nothing. The returned C3/E5 and C1 points are repaired; the required dry run remains.
