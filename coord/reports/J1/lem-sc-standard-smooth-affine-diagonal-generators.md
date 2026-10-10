# Stage-1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-standard-smooth-affine-diagonal-generators.json`: item split into two proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-standard-smooth-affine-diagonal-regular-immersion.json`: one statement-only child, closed by the sorry-free Lean theorem `AlgebraicGeometry.isRegularImmersion_diagonal_specMap`.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

`AlgebraicGeometry.isRegularImmersion_diagonal_specMap` belongs to the new node `lem-sc-standard-smooth-affine-diagonal-regular-immersion`.

## WANTED

None.

## What I checked

I read the item's source reference (Stacks Tag 067R and the affine calculation in `WeilConjectures/AlgebraicGeometry/Morphisms/RegularImmersion.lean`, lines 336-375) and the surrounding Lean theorem. The item statement is the local-on-the-affine-diagonal consequence of that calculation. I searched the DAG and blueprint for the declaration, its theorem name, and the diagonal-generator wording; no existing node states the closed affine theorem, so the child is not a duplicate. The child records the exact declaration and lines and is marked closed in `lean_audit.slopmaster2`.

For step 1, I checked that the child statement supplies an affine neighbourhood, a length-d weakly regular generating list, and the diagonal kernel ideal. For step 2, I read `def-weil-pbc-regular-sequence`: at a point of the image the quotient is nonzero, so the weakly regular list satisfies the additional non-unit condition and is regular. I also read `def-weil-affine-spectrum`: on an affine spectrum the diagonal induced by multiplication has the stated ring kernel, so the sheaf-kernel ideal is the multiplication-map kernel. These are the only facts used by the two steps; the second is elementary from the cited definitions. The small cases d=1 and d=2 are the coordinate-difference sequences, and the positivity hypothesis excludes the zero-dimensional unit-ideal exception.

Mathlib searches for the new child were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as such. The parent item's pre-existing searches were retained unchanged. No source error or unresolved dependency was found.

## Review by J1

I checked the source and hypotheses line by line: `R` and `A` are commutative, `d` is positive, and the diagonal is the spectrum of the multiplication map. The closed child exactly records the project theorem's generator property. Step 1 cites only that statement. Step 2 cites the same generator statement, the regular-sequence definition, and the affine-spectrum definition; it explicitly checks the image-point nonzero quotient needed to pass from weakly regular to regular and identifies the affine kernel. The new node has statement only, complete Mathlib search records, a blueprint reference to the diagonal clause of `lem-sc-finite-duality`, and a closed Lean audit. I also checked there is no duplicate node or dependency cycle.

## What was wrong or incomplete

The imported item had no proof and no proof dependencies despite the completed affine theorem in the Lean source. The split makes that theorem an explicit closed child and records the missing local kernel argument in the item steps.

## What remains

Nothing remains for this stage; the required dry run is the final check.

## Second reading by J1

- Item statement: checked against Stacks Divisors Tag 067R, label `lemma-section-smooth-regular-immersion`, and the numerical affine theorem `isRegularImmersion_diagonal_specMap` at `RegularImmersion.lean:341-361`. The source gives regularity of a smooth section; the Lean theorem supplies length `d`. Hypotheses are commutative `R,A`, standard smoothness of relative dimension `d`, and `d>0`. Empty `Spec A` has no image points; for `d=1,2`, the chart has exactly that many coordinate differences.
- Step 1: `lem-sc-standard-smooth-etale-polynomial-chart` states the factorization and the etale map; `lem-weil-pbc-etale-algebra-flat` gives its flatness. Checked against Mathlib `RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` at `StandardSmooth.lean:253-258` and the existing flatness node. The ring maps agree on constants, as required by the later tensor product over `R`.
- Step 2: `lem-sc-flat-polynomial-diagonal-differences-weakly-regular` states weak regularity for precisely the list used. Membership in `ker mu` follows by applying multiplication to each of the two tensor terms; surjectivity is witnessed by `a tensor 1`. Checked against `Algebra.TensorProduct.isWeaklyRegular_ofFn_one_tmul_sub_tmul_one` at `StandardSmooth.lean:40-59`.
- Step 3: `lem-sc-etale-polynomial-diagonal-kernel-clearance` supplies the element `e` and the kernel containment. `lem-sc-affine-regular-immersion-kernel-criterion` has exactly the remaining hypotheses established in steps 1-2, including positive length and surjectivity. Checked against `exists_lmul'_eq_one_mul_mem_ofList` at `StandardSmooth.lean:64-91` and `isRegularImmersion_specMap` at `RegularImmersion.lean:266-310`. This is where the local generator conclusion is obtained.
- Step 4: `def-weil-pbc-regular-sequence` requires a nonzero final quotient, and `def-weil-affine-spectrum` identifies the affine diagonal with multiplication. At an image point the inverse image on `U` is nonempty, so its defining ideal is proper; thus the weakly regular generators from step 3 are regular. This is an elementary deduction, including over a field and for `d=1`. `d=0` is excluded by the item.
- New node `lem-sc-standard-smooth-etale-polynomial-chart`: exact Mathlib leaf at `Mathlib/RingTheory/RingHom/StandardSmooth.lean:253-258`, checked against Tag 00T6, label `definition-standard-smooth`. Statement only, self-contained, definition cited, TeX and source checked. Loogle and LeanFinder found the declaration; Mathlib grep found its line.
- New node `lem-sc-flat-polynomial-diagonal-differences-weakly-regular`: checked against the sorry-free Lean theorem at `WeilConjectures/Mathlib/RingTheory/RingHom/StandardSmooth.lean:40-59`. It asserts only weak regularity under flatness, not any diagonal ideal generators. Statement only, weak regularity spelled out, TeX and source checked. Mathlib searches found flat transport but no exact coordinate-difference theorem. For `d=0` the empty list is weakly regular; for `d=1,2` the list has the expected length, including over the zero ring.
- New node `lem-sc-etale-polynomial-diagonal-kernel-clearance`: checked against the sorry-free Lean theorem at `WeilConjectures/Mathlib/RingTheory/RingHom/StandardSmooth.lean:64-91`. It gives an element clearing the kernel, strictly less than the item's local regular sequence claim. Statement only, TeX and source checked. Mathlib searches found no exact kernel-clearance theorem; for `d=0` it is the usual etale diagonal idempotent condition, and the zero ring causes no exception.
- New node `lem-sc-affine-regular-immersion-kernel-criterion`: checked hypothesis by hypothesis against the sorry-free Lean theorem at `WeilConjectures/AlgebraicGeometry/Morphisms/RegularImmersion.lean:266-310`. It applies to any surjective affine ring map satisfying the clearance condition, so is not a clause of the item's standard-smooth diagonal statement. Statement only, notions defined inline or cited, TeX and source checked. Mathlib searches found closed-immersion results but no exact criterion. The positive-codimension hypothesis rules out its empty-list edge case.
- Existing-node search: Tag 067R and diagonal-regularity searches found `lem-sc-smooth-diagonal-regular-immersion`, which already depends on this item, so citing it would cycle; searches for etale flatness found the existing Mathlib leaf `lem-weil-pbc-etale-algebra-flat`, used in step 1. Blueprint searches found no matching node. All new-node Mathlib queries were run with `msearch.py` and recorded in `searches.jsonl`.
- Changes: the dry run rejected the original closed child under D1 because it restated the item. Removed it, split the actual Lean calculation into three narrower closed facts and one Mathlib leaf, wrote the four proof steps, replaced citations with verbatim statements, and corrected source labels and line numbers. The first worker's sections above remain for history; their file list and proof summary describe the superseded first draft.

## Not duplicates

- `lem-sc-standard-smooth-etale-polynomial-chart` vs `def-weil-pbc-standard-smooth-algebra` (00T6): the definition gives a Jacobian presentation; the new leaf gives the relative-dimension-$d$ etale polynomial factorization used by the Lean proof.
- `lem-sc-flat-polynomial-diagonal-differences-weakly-regular` vs `lem-sc-standard-smooth-affine-diagonal-generators` (067R): the new node is a ring-theoretic weak-regularity fact for coordinate differences under flatness, with no diagonal or local-neighbourhood conclusion.
- `lem-sc-etale-polynomial-diagonal-kernel-clearance` vs `lem-sc-standard-smooth-affine-diagonal-generators` (067R): the new node only clears the multiplication kernel after multiplying by one element; it does not assert regularity or local generators.
- `lem-sc-affine-regular-immersion-kernel-criterion` vs `lem-sc-standard-smooth-affine-diagonal-generators` (067R): the new node is a general affine criterion for any surjective ring map and does not assume standard smoothness or a diagonal.
- `lem-sc-standard-smooth-etale-polynomial-chart` vs `sbc-lem-affine-space-smooth` (00T6), `lem-weil-pbc-polynomial-ring-smooth` (00T6), and `lem-weil-pbc-popescu-delocalize-weak-localization-smooth` (00T6): those nodes state smoothness or a spreading-out construction, while this leaf states the relative-dimension etale factorization.
