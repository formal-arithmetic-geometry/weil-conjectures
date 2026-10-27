## Files written

- `dag/nodes/sec-smooth-purity/lem-route-bounded-constructible-tate-twist-derived-of-invertible.json`: corrected the provisional machine-generated statement to the residue-field invertibility formulation, supplied a two-step proof, and marked the item `split`.
- No new node files: the existing reviewed node `nt-target-poincare-tate-bc` already states the bounded-constructibility theorem used in step 2.
- `citations.json`: verbatim citations for all proof-step uses.

## Attachments

None. The source theorem `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived_of_invertible` still has `sorry` in `lean/Sheaf/Targets/PoincareTateBoundedConstructible.lean`, so it is not a completed attachment.

## WANTED

None. The split uses the existing DAG statements and the current blueprint text; no additional literature document is required.

## What was wrong or changed

The imported item was provisional: it embedded a six-step machine-generated proof plan in the `statement`, had no statement dependencies, no proof, no completed blueprint place, and only a name grep. I replaced it with the exact mathematical content of the Lean theorem: an arbitrary scheme, a prime ell, residue-field invertibility at every point, the actual condensed Tate construction, and bounded constructibility for every signed twist and integer shift in the ordinary derived category. The source declaration and its docstring were read at lines 47–102 of `lean/Sheaf/Targets/PoincareTateBoundedConstructible.lean`; the theorem body remains `sorry`.

A whole theorem with the same conclusion already exists as the reviewed DAG node `nt-target-poincare-tate-bc`, under the equivalent formulation “ell is invertible on X.” I did not create a duplicate. Step 1 verifies the equivalence needed here: the image of ell is nonzero, hence invertible, in every residue field; a local inverse germ lifts to a local section of the structure sheaf, and these inverse sections glue uniquely. This also covers the empty scheme. Step 2 applies the existing node, whose statement has the same condensed coefficient ring, signed tensor-power/internal-Hom Tate construction, arbitrary scheme hypothesis, and exact bounded-constructibility predicate.

## Review by NC

I read the item’s archived upstream source and current Lean target, the current blueprint node `sk-def-sp-tate-twist`, the definitions `def-pur-condensed-tate-twists`, `def-sfb-bounded-constructible-complexes`, and `def-sfb-constructible-module`, and the complete statement of `nt-target-poincare-tate-bc`. The corrected item statement matches the Lean theorem clause by clause: `Fact ell.Prime` is represented by “ell is a prime”; the typeclass `∀ x, Invertible (ell : X.residueField x)` is represented by the pointwise residue-field unit hypothesis; `condensedRingObj (Profinite.padicAlgClRingObj ell) X`, `tateTwistDerived`, signed twists, and all integer shifts are retained; and the conclusion is the ordinary unbounded derived category’s `boundedConstructible` predicate with no finiteness assumption on X.

Step 1 uses only the definition of the residue field. The cited statement explicitly identifies it as the local ring modulo its maximal ideal. The remaining argument is elementary sheaf-local algebra: a residue-field unit is outside the maximal ideal, hence a local-ring unit; local inverses glue because inverses are unique. I checked the empty scheme separately.

Step 2 uses the complete statement of `nt-target-poincare-tate-bc` and the Tate-construction definition. That existing statement explicitly supplies the exact coefficient ring, construction, arbitrary-scheme hypotheses, all signed powers and shifts, and bounded-constructibility conclusion. The tool use is declared because this is a generic Tate bounded-constructibility result from the pro-etale Tate-twist unit, while the present purity-transport unit does not reproved general Tate constructibility. The citation quotes were copied verbatim into `citations.json`; there are no uncited non-elementary facts and no new node to audit for duplicates.

I searched the whole DAG and blueprint for the Tate construction and bounded-constructibility statement, and searched Mathlib with LeanSearch, LeanFinder, Loogle, and source grep. The searches returned only generic condensed-category, derived-shift, or constructible-set declarations; none states this condensed Tate theorem. No Lean file was written and no compiler or build tool was run. The server-side `review_split` check passed with zero new nodes.
