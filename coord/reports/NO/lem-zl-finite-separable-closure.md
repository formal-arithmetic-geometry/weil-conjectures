# Delivery report: lem-zl-finite-separable-closure

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-finite-separable-closure.json`: item split into two proof steps; status `split`.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-finite-algebraic-closure.json`: statement-only node for Stacks Tag 037J; Mathlib searches found no exact theorem.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-separable-permanence.json`: Mathlib leaf, `Algebra.IsSeparable.trans`, `Mathlib/FieldTheory/SeparableDegree.lean:835`.
- `citations.json`: verbatim statement excerpts for every node cited by every item step.

## Attachments

None. I searched the slopmaster2 source for the item id and for the field-theoretic declarations; no sorry-free project declaration states this item.

## WANTED

None.

## What was wrong or incomplete

The imported item was unsplit even though Tag 037Q gives a short field-theoretic proof. The proof requires two facts that were absent from this unit's DAG: Tag 037J (the algebraic closure of the base in a finitely generated extension is finite) and Tag 09HB (separable algebraicity is transitive). I added those supports, using the existing relative-separable-closure and relative-algebraic-closure definitions. The item statement itself is faithful to Tag 037Q; no hypotheses or conclusions were changed. No duplicate node for Tag 037J or Tag 09HB exists in the DAG or blueprint. The Mathlib search for Tag 037J found only nearby algebraic-closure and finite-intermediate-field results, so that node remains unsplit; the Tag 09HB statement is a one-line specialization of `Algebra.IsSeparable.trans` and is recorded as a Mathlib leaf.

## What I could not finish

Nothing. No Lean files were written and no compiler or build tool was run, as required for stage 1.

## Review by NO

I read the item node, the chapter `sec-deligne-laumon-general`, and unit `sk-i-dl-general-real`, then checked the source proof in `literature/stacks-project/algebra.tex` at Tag 037Q and its cited Tag 0G33 equivalence. Step 1 uses the statement of `def-weil-pbc-relative-separable-closure` to obtain that k' is the separable algebraic closure and a separable algebraic extension of k; it uses `lem-zl-separable-permanence` for the tower k ⊆ k' ⊆ K, and then applies the exact equivalence in `lem-zl-geometric-irreducibility-separable`. Step 2 uses `def-weil-relative-algebraic-closure` to identify the algebraic closure k_alg and the new Tag 037J node to bound its degree; the inclusion k' ⊆ k_alg and the finite-dimensional subfield bound give [k':k] < ∞. I checked the hypotheses in both steps, including that every element of k' is algebraic over k and separable-permanence applies to an element separably algebraic over k'. I tested edge cases K = k (so k' = k), finite separable K/k (so k' = K), and a purely inseparable finitely generated extension (so k' = k). I searched the whole DAG and blueprint for Tags 037J, 09HB, and the relevant field-theory wording, and ran LeanFinder, Loogle, grep, and LeanSearch for both the item and each new node. The citation quotes were checked programmatically as exact substrings of the cited statements. No source error or duplicate was found.
