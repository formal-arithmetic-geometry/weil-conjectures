# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-rational-cone-dual-integral-forms.json`: split item, with one new statement-only dependency.
- `dag/nodes/sec-trace-formula/lem-trf-rational-cone-dual-finite.json`: statement-only unsplit node; Mathlib search verdict no match.
- `citations.json`: verbatim citation for item step 1.

## Attachments

None. I found no sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` carrying this item or the new node.

## WANTED

- Kato 1994, *Toric singularities*, for the finite rational half-space (Minkowski--Weyl) description of a rational polyhedral cone used by `lem-trf-rational-cone-dual-finite`.

## Not duplicates

- `lem-trf-rational-cone-dual-finite` vs `lem-trf-gordan-rational-cone-finite`: the new node gives a finite rational half-space intersection for a cone, while the existing node gives a finite union of translates describing lattice points in a cone.
- `lem-trf-rational-cone-dual-finite` vs `lem-trf-sharp-cone-lattice-intersection`: the new node is a rational cone H-description, while the existing node identifies a saturated sharp monoid with lattice points and proves freeness, pointedness, and spanning.
- `lem-trf-rational-cone-dual-integral-forms` vs `lem-trf-sharp-fs-orthant-embedding`: the item supplies the integral defining forms used by the orthant embedding; the existing node is the larger monoid embedding theorem that cites this item.

## What I checked and corrected

The item has no exact closed declaration. I read its DAG statement, the `sk-i-curve-zero` unit, the `sec-trace-formula` chapter, the immediate citer `lem-trf-sharp-fs-orthant-embedding`, and the ancestor `lem-trf-local-term-locality`. I searched the whole DAG and both blueprint snapshots for the item, rational-cone, dual-cone, Minkowski, and Farkas formulations; no duplicate or alternate blueprint statement was found. I also searched the Lean source for the item id and its mathematical keywords; no declaration exists.

For the new node I read Mathlib's `Geometry/Convex/Cone/DualFinite.lean` and `Dual.lean`. Mathlib defines `PointedCone.DualFG` and records the general dual-cone operations, but it does not prove the finite-dimensional rational Minkowski--Weyl equivalence or its rational H-cone specialization. The new statement is therefore unsplit with `mathlib_match: null`.

Step 1 cites the new node for exactly its finite family of rational linear forms and the displayed equality. The node's statement explicitly allows the empty family, so the rank-zero case is handled there and in the item step. Step 2 uses only a chosen lattice basis: rational coefficients have common positive denominators, rescaling preserves nonnegative inequalities, and the resulting forms map the lattice into integers. Step 3 checks the hypotheses carefully: if all forms vanish on `x`, then both `x` and `-x` lie in the cone; pointedness forces `x=0`. The finite-dimensional annihilator argument written in the step then gives that the forms span the full dual. Since the dual of nonzero `V` is nonzero, a spanning family has at least one member. I tested the empty-rank case, the one-dimensional cone `Q_{≥0}` with form `x`, the full-line case (excluded by pointedness), and the zero cone in positive dimension (forms `±` a basis coordinate are needed).

I retained the item's source and blueprint ancestry, filled its previously unspecified blueprint place, and set `proof_deps` to the union of the step uses. No Lean files were written or compiled.

## Review by Q67

I reread the item and new node after writing them. The only non-elementary input is the new node's finite rational half-space theorem; its statement says exactly what step 1 takes from it, and the quote in `citations.json` is verbatim. I checked that the lattice is free of finite rank as stated, so the denominator-clearing argument in step 2 applies, and that positivity of each denominator preserves the cone. In step 3 I verified both directions of the common-kernel argument and the use of pointedness; the spanning conclusion is the standard finite-dimensional dual-basis argument spelled out in the step. I checked the zero-dimensional case separately and verified that the nonzero case forces a nonempty family. The existing Gordan and sharp-cone nodes are cited in the duplicate review only because their statements are different; neither is inserted as a proof dependency. The source route remains the ILO Remark 3.1.29 rational-polyhedral route, with Kato recorded as wanted.

## Long-step review

No proof step exceeds 2000 characters or hides a separate lemma: step 1 is one application of the new node, step 2 is denominator clearing, and step 3 is the direct pointedness/common-kernel argument.
