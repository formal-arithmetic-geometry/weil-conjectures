# Worker report: lem-sfb-split-unipotent-affine-torsor-section

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-split-unipotent-affine-torsor-section.json`: item, unchanged statement and dependencies, three-step induction proof, status `split`.
- `citations.json`: five verbatim statement quotations for every cited node in the three proof steps.
- No new nodes were needed; the existing quotient-reduction, additive-section, and flat-monomorphism statements already provide the one-level ingredients.

## Attachments

None. I searched the project Lean source under `WeilConjectures/` and `Sheaf/` for the exact blueprint tag and for split-unipotent torsor terminology; no declaration states this item without `sorry`.

## WANTED

None. The cited Milne source is present locally at `literature/milne-algebraic-groups_iAG2017.pdf`.

## What was wrong or incomplete

The imported item had an empty proof and status `unsplit`. Its statement is faithful to Milne Proposition 16.55(b): it allows length zero, arbitrary fields and nonreduced affine finite-type bases, and imposes no commutativity or centrality. I retained the statement, statement dependencies, blueprint ancestry, and existing Mathlib searches. The proof now supplies the omitted induction through the given additive quotient series. The only potentially hidden base case is made explicit using the existing flat locally-finitely-presented monomorphism criterion.

## Not duplicates

The item versus `lem-sfb-additive-affine-torsor-section`: the existing node treats only a single `G_a)-torsor; this item handles an iterated, possibly noncommutative split series.
The item versus `lem-sfb-normal-extension-torsor-reduction`: the existing node constructs quotient and kernel torsors and lifts a pair of already-given sections; it does not produce a section from an affine base.
The item versus `lem-sfb-split-solvable-torsors-and-variety`: that node gives Zariski-local triviality for general additive/multiplicative series, while this item gives a global section over an affine base for exclusively additive quotients.
The item versus `lem-pe-flat-lfp-monomorphism-open`: that Mathlib leaf is only the length-zero base-case criterion and does not concern torsors or unipotent groups.

## Review by N0

I read the item source in Milne, Proposition 16.55(b), printed p.344, and Example 2.72, printed p.61, then read the complete statements of all three cited nodes. In step 1, the length-zero series makes the group trivial, so the torsor comparison is exactly the diagonal and gives a monomorphism. The torsor hypotheses provide flatness and local finite presentation; the cited Mathlib leaf says precisely that such a monomorphism is an open immersion. Surjectivity then makes it an isomorphism, whose inverse is a section. This handles the empty base and the trivial group as well.

For step 2, I checked that (N=U_1) is a closed normal affine finite-type subgroup and that the supplied quotient clause matches the quotient geometry statement. The cited quotient node supplies an affine finite-type (Q=U/N), a faithfully flat finitely presented map with scheme-theoretic kernel (N), and the represented fppf quotient. The split-series hypothesis identifies (Q) with (mathbf G_a). I then checked every hypothesis of the cited normal-extension reduction: (U,N,Q) are affine finite-type group schemes, (P	o S) is a represented right (U)-torsor, and the quotient map has the required kernel and fppf quotient property. Its conclusion gives (R=P/N	o S) as a (Q)-torsor, and the pullback over any section as an (N)-torsor.

For step 3, writing the affine scheme (S) as (operatorname{Spec}A) puts the quotient torsor, after transport along (Qsimeqmathbf G_a), under exactly the additive-section node's hypotheses: flat, surjective, finite presentation and the torsor comparison isomorphism. The tail (U_1supseteqcdotssupseteq U_m=1) has length (m-1) and retains smoothness, connectedness, closed-normality and additive quotient hypotheses, so induction applies to (P_a). The normal-reduction statement explicitly says that a section of (P_a) composes to a section of (P), giving (pcirc e=operatorname{id}_S). I tested (m=0), (U=mathbf G_a), a two-step noncommutative unitriangular example, and an empty affine base. No new lemma is hidden in the induction, and every non-elementary cited fact has a matching verbatim quotation in `citations.json`. The item is not a unit key statement, so no unit record was changed.
