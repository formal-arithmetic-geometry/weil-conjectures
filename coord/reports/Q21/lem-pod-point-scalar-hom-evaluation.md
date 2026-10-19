# Worker report: lem-pod-point-scalar-hom-evaluation

## Files written

- `dag/nodes/sec-six-functors/lem-pod-point-scalar-hom-evaluation.json`: repaired statement and seven proof steps; Mathlib verdict remains no exact match for the completed pro-etale internal-Hom/sections square.
- `citations.json`: 18 verbatim statement quotations, one for each cited node in each proof step.
- `report.md`: this report.

No new nodes or Mathlib leaves were created.

## Attachments

None. I searched `WeilConjectures/` for the item tag, its scalar/Hom terminology and likely declaration names. The only nearby declaration, `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual` in `SixFunctors/Etale/Derived/Point.lean`, has `sorry`, concerns finite discrete etale coefficients, and does not state this integral completed-coefficient square.

## WANTED

None.

## STATEMENT-DISPUTED

The imported wording was under-specified at the point returned by the maintainer. The statement of `lem-pur-integral-operations-scalar-extension` gives naturality, identity, and tower coherence, but does not choose the quotient-level multiplication map. Those properties allow scalar twists: already for $P=R$ in degree zero, multiplying the comparison by a compatible unit family can preserve naturality, identity, and tower coherence while changing the required evaluation square. I repaired the statement by explicitly choosing the quotient-normalized comparison whose finite-quotient tensor component sends
`(x ⊗ ā) ⊗ (y ⊗ b̄)` to `(x ⊗ y) ⊗ ā b̄`, compatibly with transitions, with the Hom component its evaluation transpose. This is the canonical comparison intended by the route and removes the ambiguity without weakening the target conclusion.

## What was wrong and what was corrected

The returned Step 3 cited the scalar-operations node for a multiplication normalization that its statement does not contain. Step 3 now treats the quotient normalization as an explicit part of the item and checks it against the actual completion comparison `χ`: the finite-quotient maps agree on pure tensors and on all transitions, and both have zero shifted-product component, so the equality survives the strict derived-limit cone. Step 6 now uses this same normalization to justify the identity and tower associator clauses, rather than deriving them from coherence alone. The statement, proof dependencies and summary were updated accordingly; no new node is needed.

## What could not be finished

No mathematical part of this one-level split remains. The required server checks and delivery dry run are the remaining validation steps.

## Review by Q21

I reread the repaired item, the ancestor `lem-pod-point-dualizing-complex`, and `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`. I also reread the full statements of every cited node: `lem-pod-point-completed-evaluation`, `def-weil-finite-tor-amplitude`, `lem-sf-point-fibre-derived-tensor`, `def-pur-hom-complex`, `lem-pod-point-derived-hom-evaluation`, `lem-weil-finite-free-completed-scalar-comparison`, `lem-pur-integral-operations-scalar-extension`, `lem-weil-point-sections-scalar-extension`, and `def-weil-rationalization-karoubi`. The 18 entries in `citations.json` quote those statements verbatim.

Step 1 uses the completed point-evaluation statement for the internal-Hom models, completeness and completed evaluation, the finite-Tor-amplitude definition for the common bounded interval, and the point-fibre tensor comparison for the tensor model. I checked that tensoring the finite-projective retractions preserves the required hypotheses. Step 2 uses the Hom-complex differential and the signed evaluation statement; its balancing, differential and Koszul-sign calculations are elementary once those statements are fixed.

The repaired Step 3 uses the finite-free comparison for the explicit quotient components and zero shifted-product component of `χ`, and the scalar-operations node for the stipulated operation comparison and transpose. The newly explicit item normalization supplies the multiplication formula; I checked the two strict quotient towers on pure tensors before taking the cone, which is the missing compatibility identified in the return. Step 4 uses the completed-evaluation and sections-scalar statements plus the point-fibre tensor constraint to identify the prescribed vertical maps and computes both sides as `f(x)ab`. Step 5 checks precomposition on a cochain map and then invokes the naturality clauses of the three cited comparisons. Step 6 checks $L=E$ and a tower $E\subset L\subset M$ on $f(x)abcd$; the quotient normalization fixes the actual associator, while the sections statement supplies its conjugation equation. Step 7 uses the rational sections clause and the stated localized-Hom model; the fraction calculation verifies naturality for localized morphisms.

I tested $P=0$, $P=R$ in degree zero, a shifted free term (the Koszul sign), a two-term finite-free complex, finite-projective retracts, $L=E$, a three-field tower, zero morphisms and alternate fraction representatives. I checked each step is below 2000 characters and contains no hidden comparison justified by “transport” or “the same calculation”. No SGA source is used. The prior return’s C3/C4/E5 issue is corrected by the explicit quotient normalization and the finite-level compatibility calculation.
