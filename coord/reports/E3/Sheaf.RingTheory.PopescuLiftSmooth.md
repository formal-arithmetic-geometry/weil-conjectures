## What changed
Resumed the saved delivery after the earlier tool failure. All three modules compile
through `lcompile.py --all`; `deliver3.py --no-push` now prints OK. Nothing pushed.
The earlier tool mismatch is resolved externally; no project tools were edited.

The unchanged `Algebra.popescu_lift_smooth` statement is reduced to generic-localization
smoothness and the two special-fibre smoothness conclusions. The parent supplies the
explicit witness `algebraMap R d.liftingAlgebra π` for each prime avoiding π.
The two new modules are `Sheaf.RingTheory.PopescuLiftSmoothAway` and
`Sheaf.RingTheory.PopescuLiftSmoothSpecial`. No existing definition, statement,
visibility or public import changed. Both new components have complete proof docstrings
and detailed DAG plans. The generic component omits the unused Noetherian, annihilator,
and special-fibre map hypotheses.

## Proved and sorry left
Hole body closed: `Algebra.popescu_lift_smooth` (one original hole).
Holes added and left: `Algebra.popescu_lift_smooth_away`
(node `lem-weil-pbc-popescu-lift-smooth-away`) and
`Algebra.popescu_lift_smooth_special`
(node `lem-weil-pbc-popescu-lift-smooth-special`).
This is a decomposition: one hole closed, two added, net minus one in the target
import closure. Zero original declarations have an axiom-free proof; the parent
still depends on `sorryAx` through these two statements. No hole was inserted in
any definition, and no data was chosen from an unproved existence theorem.

## No longer needed
Removed from the parent the proof-only imports
`Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime`,
`Sheaf.RingTheory.AnnihilatorElementFlatBaseChange`,
`Sheaf.RingTheory.EquationCountFibreDimensionFlat`,
`Sheaf.RingTheory.ExistsAnnihilatorOfSubsingletonLocalizedModule`,
`Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`,
`Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension`, and the redundant
`Sheaf.RingTheory.SingularIdeal` (the last was already removed by the first worker).
The six substantive chart imports remain in the special component, where their
statements are the ingredients of its documented proof plan. They were removed
from the generic component, which needs only `PopescuLiftPresentation`.
No module is claimed pruned from the targets' transitive import closure.

Every old parent proof dependency absent from its new proof_deps is listed below.
These are redistributed to the component plans, not deleted from the unit route;
preparation stays a statement dependency and a public import of the parent.

- `def-weil-pbc-finitely-presented-algebra`
- `def-weil-pbc-flat-ring-map`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-module-localization-away`
- `def-weil-pbc-smooth-ring-map`
- `lem-weil-pbc-annihilator-element-flat-base-change`
- `lem-weil-pbc-equation-count-fibre-dimension-flat`
- `lem-weil-pbc-finite-module-localization-zero-annihilator`
- `lem-weil-pbc-flat-ring-map-comp`
- `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime`
- `lem-weil-pbc-kahler-differentials-base-change`
- `lem-weil-pbc-kahler-differentials-localization`
- `lem-weil-pbc-kahler-differentials-polynomial-extension`
- `lem-weil-pbc-localization-flat`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-popescu-lift-preparation`
- `lem-weil-pbc-smooth-over-field-dimension-differentials`
- `lem-weil-pbc-smooth-ring-map-base-change-composition`
- `lem-weil-pbc-smooth-ring-map-flat`
- `lem-weil-pbc-smooth-ring-map-principal-localization`

## Where the brief, the DAG or earlier work was wrong
The earlier report described the parent as proved without distinguishing a
conjunction decomposition from an axiom-free proof. The initial component
holes had no natural-language proof, non-self-contained node statements, and
placeholder proof plans. The special component incorrectly called itself generic
smoothness. Its search records duplicated the generic query, without a recorded
search log in this sandbox. The independent reading repaired these faults and
ran fresh searches. LeanSearch returned Internal Server Error; this is recorded
as unavailable, not as evidence of absence. LeanFinder, Loogle and Mathlib grep
returned general ingredients, not a theorem for this explicit prepared quotient.
The local Stacks .tex file was absent; Tag 07CP was read at
https://stacks.math.columbia.edu/tag/07CP and compared with the existing node's
full argument. Neither the source nor the original statement was weakened.

## New nodes
`lem-weil-pbc-popescu-lift-smooth-away` states smoothness of the explicit
localization after inverting π. Its proof plan derives the key equality, eliminates
the auxiliary variables, and uses smoothness of localized polynomial algebras.
`lem-weil-pbc-popescu-lift-smooth-special` states exactly the two special-fibre
conclusions. It retains the source's D_k chart computation, dimension/flatness
argument, conormal coefficient calculation, annihilator transfer and finite-kernel
localization argument. No change record is needed: existing interfaces are unchanged.

## Second reading by E3
1. I compared the delivered parent module with the repository version. The target
statement and every existing declaration signature are unchanged; only the proof and
proof-only imports differ. Verdict: pass.
2. I compiled all three delivered modules with `lcompile.py --all`. The files contain
no forbidden declarations and no `sorry` in definitions. The two remaining `sorry`s
are named public theorems with source and proof docstrings, and their DAG nodes match
their Lean statements. The parent has the expected `sorryAx` dependency through those
split statements. Verdict: pass.
3. I checked both split-off statements against the prepared quotient construction and
the Stacks Project Tag 07CP argument. The generic statement omits hypotheses unused by
the generic localization argument; the special statement retains exactly the special
fibre assumptions and conclusions. Neither duplicates the parent statement. Verdict:
pass.
4. I checked the proof route and pruning. The parent uses the explicit algebra-map
witness for the generic localization and delegates the two special-fibre conclusions
to the corresponding components. The unit route is retained in the component DAG
plans, and removed proof-only imports are listed above. Verdict: pass.
5. I checked the DAG records, declarations, proof dependencies, origins, sources and
search records against the delivered modules. The parent node records the decomposition
and the two new nodes record their separate statements and plans. Verdict: pass.

I changed only the report by adding this second-reading record; no Lean source or DAG
content was changed during the reading.
