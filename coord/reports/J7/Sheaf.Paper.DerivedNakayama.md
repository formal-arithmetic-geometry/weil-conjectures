## What changed

Proved `AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama`
from the existing resolution and first-reduction statements, with the public signature
unchanged. The private `twoTermResolution` constructs `HomologicalComplex.double`
in degrees -1 and 0, constructs its augmentation, and checks its quasi-isomorphism
on homology. The exact sequence is transported by `regularPullbackIso`, and
faithfulness identifies its quotient map with `AdicCompletion.finiteUnit`.

The private `reductionComparison` specializes the existing proved generic
`Mod.residueDerivedTensorIso` and `mapModComapIso` to identify restricted canonical
scalar extension with tensor reduction. Private proved homology arguments show
that exact faithful restriction detects zero objects and that exact conservative
restriction detects isomorphisms. This bridges the coefficient-category difference
before applying the two consequences of `derived_nakayama_first_reduction`.

Updated the item's node to record this argument and its actual dependencies.
Validation: `lcompile.py` compiled the final module cleanly on the project server
in 20.6 seconds (exit code 0, no warnings). A source comparison confirms that the
public theorem statement is verbatim unchanged, every line is at most 100 characters,
and no `sorry` remains. The new dependency does not reach the item in the DAG.

All edits are confined to the item, its node and this report. No signature,
definition or public import changes; no forced adaptations.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama`
(node `sk-lem-pe-derived-nakayama`). Added 0 holes and split off 0 statements.
There are no remaining `sorry` declarations in this delivery.
The imported `AlgebraicGeometry.ProEtale.derived_nakayama_first_reduction`
remains an existing proof dependency, as intended by the stage-3 brief.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
and `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`.
The nodes `lem-weil-pbc-standard-quotients-perfect` and
`def-weil-pbc-strict-perfect-coefficient-package` are not needed directly by this
proof: the coefficient-resolution dependency already provides the short exact
sequence, and the public conclusion specifies a bounded rank-one representative
rather than a local-perfectness predicate. The two-term complex and its homology
calculation are constructed directly. These modules and declarations are retained
in the library for their other consumers. No module is withdrawn. The obsolete
item-level `tool_uses` approval for ordinary quotient perfectness is removed.

## Where the brief, the DAG or earlier work was wrong

The planned direct applications of the first-reduction lemma require a coefficient
comparison: its reductions take values in the derived category of finite-ring
modules, whereas the item's reductions are tensor functors in the integral derived
category. The existing proved generic scalar-tensor presentation supplies this
comparison without changing either statement or adding a new mathematical result.
The resolution node states an exact sequence and cone comparison, so the explicit
bounded resolution and its augmentation still require the double-complex argument
implemented here.

Searches used `msearch.py` with LeanFinder, Loogle and grep, and direct `rg` in
Mathlib and both library roots. They found Mathlib's double-complex construction,
the private module-specific model in `StandardQuotientsPerfect`, and the proved
generic `Mod.residueDerivedTensorIso` in `IntegralResidueTensorPresentation`.
The private resolution argument generalizes the existing module-specific homology
calculation to an arbitrary abelian category. No new statement or edge-case
restriction is introduced: positive exponent n+1 includes first reduction, and the
proof works for empty schemes, zero objects, identities and unbounded complexes.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
