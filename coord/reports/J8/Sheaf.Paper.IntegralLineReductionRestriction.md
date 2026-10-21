## What changed

Replaced the sorry in
WeilConjectures.IntegralLineReduction.integral_line_reduction_restriction by a
complete assembly of ordinary powers/evaluations, derived reduction/support, and
completeness/restriction. Its signature is unchanged verbatim. The completion
comparison clause uses integralLineTensorComparison_iso, after converting residue
field invertibility into the local stalk unit hypothesis. Signed powers have rank
one by signedLineTensor_equivalence.

Moved the shared data to IntegralLineReductionDefinitions, publicly re-exported by
the original module. The power and finitePower abbreviations use the generic scalar
tensor powers, avoiding dependent transports between two recursive implementations.
The new proved power_eq_coefficient and finitePower_eq_coefficient identify these
objects with the original coefficient powers for every integer exponent. All other
moved signatures and bodies are unchanged. The change record is
coord/changes/J8-integral-line-reduction-data.md.

IntegralLinePowerComparisons proves the ordinary comparison and evaluation formulas.
It uses the existing normalized signed-line scalar comparison and its dual formula,
the scalar-extension/dual local-isomorphism theorem, and the proved local line
pairing. The sheafification unit's naturality identifies the two scalar-extension
presentations on pure tensors. At exponent zero the evaluation is multiplication;
positive evaluations are the actual module/dual pairing; negative evaluations first
swap the factors. These are genuine proofs, with no new holes in this module.

Validation: lcompile.py --all compiled all five modules, including the ordinary
proof and main assembly. The main theorem signature was compared verbatim against
the repository source. The unchanged moved declaration bodies were compared after
removing comments/whitespace, and the two changed constructions have compiled object
equality proofs. Node dependencies, new statement signatures, three search kinds,
and the 100-character Lean line limit were checked.

## Proved and sorry left

Closed the original hole:
WeilConjectures.IntegralLineReduction.integral_line_reduction_restriction.
The item module has zero remaining sorry. The ordinary theorem
WeilConjectures.IntegralLineReduction.integral_line_power_comparisons and both
power-equality theorems are proved. Existing imported declarations can still contain
sorry; no axiom-freedom claim is made for the whole target closure.

Added two named holes, each in its own new module:

- WeilConjectures.IntegralLineReduction.integral_line_derived_comparisons,
  node lem-pur-integral-line-derived-comparisons: the natural derived reduction
  comparisons, normalized on K-flat representatives and strict quotient
  transitions, together with preservation of the same support interval.
- WeilConjectures.IntegralLineReduction.integral_line_restrictions,
  node lem-pur-integral-line-restrictions: preservation of completeness and the
  ordinary/completed inverse equivalences of the integral full subcategory, with
  both evaluation normalizations.

This is a decomposition: one original hole closed, two lower holes added, net minus
one hole closed before accounting for already stated dependencies. The lower
statements are independent proper parts of the original conjunction. Neither repeats
the original conclusion: the first omits completeness and all restrictions, and the
second omits the ordinary and derived reduction comparisons and support assertion.
The ordinary comparisons/evaluations and completion comparison are discharged in the
combining proof. The new docstrings give the source and complete argument for each
remaining part. For zero/empty schemes and zero exponent the same unit constructions
apply; negative exponents use the actual internal dual, not an arbitrary inverse.

## No longer needed

No module is withdrawn and no globally pruned node is claimed. The original theorem
is still required by its unfinished DAG parents despite having no current Lean
importers. The unit's route is preserved.

The original direct proof imports below are removed from the assembly module.
Their mathematical work remains in the new derived/restriction nodes, rather than
being claimed as globally pruned:

- Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
- Sheaf.Paper.IntegralReductionTowerCanonical
- Sheaf.Paper.IntegralOperationsWellDefined
- Sheaf.Algebra.Homology.RoosConeCalculus
- Sheaf.Paper.FiniteFreeCompletedScalarComparison
- Sheaf.AlgebraicGeometry.ProEtaleConstantExact

All original public statement imports remain explicit in the original module
and are also retained by the public shared data module. SignedLineTensorEquivalence and IntegralLineTensorComparisonIso are new
private proof imports of the assembly module, for the rank/completion clause.

The ordinary proof uses SignedLineScalarTensorTower,
SignedLineTensorEquivalence, and ScalarHomOrdinaryTensorComparison. Experimental
imports of ScalarHomTensorComparison, ScalarTensorComparisonTransport,
ScalarInternalHomAdjunction and SheafRingDerivedCoefficientAdjunction were removed
from the derived module because the attempted adapter was not a completed proof.
They are not delivered as unused proof imports. No adopted source declaration or
its dependencies is removed.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical plan is sound. Its originally monolithic Lean predicate
packages independent ordinary, derived and restriction assertions, requiring a shared
data module to split the argument without an import cycle. The generic scalar power
and coefficient power definitions have equal recursive equations but fail Lean's
rfl test at a variable exponent; the proved equality bridges preserve their exact
meaning. The original main theorem signature is preserved, and no mathematical
statement is weakened.

The existing general scalar tensor transport supplies the right derived map, but
specializing all chosen tensor-model instances and proving the representative,
strict-transition and support equations is still unfinished. No partial anonymous
proof hole or arbitrary chosen data is delivered.

## New nodes

- def-pur-integral-line-reduction-data attaches the moved data and formula
  predicates, and the proved equalities of the power implementations.
- lem-pur-integral-line-power-comparisons attaches the proved ordinary power and
  evaluation argument.
- lem-pur-integral-line-derived-comparisons isolates the sourced derived
  reduction, strict-transition and support argument.
- lem-pur-integral-line-restrictions isolates the sourced completeness and
  normalized restriction argument.

The parent proof/dependencies now follow the assembly proof. The definition change
record is coord/changes/J8-integral-line-reduction-data.md. There are no forced
adaptations of modules held by another group.

The first preflight found missing LeanSearch records (LeanFinder and Loogle count
as one search kind) and a definition signature recorded with its body. Both were
corrected. The original public imports are also retained explicitly, including the
unit-route import.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
