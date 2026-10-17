## What changed

Removed the duplicate private declaration `restricted_counit_hom`, whose statement
was identical to the existing `bounded_counit_hom` in
`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct`. Its restriction calculation
is now performed directly at the sole use in `counit_step_hom`; the module compiles
with the same public interface and the previously repaired `unit_step_hom` and
`counit_step_hom`. The top-level comparison theorem keeps its original statement
and its original named `sorry`. The unused
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB` proof import was removed.
The second reading also removed the redundant direct public import of
`Sheaf.AlgebraicGeometry.OverSquare`: the same module remains publicly exported
through `FiniteDiscreteDerivedCoefficientData` → `FiniteDiscreteCoefficientEncoding`
→ `FiniteDiscreteRealizationFunctor`. No exported import closure changes.

## Proved and sorry left

Closed two original holes: `unit_step_hom` and `counit_step_hom`. Removed the duplicate
`restricted_counit_hom` declaration. No new public statement or split-off theorem was
added, and no definition contains `sorry`.
The one remaining original hole is
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientComparisonData_exchangeSteps`
(node `lem-weil-pbc-coefficient-exchange-from-comparisons`).
Thus 2 of the 3 original local holes are closed, 0 holes are added, and 0 statements
are split off. The helper proofs still depend on open upstream statements; this is
local hole closure, not an axiom-complete proof of the main comparison theorem.

## No longer needed

Removed the proof-only import `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`;
compilation succeeds without it. Also removed the redundant direct
`Sheaf.AlgebraicGeometry.OverSquare` import, whose public transitive export remains.
No old `proof_deps` entry is removed: all three remain part of the documented
unfinished argument. No DAG unit or module was pruned. The existing
three-step comparison, coefficient API, and derived-exchange dependencies remain
needed by the module's helper proofs, statement, and documented route.

## Where the brief, the DAG or earlier work was wrong

The upstream sync had commented out `restricted_counit_hom` because its proof no longer
compiled against the refreshed source. The retained delivery recreated it as a private
helper, but the import-prune review correctly identified that it duplicated the existing
`bounded_counit_hom` statement. This repair removes that declaration and keeps only its
component calculation inline where needed. The top-level theorem remains open as
documented by the DAG.


## Second reading by A4

1. **Interface — pass.** Compared the entire delivered module and node against the
   read-only repository with `diff -u`. Every previously active declaration has
   its original Lean signature tokens; the three private signatures listed in
   `coord/changes/A4-coefficient-exchange-private-signature-formatting.md` are
   line-wrapped to satisfy the delivery tool. All other active signatures, section
   variables and public definitions are byte-identical. The restored `restricted_unit_hom` was
   commented out in the baseline and is private. The removed commented-out
   `restricted_counit_hom` was never an active baseline declaration. There is no
   mathematical statement or definition change. The change record declares only
   the three private signature formatting differences. Removing the redundant
   direct OverSquare import preserves its existing public transitive export.
2. **Proof — pass, partial delivery.** Independently compiled the module using
   `lcompile.py`, then compiled a scratch copy of the final source with `#print axioms`
   for all eleven named declarations. The generic reverse/transport helpers use only
   `propext`, `Classical.choice`, and `Quot.sound`; the geometric helpers and the main
   theorem additionally use inherited `sorryAx`, with no other axioms. The only local
   `sorry` is the original named main theorem, whose source, complete proof in words,
   and node remain. No forbidden declaration or attribute and no hollow definition
   occurs. The first dry run refused three baseline long-line warnings after
   byte-identical signatures were restored. The final source wraps those three
   private signatures as declared in the formatting change record. The generic coefficient restriction API
   depends on the existing disputed upstream theorem
   `boundedConstructible_rightDerivedLowerStar_obj`; this delivery does not assert
   that arbitrary coefficients satisfy its constructibility conclusion.
3. **Split statements — pass (none added).** No new public theorem or split-off hole
   was introduced. Independently searched the two library roots for restriction
   component equations and compared the private counit calculations in
   ContinuousIntegralExchangeTargetAdjunct, ContinuousIntegralExchangeSourceAdjunct,
   and BoundedExchangeAmbient. These private declarations cannot be imported as
   public lemmas; retaining the sole counit calculation inline avoids duplication.
   A fresh Loogle query `"restrictFullyFaithful", "unit"` returned Mathlib's unit and
   counit restriction formulas, exactly the API used here. The restored private
   unit equation is a specialization of that formula, not a restatement of the item.
   The component proofs use no nonempty-scheme, nonzero-ring, Cartesian-square or
   properness assumption, so empty schemes and zero objects cause no exception.
4. **Route and pruning — pass.** Read the restriction/compatibility definitions,
   the specified unit-square-counit factors, CoefficientDerivedFunctorAPI, and
   threeStepComparison. The repaired proofs explicitly identify the cached ambient
   adjunction before unfolding functors, then simplify the restriction identities.
   No shorter public geometric component lemma was found. Removed the redundant
   OverSquare import in addition to the worker's unused ModuleCat.AB import.
   The three-step comparison import remains for the existing unfinished DAG route.
   Read `dag/units/sk-thm-properbasechange.json`: its `realized` statement and three
   steps are unchanged and none is bypassed or pruned.
5. **DAG — pass.** The existing node's statement and Lean record match the unchanged
   main declaration. Its three proof steps and all three proof dependencies remain
   the plan for the existing main hole; the component calculations now implement
   the second step. Its proof-origin note accurately records partial repair rather
   than repeating the baseline's stale claim of a complete Lean proof. There are no
   new nodes to validate.

Second-reading changes: removed the redundant direct OverSquare import, verified
baseline signatures and declared the required line wrapping of three private
signatures in `coord/changes/A4-coefficient-exchange-private-signature-formatting.md`,
corrected report accounting and documented independent compilation, axiom checks,
search, and the inherited upstream limitation. No proof body needed correction.
