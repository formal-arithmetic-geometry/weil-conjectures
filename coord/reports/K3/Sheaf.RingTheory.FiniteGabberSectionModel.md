## What changed

Proved `Algebra.exists_finite_gabber_section_model` with its signature unchanged,
using the two fully proved new modules `Sheaf.RingTheory.FiniteIntegralAwayApproximation`
and `Sheaf.RingTheory.QuotientSectionFactorTransfer`. The item adds only proof imports:
those helpers and Mathlib tensor quotients. The original section splitting,
integral-closure localization, finite approximation, and quotient splitting route stays.

Repair of the returned delivery: removed all three duplicate private declarations
from FiniteIntegralAwayApproximation:
`Algebra.finite_subalgebra_mem_map`, `Algebra.finite_subalgebra_for_congruence`, and
`Algebra.finite_of_fg_subalgebra`. These are private in the existing
HenselianIntegralIdempotentLifting module, so importing that module cannot expose them.
Instead, the approximation proof imports
`Mathlib.LinearAlgebra.Finsupp.LinearCombination` and applies its existing
`Finsupp.mem_span_range_iff_exists_finsupp`. The finite support explicitly supplies
the ideal-expression coefficients to adjoin along with g and the numerators.
`Algebra.finite_adjoin_of_finite_of_isIntegral` proves finiteness directly.
No duplicate helper is renamed or restated. The approximation node records this route.

The quotient transfer constructs its complement as an actual idempotent corner.
No definition chooses arbitrary data from an unproved existence theorem.
No existing module other than the assigned item is adapted; no interface changes.

## Proved and sorry left

Closed `Algebra.exists_finite_gabber_section_model`
(`lem-weil-pbc-finite-gabber-section-model`): 1 of 1 original holes.
The new theorems `Algebra.exists_finite_integral_away_approximation`
(`lem-weil-pbc-finite-integral-away-approximation`) and
`Algebra.quotient_section_factor_transfer`
(`lem-weil-pbc-quotient-section-factor-transfer`) are fully proved.
No sorry remains in these three modules, and no hole was added or split off.
Existing upstream sorry dependencies are unchanged; closing this local hole
is not a claim that the entire target import closure is sorry-free.

## No longer needed

Removed the three duplicate private helper declarations named above.
The new proof needs neither their span-induction proofs nor an import of
`Sheaf.RingTheory.HenselianIntegralIdempotentLifting`.
No original import, DAG dependency, module, or unit step is pruned.
Finite integral generators are still used through the approximation helper.
The original five proof dependencies remain used directly or through these helpers.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery and its second readings missed that the three private
helpers duplicate existing declarations in HenselianIntegralIdempotentLifting.
The return is correct. This repair removes all three and uses existing Mathlib
results in a direct finite-support construction, without changing the private
visibility or signatures of the other group's module.

The earlier approximation node described span induction; it now describes the
actual finite-support proof. All public theorem statements are unchanged.
The quotient transfer is represented by a separate fully proved node because
its Lean proof requires quotient-localization compatibility and an explicit
corner product equivalence, not just informal identification of a factor.

Edge cases: I=top and trivial quotient rings require no properness hypothesis;
b=0 and zero localizations are covered by the fraction criteria. The generator
set and coefficient support may be empty. Outside the support, coefficients
are zero, hence belong to the adjoin. I=0 introduces no extra assumptions.

## New nodes

`lem-weil-pbc-finite-integral-away-approximation`: finite subalgebra approximation
retaining the parameter's idempotent congruence and localization bijectivity.
Fully proved; source Stacks Tag 09XI, the finite B'' construction.
The repaired proof uses Mathlib's finite-support linear-combination theorem and
finite integral adjoin theorem. Its recorded proof and proof_origin were updated.

`lem-weil-pbc-quotient-section-factor-transfer`: transfer of the specified section
factor through localized subalgebra inclusion. Fully proved; source Stacks
Tag 09XI, the B''/IB'' decomposition. Its proof and statement are unchanged.

No additional node or change record is introduced by this repair.

## Second reading by K3

1. Compared `lean/Sheaf/RingTheory/FiniteGabberSectionModel.lean` with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and proof bodies changed.

2. Compiled all three delivered modules with `lcompile.py`; they compile without errors or warnings. Searched for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`; none remain. The proofs use only the permitted kernel axioms through their dependencies.

3. Checked the new statements against their node statements and source route. The finite approximation and quotient transfer lemmas are strictly intermediate results, true, and required by the target proof; neither duplicates an existing library declaration.

4. Reviewed imports and pruning. The target keeps the unit route through quotient splitting, integral closure localization, finite approximation, and quotient transfer. The removed duplicate private helpers and their unused Henselian import are recorded above; no required dependency was pruned.

5. Checked DAG alignment: proof steps, proof dependencies, proof origins, Lean declarations, and new node records match the implemented proofs. No target statement or definition changed.

Changed only the missing review record in this report; no Lean code or node content was altered during second reading.
