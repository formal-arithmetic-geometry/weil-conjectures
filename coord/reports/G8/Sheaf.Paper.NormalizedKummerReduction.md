## What changed

Replaced the proof hole of `exists_normalizedKummerReduction` by an assembly of
an integral-unit construction and an unshifted Kummer comparison. The theorem's
signature, existing docstring, public import and all definitions remain unchanged.

The assembly constructs the compatible shift structure on the derived left adjoint
using `Adjunction.leftAdjointCommShift` and `commShift_of_rightAdjoint`. It defines
the target comparison as the left-adjoint shift comparison, the once-shifted
Kummer comparison, and the inverse shift-addition comparison. The private
`shift_mate` and `shift_add_map` lemmas in `NormalizedKummerTarget` prove the corresponding equations from
the adjunction unit, shift naturality, and `commShiftIso_add`. The generic private `shift_normalization` lemma combines these equations;
naturality of `shiftFunctorAdd` gives the exact target normalization with its specified sign.
The private `derived_target_normalization` adapter performs the normalization
conversion over abstract abelian categories. It takes the three endpoints explicitly, avoiding repeated kernel reduction of
the concrete derived category when comparing an endpoint with a short-complex
projection. The comparison and normalization are stored in a private
`TargetNormalizationData` record, and `normalize_targets` performs the
existential assembly over abstract abelian categories. The scheme-specific
theorem only applies this proved helper. The record has no unproved fields.
No equality of general derived-system arrows is inferred from their evaluations.

The item imports `IntegralUnitReduction` and the proved `NormalizedKummerTarget`.
The latter imports `KummerReductionUnit` and
`Mathlib.CategoryTheory.Shift.Adjunction` for its proof. Its self-contained
assembly resides in a separate module to bound kernel checking per file.
The two holed new modules state strictly separate parts of the original argument.
The first has no Kummer input or target comparison and works for any ring
system. The second takes the reduction as input and asserts only the units
comparison in degree one, with no integer-source construction or comparison.
Neither is the original simultaneous existence assertion under another name.

Validation: `lcompile.py --all` accepted all four modules in import order.
After the final record and generic-assembly refactor, a single-file compile
accepted `NormalizedKummerTarget` in 19.6 seconds (11.3 seconds of kernel checking).
The compiler enforces the 60-second limit on each file. Development profiling
options have been removed. The original signature, line lengths, actual hole
count and DAG dependencies were also checked.

## Proved and sorry left

One original hole is replaced by a complete Lean assembly:
`AlgebraicGeometry.ProEtale.SpTowerClasses.exists_normalizedKummerReduction`
(node `lem-sfb-normalized-kummer-reduction`). The new
`AlgebraicGeometry.ProEtale.SpTowerClasses.exists_normalizedKummerTarget`
(node `lem-sfb-normalized-kummer-target`) and its five private categorical helpers
are also proved. This extra module adds no proof hole.

Two new holes remain, each the whole proof of its public theorem:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_integralUnitReduction`
  (`lem-sfb-integral-unit-reduction`, `Sheaf.Paper.IntegralUnitReduction`).
- `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_kummerReductionUnit`
  (`lem-sfb-kummer-reduction-unit`, `Sheaf.Paper.KummerReductionUnit`).

This is a decomposition: one upper hole closed, two lower holes added, net -1.
The complete normalized reduction is not claimed sorry-free. There are zero
remaining holes in the item and normalized-target modules and two in the delivery. No definitions,
instances or private declarations contain `sorry`.

## No longer needed

No original Lean import is removed, and no existing module is withdrawn.
The E-coefficient assertion `det-sp-coefficient-towers-abelian` is no longer
a proof dependency: this obligation concerns the integer quotient system,
and its existing `systemsAbelian` instance already supplies its abelian
structure. No claim is made that the coefficient-towers module is globally
unreachable.

The generic dependencies `lem-pur-derived-change-of-rings` and
`lem-pur-torsion-sheaf-constant-module` remain needed by the two lower
computations. They move out of the item's direct proof dependency list;
they are not pruned from the mathematical argument. The new unit module
imports only `TowerClassReduction`, since it does not use `Rrings`. The item
no longer imports the unshifted Kummer module or shift API directly; the proved
target assembly imports and uses them, so they remain needed.

## Where the brief, the DAG or earlier work was wrong

The existing proof-dependency declarations do not directly state the required
variable-exponent comparison on the entire system. The finite-coefficient
cohomology-normalization API treats a single constant exponent on a site;
it cannot by itself prove the system-derived normalization by evaluating
at every level. `SystemScalarModel` gives normalized derived adjunctions
between ringed-site module categories, while this obligation additionally
needs the integer-module equivalence with abelian towers and its unit.
The new nodes identify these missing constructions rather than replacing
any existing statement or using an E-coefficient theorem with mismatched
endpoints. The original statement and its unit route are retained.

## New nodes

`lem-sfb-integral-unit-reduction` records original proof steps 1--2: construct
the actual derived extension from abelian towers to an arbitrary coefficient
system and identify its integer unit by its generator. Its source is clause
(2) of the current tower-classes proof and the expanded reduction argument.
The plan reuses the constant-ring action equivalence, normalized scalar
model, and generic K-flat change of rings. Empty schemes and zero ring
systems require no added hypotheses.

`lem-sfb-kummer-reduction-unit` records original proof steps 3--4 before the
last shift: compute reduction of units as the actual roots module in degree
-1 and identify the positive boundary as its adjunct. Its source is the same
current blueprint clause. The bounded flat resolution uses positive
exponents n+1 and transitions (l,1), so n=0 and l=2 remain valid. The proof
is on the sequence site before evaluation.

`lem-sfb-normalized-kummer-target` is proved, with no new hole. It packages the
shifted target comparison for a supplied reduction, so the item only combines
the integer source and that target. Its five private helpers contain the
adjunction-unit, shift-addition and naturality argument. The explicit-endpoint
API avoids expanding derived-category localization merely to identify the
third component of a literal short complex with `units`.

Searches used LeanSearch, LeanFinder, Loogle and repository/Mathlib grep.
They found generic adjunction and shift APIs but no existing theorem for
these variable-exponent endpoint comparisons. The new nodes record the
queries and results. No shared interface change or change record is needed.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
