## What changed

Proved `SheafOfModules.FixedTensorLocalization.fixed_tensor_localization_comparison` in
`Sheaf.Algebra.Homology.FixedTensorLocalizationComparison`. All existing declarations retain
their statements and visibility, and all definitions retain their bodies.

Four proved private helpers carry the common argument: the published resolving restriction is
a localization; the explicit shift square is equivalent to `NatTrans.CommShift`; that square
uniquely determines the shift structure; and normalized descent holds for any exact homotopy
functor with a natural comparison on the resolving class. The main theorem applies this
argument in each variable of the published resolving comparison.

The proof first localizes the homotopy functor, extends the resolving comparison, and then uses
the published derived tensor itself as the final descended functor, with identity normalized
comparison. Mathlib's `Functor.commShiftOfLocalization` constructs coherent shifts;
`Functor.isTriangulated_of_precomp_iso` proves exactness with the connecting arrow, and its
triangulated-functor instance proves additivity. Naturality proves the resolution formula.
Full faithfulness of localization proves every uniqueness and compatibility clause, including
shift compatibility of the unique change of factorization. The theorem locally disables the
unused-variable linter because the stronger general descent argument does not need to use
`hSL` and `hSR`; their existing binder names and signed input constraints are preserved.

Updated the item's DAG proof, proof dependencies, proof origin, and obsolete tool approvals to
this argument. Only the item module and its node are changed; there are no consumer adaptations
or interface change records.

## Proved and sorry left

Closed 1 of 1 original holes:
`SheafOfModules.FixedTensorLocalization.fixed_tensor_localization_comparison`
(node `lem-weil-pbc-fixed-tensor-localization-comparison`).

No holes added; no holes remain in the item or any delivered helper. No statements split off.
The private helpers `resolving_isLocalization`, `shiftCompatible_iff`,
`shiftCompatible_unique`, and `normalizedDescent` are all proved.

Validation: the complete module was compiled on the project server using `lcompile.py`.
The delivery command performs the final compilation, axiom probe, and preflight checks.

## No longer needed

Removed the proof-only imports `Sheaf.CategoryTheory.AdditiveLocalizationDescent` and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
Also removed redundant proof imports `Mathlib.CategoryTheory.Localization.Predicate`,
`Mathlib.CategoryTheory.Shift.Localization`, and
`Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`: all three are already available
through the existing public import closure, whose modules and declarations were checked.

The item no longer directly uses `lem-pur-additive-localization-descent`: triangulatedness
implies additivity by Mathlib's proved instance. It no longer directly uses
`lem-pc-kflat-resolution`: the displayed conclusion quantifies over any given resolving
quasi-isomorphism, and naturality proves its formula without choosing a resolution. The
published resolving-localization equivalence already supplies the localization needed for
comparison descent. Its existing internal dependencies remain in place.

Removed these two entries from `proof_deps` and the obsolete top-level `tool_uses` approvals.
`lem-weil-pbc-total-tensor-integer-shifts` remains a statement dependency specifying the signed
input shifts, but is not a separate proof dependency: coherent `CommShift` structures are
already hypotheses. The general descent proof works for any such structures, so `hSL` and
`hSR` may be cleared after their role in specifying the input data.

No module is withdrawn, and no claim is made that these dependencies are globally unused.
The retained public imports support the existing statements and definitions.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original plan can be shortened: prove
triangulatedness before additivity, and use the published fixed derived tensor as the final
factorization after extending its resolving comparison. This removes the separate additive
descent and resolution-existence steps while proving every stated clause. The unit route and
all target statements are preserved.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
