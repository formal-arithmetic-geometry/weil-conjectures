## What changed

Retired the duplicate module
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel` in favor of
`WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel`.
Switched all five remaining direct consumers to the upstream public import:
DerivedExtensionRingEquivRawTransport, FlatLocalizedBaseComparison,
AffineDerivedPullbackTensorTilde, PullbackStalkTensorComparison, and
SingleComplexBaseChangeStalkCondition. In the last module, changed the one proof
call from `ModuleCat.extendScalars_additive_sheaf` to the upstream theorem
`ModuleCat.baseDerivedTensor_extendScalars_additive`, which has the same type.
All five consumers are unclaimed; their signatures and definitions are unchanged.

The upstream structure, existence proof and chosen definition are verbatim
identical to the retired implementation. The DAG attachment now records them in
the upstream module. No adopted source-library file is edited. The item is
withdrawn via deleted.txt, so no duplicate declarations remain.

Change record: `coord/changes/P1-base-derived-tensor-model-upstream-reexport.md`.

## Proved and sorry left

This is a zero-hole duplicate-definition repair. Original item: 0 holes; final
item: 0 holes. Holes closed: none. Holes added: none. Split off: none.
All five adapted consumers also contain zero `sorry`. No unproved statement or
hollow definition is introduced. The model construction and its proof remain
unchanged in the upstream library.

## No longer needed

The entire duplicate module
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel` is withdrawn.
Its local copies of `ModuleCat.BaseDerivedTensorCohomologyModel`,
`ModuleCat.nonempty_baseDerivedTensorCohomologyModel`,
`ModuleCat.baseDerivedTensorCohomologyModel`, the private
`exists_tensorExtensionMap`, and the differently named additivity instance
`ModuleCat.extendScalars_additive_sheaf` are unnecessary.

All five imports of the retired Sheaf module are replaced with the upstream
module. The withdrawn module's four public Mathlib imports and its two proof
imports (BaseTensorOrdinaryIso and BaseDerivedTensorCohomologyAction) disappear
with it. The upstream construction still uses those dependencies, so no
proof-dependency node or adopted upstream declaration is pruned. The mathematical
unit route stays intact.

## Where the brief, the DAG or earlier work was wrong

The retire-first item has zero holes and requires duplicate retirement. The
retained-twins record identified the missing upstream name
extendScalars_additive_sheaf as the obstacle. Upstream supplies the same theorem
under baseDerivedTensor_extendScalars_additive, and there is only one explicit
consumer proof call to adapt. The remaining model declarations are identical.
The DAG attachment still named the obsolete duplicate module and is corrected.

Validation: all five adapted consumers compiled through lcompile.py in import
order, each within the per-file limit (1.9, 8.1, 50.2, 3.5, and 34.3 seconds).
The replaced model implementation was also checked verbatim against upstream.

The delivery dry run passed (review class CODEX). Its appended axiom probe
exceeded 60 seconds for AffineDerivedPullbackTensorTilde and
SingleComplexBaseChangeStalkCondition, although both files compiled normally.
An additional import-only axiom scan of their compiled modules passed in 29.2
seconds: 6 and 39 exported declarations respectively, using the preflight axiom
allowlist. The merge still performs its own checks.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
