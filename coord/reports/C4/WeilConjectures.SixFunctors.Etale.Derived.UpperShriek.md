## What changed

Change record: `coord/changes/upper-shriek-explicit-amplitude.md`.

Repaired the returned delivery's duplicate Sheaf interface. The new
`Sheaf.SixFunctors.Etale.Derived.UpperShriekBoundedBelow` theorem is genuinely more general:
it works for arbitrary Grothendieck-abelian coefficients with an explicit left-adjoint and
upper-amplitude hypothesis, and proves the result directly by adjunction and t-structure
orthogonality. It no longer restates the finite ModuleCat source theorem.

The source item remains API-compatible with the adopted library; its existing bounded-below
instance declaration and one named proof hole are unchanged. A proof-preserving `simpa` cleanup
was made in the mapwise explicit-amplitude theorem. The unclaimed composition implementation
only removes two unused section variables; its public theorem signatures are unchanged. All
three delivered modules and the new Sheaf module compile.

## Proved and sorry left

The item module had one existing `sorry`,
`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek.plus_rightDerivedUpperShriek_obj` (the field
body of `hasBoundedBelowUpperShriek`'s quasi-compact finite-coefficient instance); it remains
unchanged. No item hole was closed and no new sorry was added. The new generic Sheaf theorem is
fully proved with zero `sorry` tokens. The explicit source amplitude criteria remain proved.

## No longer needed

The returned finite-ModuleCat alias theorem and its private duplicate helper
`explicitAmplitudeInterface` are removed from this delivery. The generalized Sheaf theorem
replaces the alias and is strictly more general, so the import-prune duplicate check passes.
The two unused global section variables in the composition implementation are pruned. No
blueprint unit route or required proof dependency is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned Sheaf theorem had exactly the same statement as the source amplitude theorem, so
`import_prune_check.py` correctly rejected it. Generalizing over the coefficient category and
assuming the left-adjoint instance removes the duplication while retaining the needed amplitude
interface. The adopted source signatures remain unchanged, as required by the current landing
gate.

## New nodes

`lem-etale-upper-shriek-explicit-amplitude-interface` records the generalized coefficient-category
interface in `Sheaf.SixFunctors.Etale.Derived.UpperShriekBoundedBelow`; its proof is written in
the new module and uses only the adjunction and t-structure APIs. The node's statement, Lean
record, and proof dependencies match the generalized theorem.

## Forced adaptations

No public signatures were adapted. In
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition`, the
original global section variables for `HasBoundedBelowUpperShrieks` were unused by the affected
theorems and emitted a compiler warning; removing those two variables is a proof-scope cleanup
forced by the delivered module's warning-free compile. The ambient theorem's existing class
parameter and all public declarations remain unchanged.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
