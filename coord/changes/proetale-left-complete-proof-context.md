# Sheaf.AlgebraicGeometry.ProEtaleLeftComplete proof context

## Reason

The completed proof adds proof-only imports and private helper lemmas. The stage-3
interface checker conservatively reports these section-level changes as changes to
what importers see. The public declarations, definitions, signatures, visibility and
public imports are unchanged. No consumer adaptation is required.

## Old

The module had proof-only imports of `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
and `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`, with the two theorem proofs left
as `sorry`. It had no private `postnikovStep_quotient` or
`eventually_constant_kernel` declarations.

## New

The module additionally imports `Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic`
and `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` for the completed proof.
It adds the proved private helpers `postnikovStep_quotient` and
`eventually_constant_kernel`; these do not occur in any public signature. The two
existing theorem proof bodies are completed. Public imports and all exported
interfaces remain unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleLeftComplete | U9 | Its proof is completed; no interface adaptation. |
| All importers of this module | unclaimed or current holder | Existing public declarations remain definitionally and textually compatible. |

## Status

landed 20261019T034318-L-420157 2026-10-19 (merge of deliver/U9/Sheaf.AlgebraicGeometry.ProEtaleLeftComplete)
