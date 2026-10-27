## What changed

Filled both proofs in `Sheaf.AlgebraicGeometry.LisseModuleInverseImage` with
unchanged declaration signatures and public imports. The specified-cover theorem
uses `InternalModuleOperations.upperComparison`, uniqueness of the sectionwise
left adjoint, the existing universe-general `RingedSitePullback.localLeftIso`,
and Mathlib `SheafOfModules.pullbackObjFreeIso`. Slice continuity follows from
cover preservation and finite-limit preservation; slice pullback existence uses
`module_pushforward_isRightAdjoint_of_universes`.

The lisse corollary reuses the fully proved auxiliary
`CondensedRing.locFree_pullback` in `Sheaf.Paper.FiniteEtaleLocallyFreeModels`,
through a private `import all`. Its predicate `LocFree` is definitionally the
existing `IsLisseCoefficientModule`: the same scheme cover and finite-free
pullbacks, with no extra hypotheses. No public declaration or deferred proof is
added. The existing DAG node records the actual route and dependencies.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.ProEtale.lisseModuleInverseImage_trivializations`.
- `AlgebraicGeometry.ProEtale.isLisseCoefficientModule_upperStar`.

Holes added: zero. Holes remaining in the item: zero. Split-off statements: zero.
The final module compiled cleanly through lcompile.py in 7.3 seconds, with no
increased timeout, heartbeat limit, transparency override, or profiler option.

## No longer needed

Removed four private proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the base-change covering and
  finite-limit facts already exist in the source-library site API.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`: replaced by the already proved
  localization comparison allowing unequal site-object and Hom universes.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: Mathlib's
  free-module pullback comparison supplies the needed coproduct calculation.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: no explicit
  sheaf-module tensor calculation is needed in this file.

The original direct proof dependencies `lem-weil-pbc-localize-ringed-site-morphism`,
`lem-weil-pbc-ringed-topoi-module-adjunction`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`def-pur-sheaf-tensor-product`, and the redundant explicit `lem-sfb-alpha-iso`
were removed from this node's proof_deps. Obsolete top-level tool_uses entries
were deleted. The independent-universe localization and adjoint-existence nodes
replace the corresponding original steps. The coefficient isomorphism remains
available inside the operations transport and proved lisse-pullback auxiliary.

No global withdrawal is claimed: other imports may still transitively use these
modules or declarations. No module, DAG node, source declaration, or unit-level
proof step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original localization dependency fixes the site object and Hom universes
to be equal, while Scheme.ProEt has object universe u+1 and Hom universe u.
The existing universe-general localization theorem fits the actual sites.

The lisse corollary already exists as a proved auxiliary in the finite-etale
local-model module. Its proof uses a general covering-property helper that
keeps the member predicate abstract during checking of cover base change;
reusing it avoids expensive expansion of condensed coefficients in the cover
construction and avoids duplicating that argument. No timeout or transparency
setting is relaxed, and no library definition is changed.

The main theorem transports the actual supplied basis index
`ULift (Fin (r i))`; it does not infer ranks. Rank zero, empty covering families,
the zero coefficient ring, empty schemes, and arbitrary non-flat morphisms are
allowed. The unit-level pullback argument is preserved.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
