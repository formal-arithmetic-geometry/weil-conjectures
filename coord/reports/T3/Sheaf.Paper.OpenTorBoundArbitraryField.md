## What changed

Retained the earlier attempt and completed both helper proofs. The signature of
`AlgebraicGeometry.Etale.open_tor_bound_arbitrary_field` is unchanged. It combines the
proved finite constant-module bound with the proved extension to arbitrary module sheaves.

`Sheaf.Paper.OpenTorBoundFiniteConstantTests` proves the lower bound by a bounded-below
injective representative, compares the existing unbounded right derived functor with the
one supplied by `finiteCDDerivedUpperBound` using Kan-extension uniqueness, and transfers
both bounds through the assumed projection isomorphism. It uses the existing derived
functor and constructs no arbitrary new derived object.

`Sheaf.Paper.OpenTorBoundStalkFilteredExtension` now proves the remaining half. The existing
`exists_derivedTensor_stalk_iso` and exact-functor homology/single comparisons turn finite
constant tests into finite module tests at each stalk. Private proved helpers show that
`N ↦ H^q(C ⊗ᴸ N[0])` preserves filtered colimits: use a K-flat representative of C,
the tensor localization counit, colimit preservation of degree-zero embedding and tensor,
and exactness of filtered module colimits. `Module.fgSystem.equiv` and
`ModuleCat.directLimitIsColimit` express every module as the filtered colimit of its finite
submodules. Joint faithfulness of module-valued geometric stalks then proves zero
cohomology sheaves by identifying their identity with zero.

The two new DAG records have self-contained statements, exact Lean signatures, sources,
proof steps, actual logged searches and their blueprint ancestor. The item's proof record
now records its two immediate helper dependencies. All three modules compiled in dependency order without errors or warnings. The extension
helper compiled in 36.9 seconds and the item in 4.0 seconds. The required delivery dry run
checks the final sources, records and axioms before push.

## Proved and sorry left

Original item: one hole, closed:
`AlgebraicGeometry.Etale.open_tor_bound_arbitrary_field`
(node `lem-sf-open-tor-bound-arbitrary-field`).

Both new public helper theorems are proved:

- `AlgebraicGeometry.Etale.open_tor_bound_finite_constant_tests`
  (node `lem-sf-open-tor-bound-finite-constant-tests`).
- `AlgebraicGeometry.Etale.open_tor_bound_stalk_filtered_extension`
  (node `lem-sf-open-tor-bound-stalk-filtered-extension`).

There are zero `sorry`s in the three delivered modules and zero holes added. This closes
one assigned hole from existing library declarations; it leaves no split-off obligations.
The proof uses existing declarations that themselves may still depend on `sorry`, notably
`finiteCDDerivedUpperBound` and `exists_derivedTensor_stalk_iso`; proving those is outside
this delivery. No definition, existing statement or target signature is changed.

Edge cases: zero ring, empty scheme, empty interval, and infinitely generated modules.
No projective-dimension assumption on finite modules or commutation of Rj_* with colimits
is used. Finitely generated submodules are finite by `Module.finite_of_finite`.

## No longer needed

All fifteen original proof-only imports are removed from the item module. It now directly
imports the two proved helpers. Two original imports are used inside those helpers:
`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives` and
`Sheaf.CategoryTheory.DerivedCategory.FiniteCDDerivedUpperBound`. The geometric-stalk
conservativity API in `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` is used
by the extension helper (available through its derived-stalk import). These are relocations,
not pruning of their underlying obligations.

The following original imports and proof dependency nodes are not used by this route:

- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
  (`lem-weil-pbc-module-sheaves-enough-injectives`): existing Grothendieck-abelian instances
  provide enough injectives for the actual module-sheaf category.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
  (`lem-weil-pbc-module-direct-image-left-exact`): existing direct-image instances give
  additivity and preservation of finite limits.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
  (`prop-weil-pbc-kinjective-resolutions-exist`): use existing source K-injective instances.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
  (`lem-weil-pbc-kinjective-total-derived`): use source `rightDerivedFunctorObjQIso` and
  Kan-extension uniqueness directly.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
  (`lem-weil-pbc-right-derived-plus-injective`): compute the unbounded functor directly
  on the K-injective representative, using source `RightDerivedFunctor.PlusCompatibility`
  for the degree-zero classical comparison.
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback` (`lem-kun-stalk-as-pullback`),
  `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
  (`lem-kun-inverse-image-monoidal`), and
  `Sheaf.AlgebraicGeometry.GeometricStalkCohomology` (`lem-kun-stalks-of-cohomology`):
  the module-valued unbounded derived-stalk tensor theorem supplies the tensor comparison;
  the exact-functor API supplies the homology comparison.
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
  (`lem-weil-pbc-constant-sheaf-geometric-stalk`): use the proved module-valued
  `Point.sheafFiberConstantSheafIso` directly.
- `Sheaf.Algebra.Homology.FilteredColimitDerivedTensor`
  (`lem-pc-filtered-colimit-derived-tensor`): the private K-flat computation proves the
  required colimit comparison for the existing monoidal tensor directly. That node's
  statement concerns a separately chosen mixed-tensor bifunctor, requiring additional
  identifications for this use.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar` and
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`: neither comparison is used.

The old top-level `tool_uses` entries of the item are withdrawn because its immediate proof
uses the two helper nodes. No claim is made that a named module leaves the entire targets'
import closure; other consumers and transitive dependencies can still use it. No module
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The retained finite-test helper had a `sorry` and its docstring copied unrelated stalk
steps. The retained node records had empty proofs/search lists, nonverbatim Lean fields,
and an incorrect blueprint ancestor. Those records and docstrings are repaired.

The earlier report described the comparisons as unavailable. The current source library
provides the needed derived-functor comparisons, a module-valued derived-stalk tensor
theorem, exact-functor cohomology comparisons, and a module-valued constant-stalk iso.
The remaining module colimit argument is now proved explicitly.

The supplied source labels the Tor passage Step 3, while the current blueprint places the
closed-support argument in its second paragraph. Both places are identified in the new
records. The unit's route is preserved.

The extension helper uses `lem-sfb-etale-derived-tensor-stalk` as the existing general tool
for unbounded module-valued tensor at stalks; this is not a replacement of the unit's route.
No statement of this unit supplied that generic comparison. The independent reader should
record its tool use if the maintainer's route check requires it.

## New nodes

- `lem-sf-open-tor-bound-finite-constant-tests`, module
  `Sheaf.Paper.OpenTorBoundFiniteConstantTests`: proved, zero holes.
- `lem-sf-open-tor-bound-stalk-filtered-extension`, module
  `Sheaf.Paper.OpenTorBoundStalkFilteredExtension`: proved, zero holes.

No change record is needed: all existing signatures and definitions are preserved.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
