## Worker report

The module `Sheaf.AlgebraicGeometry.LowBaseOpenSheafFiniteness` states
`AlgebraicGeometry.Etale.higherDirectImage_constructible_bounded_of_regular_low_base`.
Its only theorem has proof `sorry`; no notion is redefined. The node changes only in `lean`.

The statement matches every hypothesis and conclusion as follows:

| Node clause | Lean rendering |
| --- | --- |
| S a Noetherian scheme | `{S T V : Scheme.{u}} [IsNoetherian S]` |
| S regular | `_hS : IsRegularScheme S` |
| Dimension at most one | `_hdim : topologicalKrullDim S ≤ 1` |
| ell prime | `(ell : ℕ) [Fact ell.Prime]` |
| ell invertible in every local ring of S | `_hinv : ∀ s : S, IsUnit (ell : S.presheaf.stalk s)` |
| A = F_ell | `ULift.{u + 1} (ZMod ell)` throughout; this is the same finite field in the established coefficient universe |
| T → S separated of finite type | `(f : T ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` |
| Any open immersion V → T | `(j : V ⟶ T) [IsOpenImmersion j]` |
| F a module sheaf over the constant A on the ordinary small etale site | `F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))` |
| F constructible | `_hF : Scheme.IsConstructibleEtaleModuleSheaf F` |
| Every R^q j_* F for q ≥ 0 is constructible | First conjunct quantifies `q : ℕ` and applies that same constructibility predicate to `higherDirectImage ... j (q : ℤ) F` |
| Some integer c_F ≥ 0 with vanishing for q > c_F | Second conjunct `∃ cF : ℕ, ∀ q : ℕ, cF < q → IsZero (higherDirectImage ... j (q : ℤ) F)`; natural numbers encode precisely nonnegative integers |
| Bound may depend on F; no assertion for arbitrary sheaves | `cF` is inside the conclusion after the binder F and its constructibility hypothesis |
| No excellence, dualizing-complex or purity assumption | None occurs among the binders |

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`:
  `IsLocallyNoetherian S ∧ IsRegular S`, the recorded regular-scheme predicate.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`:
  dimension in `WithBot ℕ∞`, including the empty space.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsSeparated`:
  the separated clause of the dependency; properness itself is not assumed.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`,
  together with `AlgebraicGeometry.QuasiCompact`: the two finite-type conditions.
- `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`: the recorded finite locally
  closed stratification with constructible strata and finite constant module trivializations.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and the standard `DerivedCategory.Plus`
  and its cohomology functor, as specified by the dependency record. The recorded module
  was absent from the older local source checkout; its current source was read using
  `scompile.py --source WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`,
  `AlgebraicGeometry.Etale.lowerStar`; its bounded-below right derived functor is
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` from
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  The existing abbreviation `AlgebraicGeometry.Etale.higherDirectImage` in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` is exactly degree-q cohomology
  of this derived direct image applied to F in degree zero. It introduces no new notion.

All recorded proof-dependency modules are imported without `public`, except when already
publicly imported as statement dependencies. Mathlib proof leaves are supplied by these
imports. The generic-open and DVR-closed-fibre finiteness nodes have no recorded modules,
so there are no imports for them. Their uses remain explicit in the six-step proof docstring.
No missing statement dependency, new node, dependency repair or statement correction was needed.

Edge cases checked before drafting: empty S (and consequently empty T and V), empty V,
zero F, identity open immersion, degree q = 0, and zero-dimensional regular bases all remain
in the statement. In particular dimension uses ≤ rather than equality, and no nonemptiness,
integrality, field-base or positive-dimension assumption was added. Naturals as the degree
and bound types retain every nonnegative integer. The ordinary small etale site and the
u+1 coefficient universe agree with the landed constructibility interface and its consumers.

Source reading: Zheng, Proposition 3.16(1), printed p.19, with its preceding assumption
that S is regular of dimension ≤ 1 (or quasi-excellent) and the coefficients are Noetherian
and annihilated by an invertible integer. Schemes have trivial inertia, so its bounded
constructibility assertion applies to the open immersion. The node uses its regular-base
alternative and finite field coefficients. The proof docstring reproduces the node's six
steps and all named uses, following ILO XIII 2.3.1(i), printed p.197.

Searches for existing statements, made using `msearch.py` for this group and item:

- LeanFinder: “Higher direct images of constructible finite field etale sheaves under open
  immersion over regular noetherian base dimension at most one are constructible and
  eventually zero”. Eight hits concerned affine limits, constructible subsets and ordinary
  scheme properties; none states higher-direct-image finiteness.
- LeanSearch: “Higher direct images of constructible etale sheaves under an open immersion
  are constructible and bounded over regular dimension one base”. Eight hits concerned
  open restrictions, module stalks and open-immersion properties; none matches.
- Loogle: `AlgebraicGeometry.IsOpenImmersion`. Twelve hits supply the open-immersion
  predicate and stability results, not the assertion of this item.
- Mathlib grep: `constructible.*direct|direct.*constructible|higherDirectImage`, restricted
  to `AlgebraicGeometry/Sites`. No hits.
- Direct source/project rg: `low.base.*(finit|open)|lowBase.*(Finit|Open)` and
  `higherDirectImage.*construct|construct.*higherDirectImage|isConstructible.*[Oo]pen|isConstructible.*regular`.
  Read `OpenImmersionHigherDirectImages.lean`: it assumes schemes of finite type over a
  field, so it does not give the present arbitrary regular Noetherian low-dimensional base.
  Read `LowBaseConstructibleInternalHom.lean`: it is a consumer, not this theorem.
- Direct grep for the exact node id in the upstream source returned no declaration.
  Direct rg for the new theorem name across Mathlib, upstream and project returned no hit.

Validation: `scompile.py Q134 lem-per-low-base-open-sheaf-finiteness` compiled the delivered
file in both sandbox and library modes, cleanly with no warnings or errors.
No statement fault or disputed claim was found.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
