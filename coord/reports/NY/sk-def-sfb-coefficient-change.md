## Worker report

This item is already stated by the published upstream module
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`; no new
module is introduced.  The node's `lean` record therefore uses the existing
`AlgebraicGeometry.ProEtale.coefficientMap` declaration and lists the four
companion declarations that render the remaining coefficient-change clauses.

The coefficient-change input is a morphism `a : Λ ⟶ Λ'` of condensed ring
objects, represented in Lean by `Λ Λ' : Sheaf (coherentTopology Profinite.{u})
Ab.{u + 1}`, `[MonObj Λ]`, `[MonObj Λ']`, `(a : Λ ⟶ Λ')`, and `[IsMonHom a]`.
For a scheme `X : Scheme.{u}`, the definition

```
noncomputable abbrev coefficientMap (X : Scheme.{u}) :
    condensedRingObj Λ X ⟶ condensedRingObj Λ' X
```

is `(upperStarFromPoint X).map a`; this is the map `a_X = p_X^* a` between the
pulled-back coefficient ring objects.  The `coefficientRing` and
`condensedRingObj` declarations from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` provide the endpoints
and their commutative ring-object structures.

The functoriality clauses are rendered by
`AlgebraicGeometry.ProEtale.coefficientMap_id` and
`AlgebraicGeometry.ProEtale.coefficientMap_comp` in the same module:
`coefficientMap (𝟙 Λ) X = 𝟙 _` and
`coefficientMap (a ≫ b) X = coefficientMap a X ≫ coefficientMap b X`.
The derived extension clause is the specialization, at
`a_X = coefficientMap a X`, of
`CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction` from
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`: its left
functor is `L(Mod.extendScalars (coefficientMap a X))`, identified with
`Λ'_X ⊗ᴸ_{Λ_X} -`, and its right adjoint is
`D(Mod.comap (coefficientMap a X))`, the levelwise restriction of scalars.
The derived-category and module-object conventions are supplied by
`CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and
`CategoryTheory.Mod`/`CategoryTheory.ModObj` respectively.

For `f : X ⟶ Y`, the first compatibility square is exactly
`AlgebraicGeometry.ProEtale.map_coefficientMap_comp_condensedPullbackHom`:
`(f)^*[Ab.{u + 1}].map (coefficientMap a Y) ≫ condensedPullbackHom Λ' f =
condensedPullbackHom Λ f ≫ coefficientMap a X`.  This renders
`α'_f ∘ f^* a_Y = a_X ∘ α_f`, with
`condensedPullbackHom` the recorded coefficient morphism `α_f`.  The second
square is exactly
`AlgebraicGeometry.ProEtale.condensedPushforwardHom_comp_map_coefficientMap`:
`condensedPushforwardHom Λ f ≫ (f)_*[Ab.{u + 1}].map (coefficientMap a X) =
coefficientMap a Y ≫ condensedPushforwardHom Λ' f`.  This renders
`f_*a_X ∘ η_f = η'_f ∘ a_Y`, with `condensedPushforwardHom` the recorded
coefficient morphism `η_f`.

The dependency declarations used are:

* `sk-def-sfb-condensed-ring`: `Profinite.continuousMapRingObjOfUniverse`
  (`Sheaf.Topology.ContinuousMapCondensedRing`), together with the existing
  condensed ring-object interface and its commutative instances.
* `sk-def-sfb-pullback-from-point`:
  `AlgebraicGeometry.ProEtale.sfbPullbackFromPoint`,
  `sfbPullbackFromPointRightAdjoint`, and `sfbPullbackFromPoint_spec` in
  `Sheaf.AlgebraicGeometry.ProEtalePointPullback`; upstream
  `upperStarFromPoint` is the corresponding published implementation.
* `sk-def-sfb-pulled-back-coefficients`:
  `AlgebraicGeometry.ProEtale.coefficientRing`,
  `coefficientRing_X`, `condensedRingObj`, and
  `isCommMonObj_condensedRingObj` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
* `sk-def-sfb-derived-extension-of-scalars`:
  `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction` and its
  exported derived-extension and restriction interfaces in
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`.
* `sk-def-sfb-derived-categories`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` in
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
* `sk-def-sfb-module-objects`: the closed upstream Mathlib declarations
  `CategoryTheory.ModObj`, `CategoryTheory.Mod`, `CategoryTheory.Mod.forget`,
  and `CategoryTheory.Mod.regular` in `Mathlib.CategoryTheory.Monoidal.Mod`.
* `sk-def-sfb-coefficient-morphisms`:
  `condensedPullbackHom`, `coefficientPullbackIso`,
  `condensedPushforwardHom`, and their `IsMonHom` declarations in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
* `def-sfb-finite-upper-star` and `def-sfb-finite-lower-star`:
  `AlgebraicGeometry.ProEtale.upperStar` and `lowerStar` in
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`.

Edge cases checked: `X` and `Y` are arbitrary schemes in the common universe
`u`; the identity map and an arbitrary composite of coefficient morphisms are
included; no nonemptiness, flatness, finiteness, or commutativity hypothesis is
added to the underlying `coefficientMap` beyond the node's commutative-ring
specialization; and the source and target of each displayed square are the
specified coefficient ring objects.  The zero morphism and identity morphism
cases are covered by the functoriality equations, and the construction does not
exclude the empty scheme.

Searches for an existing declaration were made before recording the upstream
binding: `msearch.py ... leanfinder` for “coefficient change condensed
coefficients p_X inverse image ring objects” returned only generic condensed
module and free-module declarations; `msearch.py ... loogle` for
`AlgebraicGeometry.ProEtale.coefficientMap, CategoryTheory.Functor.map` found no
Loogle identifier; `msearch.py ... grep` for `coefficientMap|coefficient change
[Mathlib]` found no Mathlib match; `rg` over `WeilConjectures/` located the
published `ChangeOfCoefficients.lean` module.  Reading that module with
`scompile.py --source WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
confirmed the exact definition, identity and composition equations, and both
compatibility-square declarations listed in the node record.  No
`STATEMENT-DISPUTED` flag or node fault remains.

## Second reading by NY

I reread the node, its source `_section.md`, the published
`ChangeOfCoefficients.lean` declarations, and every statement dependency.  The
existing binding supplies the inverse-image coefficient map, identity and
composition laws, and both `α_f` and `η_f` squares verbatim.  The generic derived
extension declaration supplies the stated `T^X` and its adjunction after the
recorded coefficient-map specialization.  No hypothesis is strengthened or
omitted, and no new module or dependency repair is needed.
