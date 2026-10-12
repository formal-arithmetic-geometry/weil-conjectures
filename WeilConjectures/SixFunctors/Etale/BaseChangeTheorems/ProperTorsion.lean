/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionReduction

/-!
# Proper base change for torsion sheaves

Fix a commutative ring `Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper. This file records the sheaf-level forms of the proper base change theorem
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`:

- for a sheaf `F` of `Λ`-modules killed by a prime `r` (a sheaf of `𝐅_r`-modules), the
  degreewise exchange maps `g⁻¹ Rᵠf_* F ⟶ Rᵠf'_* g'⁻¹ F` are isomorphisms;
- the same for every torsion sheaf `F`, deduced from the prime case by the coefficient
  dévissage `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf`;
- the derived exchange morphism `g^* Rf_* K ⟶ Rf'_* g'^* K` is an isomorphism for every
  bounded below complex `K` with torsion cohomology sheaves;
- the derived exchange morphism `g^* Rf_* F ⟶ Rf'_* g'^* F` is an isomorphism for every torsion
  sheaf `F`, naturally in `F`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isProper_of_prime`: prime
  coefficients.
- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isProper_of_isTorsionSheaf`: torsion
  coefficients.
- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_of_isProper`: bounded below
  complexes with torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_singleFunctor_of_isProper` and
  `AlgebraicGeometry.Etale.properBaseChangeTorsionIso`: the derived exchange morphism of a
  torsion sheaf, and its naturality.

## Blueprint pointers

The general facts used by the dévissage are Mathlib (or earlier project) results:
- `lem-weil-pbc-five-lemma`: `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`;
- `lem-weil-pbc-derived-cohomology-ladder`: `CategoryTheory.Functor.homologySequenceδ_naturality`;
- `lem-weil-pbc-derived-plus-iso-on-cohomology`: `DerivedCategory.Plus.isIso_iff`;
- `lem-weil-pbc-dplus-injective-representative`:
  `DerivedCategory.Plus.exists_injective_nonempty_iso`;
- `lem-weil-pbc-kinjective-shift`: `CochainComplex.instIsKInjectiveObjIntShiftFunctor`;
- `def-weil-pbc-triangles-with-shift`: `CategoryTheory.Pretriangulated.Triangle`;
- `lem-weil-pbc-commshift-nattrans-comp-whisker`: `CategoryTheory.NatTrans.CommShift.comp`;
- `lem-sp-abelian-refinements`: `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`;
- `def-weil-inverse-system`: `CategoryTheory.Functor.ofOpSequence`,
  `CategoryTheory.NatTrans.ofOpSequence`;
- `def-weil-preadditive-category`: `CategoryTheory.Preadditive`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Proper base change with prime coefficients**: for a prime `r`, a proper morphism
`f : X ⟶ Y` (no finite presentation hypothesis), a cartesian square as in the module docstring
and a sheaf `F` of `Λ`-modules on `X_ét` killed by `r`, i.e. a sheaf of `𝐅_r`-modules, the
exchange map `g⁻¹ Rᵠf_* F ⟶ Rᵠf'_* g'⁻¹ F` is an isomorphism in every degree `q`. The sheaf
`F` is torsion, so this is the degreewise form of the proper base change theorem
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology` for `F` placed in
degree `0`.
This is blueprint `lemma-weil-pbc-prime-proper-base-change`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isProper_of_prime [IsProper f]
    (sq : IsPullback g' f' f g) {r : ℕ} (hr : r.Prime)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : r • 𝟙 F = 0) (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  have : IsTorsionModuleSheaf F := .of_nsmul_id_eq_zero Λ hr.pos hF
  exact (Etale.isIso_derivedBaseChangeMapPlus_app_singleFunctor_obj_iff Λ sq F).1
    (Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq _
      (Etale.DerivedCategory.Plus.moduleTorsionHomology_singleFunctor_obj Λ X F)) q

/-- **Torsion coefficient assembly**: for a proper morphism `f : X ⟶ Y`, a cartesian square as
in the module docstring and a torsion sheaf `F` of `Λ`-modules on `X_ét`, the exchange map
`g⁻¹ Rᵠf_* F ⟶ Rᵠf'_* g'⁻¹ F` is an isomorphism in every degree `q`. The prime case
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isProper_of_prime` passes to sheaves
killed by an integer by induction on its prime factors and the five lemma, and to all torsion
sheaves as filtered colimits, along which the source and the target of the exchange map commute
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf`); the proper map `f`
is quasi-compact and quasi-separated.
This is blueprint `lemma-weil-pbc-torsion-assembly`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isProper_of_isTorsionSheaf [IsProper f]
    (sq : IsPullback g' f' f g) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  Etale.isIso_baseChangeHomologyMap_of_isTorsionSheaf Λ sq
    (fun _ hr E hE q ↦ Etale.isIso_baseChangeHomologyMap_of_isProper_of_prime Λ sq hr E hE q) F q

/-- **Bounded below derived proper base change**: for a proper morphism `f : X ⟶ Y`, a
cartesian square as in the module docstring and a complex `K ∈ D⁺(X_ét, Λ)` all of whose
cohomology sheaves are torsion, the derived exchange morphism `g^* Rf_* K ⟶ Rf'_* g'^* K` is an
isomorphism in `D⁺(Y'_ét, Λ)`. No hypothesis is put on `g`.

It is deduced from the sheaf-level statement
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_isProper_of_isTorsionSheaf` (the `E₂`
terms of the hypercohomology spectral sequences): both sides do not lower the cohomological
degree, so `Hⁿ` of both sides only depends on the truncation `τ_{≤ n} K`, a finite iterated
extension of its shifted torsion cohomology sheaves
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_of_forall_isTorsionSheaf`).
This is blueprint `thm-weil-pbc-bounded-below`. -/
@[stacks 0DDE]
theorem Etale.isIso_derivedBaseChangeMapPlus_app_of_isProper [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.moduleTorsionHomology Λ X K) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  Etale.isIso_derivedBaseChangeMapPlus_app_of_forall_isTorsionSheaf Λ sq
    (fun F hF q ↦ have : IsTorsionModuleSheaf F := hF
      Etale.isIso_baseChangeHomologyMap_of_isProper_of_isTorsionSheaf Λ sq F q) K hK

/-- **Finite-torsion proper base change**: for a proper morphism `f : X ⟶ Y`, a cartesian
square as in the module docstring and a torsion sheaf `F` of `Λ`-modules on `X_ét`, the derived
exchange morphism `g^* Rf_* F ⟶ Rf'_* g'^* F` of `F` placed in degree `0` is an isomorphism in
`D⁺(Y'_ét, Λ)`: the complex `F[0]` has torsion cohomology, so this is the bounded below
theorem `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_of_isProper` for `F[0]`.

These isomorphisms are natural in `F` (`AlgebraicGeometry.Etale.properBaseChangeTorsionIso`),
and, as for every component of `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`, they are the
identity for identity squares (`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_id`) and
compatible with horizontal and vertical pasting
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_horiz`,
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_vert`).
This is blueprint `prop-weil-proet-finite-proper-base-change`. -/
@[stacks 095T]
theorem Etale.isIso_derivedBaseChangeMapPlus_app_singleFunctor_of_isProper [IsProper f]
    (sq : IsPullback g' f' f g) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  Etale.isIso_derivedBaseChangeMapPlus_app_of_isProper Λ sq _
    (Etale.DerivedCategory.Plus.moduleTorsionHomology_singleFunctor_obj Λ X F)

/-- The natural isomorphism `g^* Rf_* F ≅ Rf'_* g'^* F` of functors of a torsion sheaf `F` of
`Λ`-modules on `X_ét`, for a proper morphism `f` and a cartesian square as in the module
docstring: the derived exchange morphism, restricted to torsion sheaves placed in degree `0`
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_app_singleFunctor_of_isProper`). -/
noncomputable def Etale.properBaseChangeTorsionIso [IsProper f] (sq : IsPullback g' f' f g) :
    (Scheme.isTorsionModuleSheaf Λ X).ι ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus ⋙
          ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      (Scheme.isTorsionModuleSheaf Λ X).ι ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        ((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ⋙
          (f')_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus :=
  have : ∀ F : (Scheme.isTorsionModuleSheaf Λ X).FullSubcategory,
      IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F.obj)) := fun F ↦
    have : IsTorsionModuleSheaf F.obj := F.property
    Etale.isIso_derivedBaseChangeMapPlus_app_singleFunctor_of_isProper Λ sq F.obj
  have : IsIso (Functor.whiskerLeft
      ((Scheme.isTorsionModuleSheaf Λ X).ι ⋙ DerivedCategory.Plus.singleFunctor _ 0)
      (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
  asIso (Functor.whiskerLeft
      ((Scheme.isTorsionModuleSheaf Λ X).ι ⋙ DerivedCategory.Plus.singleFunctor _ 0)
      (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq))

/-- The component of `AlgebraicGeometry.Etale.properBaseChangeTorsionIso` at a torsion sheaf is
the derived exchange morphism of that sheaf. -/
@[simp]
lemma Etale.properBaseChangeTorsionIso_hom_app [IsProper f] (sq : IsPullback g' f' f g)
    (F : (Scheme.isTorsionModuleSheaf Λ X).FullSubcategory) :
    (Etale.properBaseChangeTorsionIso Λ sq).hom.app F =
      (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F.obj) :=
  rfl

end AlgebraicGeometry
