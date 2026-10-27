/-
Copyright (c) 2026 Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil Conjectures contributors
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction

/-!
# Reduction of a derived mate using the unprimed counit

Source: `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusAdjunction.lean`,
proof of `derivedPlus_mateEquiv_app_fac`, mate expansion and counit reduction
(blueprint: lem-trf-derived-mate-counit-reduction).
-/

@[expose] public section

universe uA uB uA' uB' vA vB vA' vB' wA wB wA' wB'

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- A derived mate, precomposed with the unprimed right-derived comparison and the inverse
localization comparison for `G`, reduces to the transpose of the localized counit composite.
Neither the square nor either right-derived comparison is assumed invertible, and `H` need
not preserve injectives.

Source: `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusAdjunction.lean`,
proof of `derivedPlus_mateEquiv_app_fac`, old lines 439–482
(blueprint: lem-trf-derived-mate-counit-reduction).

Proof: (1) Expand the mate by `mateEquiv_apply` (def-weil-pbc-adjunction-mate), then use
naturality of the primed derived unit at
`t = G.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnit.app P)` preceded by the
inverse localization comparison. The composite becomes the primed derived functor applied
to `E'(t)`, the square, the image of the unprimed derived counit, and the comparison for `H`,
preceded by the primed unit at `q K(G) K(R) P`.
(2) Naturality of the square at the comparison `alpha_P` moves `E'(T(alpha_P))` through the
square; this uses no inverse of `alpha_P`.
(3) Replace `E(alpha_P)` followed by the unprimed derived counit using
`derivedPlus_counit_app_fac` (lem-trf-bounded-below-derived-adjunction).
(4) Naturality of the localization comparison for `H`
(lem-weil-pbc-exact-functor-derived-factorization), followed by `hθ`, changes the inside
composite to the localization of `sigma` followed by `K(H)` of the homotopy counit, preceded
by the localization comparison for `L'`. Only the comparison for `G` cancels with its inverse.
(5) Functoriality of the primed right-derived functor gives the displayed equality. -/
theorem derivedPlus_mateEquiv_counit_reduction
    {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
    [EnoughInjectives A] [EnoughInjectives A']
    {L : B ⥤ A} {R : A ⥤ B} {L' : B' ⥤ A'} {R' : A' ⥤ B'}
    {G : B ⥤ B'} {H : A ⥤ A'}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' H)
    (θ : TwoSquare G.mapDerivedCategoryPlus L.mapDerivedCategoryPlus L'.mapDerivedCategoryPlus
      H.mapDerivedCategoryPlus)
    (hθ : ∀ N : HomotopyCategory.Plus B,
      θ.natTrans.app (DerivedCategory.Plus.Qh.obj N) ≫
          H.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
          H.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj N) =
        L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) ≫
          DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.natTrans).app N))
    (P : HomotopyCategory.Plus A) :
    G.mapDerivedCategoryPlusFactorsh.inv.app (R.mapHomotopyCategoryPlus.obj P) ≫
        G.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnit.app P) ≫
        (mateEquiv adj.derivedPlus adj'.derivedPlus θ).natTrans.app
          (DerivedCategory.Plus.Qh.obj P) ≫
        R'.rightDerivedFunctorPlus.map (H.mapDerivedCategoryPlusFactorsh.hom.app P) =
      adj'.derivedPlus.unit.app
          (DerivedCategory.Plus.Qh.obj
            (G.mapHomotopyCategoryPlus.obj (R.mapHomotopyCategoryPlus.obj P))) ≫
        R'.rightDerivedFunctorPlus.map
          (L'.mapDerivedCategoryPlusFactorsh.hom.app
            (G.mapHomotopyCategoryPlus.obj (R.mapHomotopyCategoryPlus.obj P))) ≫
        R'.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus σ.natTrans).app
                (R.mapHomotopyCategoryPlus.obj P) ≫
              H.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.counit.app P))) := by
  have hmate :
      (mateEquiv adj.derivedPlus adj'.derivedPlus θ).natTrans.app
          (DerivedCategory.Plus.Qh.obj P) =
        adj'.derivedPlus.unit.app
            (G.mapDerivedCategoryPlus.obj
              (R.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj P))) ≫
          R'.rightDerivedFunctorPlus.map
            (θ.natTrans.app (R.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj P))) ≫
          R'.rightDerivedFunctorPlus.map
            (H.mapDerivedCategoryPlus.map
              (adj.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj P))) := by
    simp [mateEquiv_apply]
  set N := R.mapHomotopyCategoryPlus.obj P
  set u := R.rightDerivedFunctorPlusUnit.app P
  have h₁ := adj'.derivedPlus.unit.naturality (G.mapDerivedCategoryPlus.map u)
  have h₂ := θ.natTrans.naturality u
  have h₃ := adj.derivedPlus_counit_app_fac P
  have h₇ := adj'.derivedPlus.unit.naturality
    (G.mapDerivedCategoryPlusFactorsh.inv.app N)
  have h₈ := hθ N
  have h₉ := H.mapDerivedCategoryPlusFactorsh.hom.naturality
    (adj.mapHomotopyCategoryPlus.counit.app P)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    at h₁ h₂ h₇ h₉
  have key : θ.natTrans.app (DerivedCategory.Plus.Qh.obj N) ≫
      H.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app N ≫
        DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.counit.app P)) ≫
      H.mapDerivedCategoryPlusFactorsh.hom.app P =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus σ.natTrans).app N ≫
            H.mapHomotopyCategoryPlus.map (adj.mapHomotopyCategoryPlus.counit.app P)) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [h₉, reassoc_of% h₈]
  rw [hmate]
  simp only [Category.assoc]
  rw [reassoc_of% h₁]
  simp only [← Functor.map_comp]
  rw [reassoc_of% h₂, ← Functor.map_comp_assoc H.mapDerivedCategoryPlus, h₃, key]
  simp only [Functor.map_comp]
  rw [reassoc_of% h₇]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.id_comp]

end CategoryTheory.Adjunction
