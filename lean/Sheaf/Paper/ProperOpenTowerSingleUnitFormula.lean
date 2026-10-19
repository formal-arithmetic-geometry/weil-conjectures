/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Resolution formula for a proper/open tower unit path

Source: Stacks Project, Tags 0F7B, 0F7J and 0D6E
(blueprint: lem-sfb-proper-open-tower-single-unit-formula).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {A : Type (u + 1)} [CommRing A]
    {X U Xbar Y Ybar Z : Scheme.{u}}
    (j : X ⟶ U) (b : U ⟶ Xbar) (i : Y ⟶ Ybar)
    (q : U ⟶ Y) (p : Xbar ⟶ Ybar) (s : Ybar ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]

private theorem tower_unit_calc
    {A : Type (u + 1)} [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S)
    (K M : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [M.IsKInjective] (h : K ⟶ M) :
    ((t)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map (DerivedCategory.Q.map h) ≫
        (((t)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso M).hom =
      DerivedCategory.Q.map
        ((((t)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map h) := by
  have hn := ((t)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ _).map h)
  have h₁ (N : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
      (DerivedCategory.quotientCompQhIso _).inv.app N = 𝟙 _ := by rfl
  have h₂ (N : CochainComplex (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
      (DerivedCategory.quotientCompQhIso _).hom.app N = 𝟙 _ := by rfl
  dsimp only [Functor.rightDerivedFunctorObjQIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
    asIso_inv]
  erw [h₁, h₂]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [← cancel_mono (((t)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ _).obj M))]
  erw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact hn.symm


/-- The localized chain map equals its specified derived-unit expression.
Source: Stacks Project, more-etale.tex Tags 0F7B and 0F7J, and
sites-cohomology.tex Tag 0D6E (blueprint: lem-sfb-proper-open-tower-single-unit-formula).

Proof: Apply naturality of the total-right-derived unit for (p ≫ s)_* to the
composite augmentation from (j ≫ b)_!J to M. Its unit at M is invertible because M
is K-injective, so it cancels the final resolution identification. Expand the
augmentation. The inverse and forward open-extension composition maps cancel.
Naturality of the underived direct-image composition isomorphism moves the
augmentation across that isomorphism; its inverse at M cancels the forward
comparison. Functoriality of localization leaves exactly the second chain path.
-/
theorem properOpenTowerSingleUnitFormula
    (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (I : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (M : CochainComplex (Sheaf Xbar.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] [M.IsKInjective]
    (u : (((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
    (v : (((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I ⟶ M)
    [QuasiIso u] [QuasiIso v]
    (χ : ((q)_*[ModuleCat.{u + 1} A]) ⋙ ((i)_!open[ModuleCat.{u + 1} A]) ≅
      ((b)_!open[ModuleCat.{u + 1} A]) ⋙ ((p)_*[ModuleCat.{u + 1} A]))
    : let jc := ((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
      let bc := ((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
      let pc := ((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
      let sc := ((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
      let tc := ((p ≫ s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
      let e := NatIso.mapHomologicalComplex
        (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) j b) (.up ℤ)
      let d := NatIso.mapHomologicalComplex
        (lowerStarComp (ModuleCat.{u + 1} A) p s) (.up ℤ)
      DerivedCategory.Q.map (sc.map ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app
        (jc.obj J)) ≫ sc.map (pc.map (bc.map u ≫ v))) =
      DerivedCategory.Q.map (sc.map ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app
        (jc.obj J))) ≫
      DerivedCategory.Q.map (d.hom.app (bc.obj (jc.obj J))) ≫
      DerivedCategory.Q.map (tc.map (e.inv.app J)) ≫
      ((p ≫ s)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj
          ((((j ≫ b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj J)) ≫
      R((p ≫ s)_*[ModuleCat.{u + 1} A]).map
        (DerivedCategory.Q.map (e.hom.app J ≫ bc.map u ≫ v)) ≫
      (((p ≫ s)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso M).hom ≫
      DerivedCategory.Q.map (d.inv.app M) := by
  dsimp only
  let bc := ((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
  let tc := ((p ≫ s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
  let pc := ((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
  let sc := ((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
  let e := NatIso.mapHomologicalComplex
    (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) j b) (.up ℤ)
  let d := NatIso.mapHomologicalComplex (lowerStarComp (ModuleCat.{u + 1} A) p s)
    (.up ℤ)
  have hu := tower_unit_calc (p ≫ s) _ M (e.hom.app J ≫ bc.map u ≫ v)
  erw [reassoc_of% hu]
  simp only [← Functor.map_comp]
  congr 1
  have hd := d.hom.naturality (bc.map u ≫ v)
  change sc.map (pc.map _) ≫ d.hom.app M = d.hom.app _ ≫ tc.map _ at hd
  simp only [Functor.map_comp, Category.assoc]
  rw [← tc.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← tc.map_comp_assoc (bc.map u) v, ← reassoc_of% hd,
    Iso.hom_inv_id_app, Category.comp_id]
  simp only [Functor.map_comp]
  rfl

end AlgebraicGeometry.Etale
