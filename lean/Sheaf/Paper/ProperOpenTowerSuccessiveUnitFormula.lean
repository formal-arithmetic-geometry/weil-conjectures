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
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

/-! # Resolution formula for a proper/open tower unit path

Source: Stacks Project, Tags 0F7B, 0F7J and 0D6E
(blueprint: lem-sfb-proper-open-tower-successive-unit-formula).
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

private noncomputable def towerUnit {T S : Scheme.{u}} (t : T ⟶ S)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.Q.obj
      ((((t)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj K) ⟶
    R((t)_*[ModuleCat.{u + 1} A]).obj (DerivedCategory.Q.obj K) :=
  ((t)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ _).obj K)

private theorem tower_unit_calc
    {A : Type (u + 1)} [CommRing A]
    {T S : Scheme.{u}} (t : T ⟶ S)
    (K M : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [M.IsKInjective] (h : K ⟶ M) :
    towerUnit (A := A) t K ≫
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
  dsimp only [towerUnit, Functor.rightDerivedFunctorObjQIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
    asIso_inv]
  erw [h₁, h₂]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [← cancel_mono (((t)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ _).obj M))]
  erw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact hn.symm


private theorem comp_eq :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom =
      (Functor.rightDerivedFunctorCompIso' ((p)_*[ModuleCat.{u + 1} A])
        ((s)_*[ModuleCat.{u + 1} A]) (lowerStarComp (ModuleCat.{u + 1} A) p s)).hom := by
  have he : (lowerStarComp (ModuleCat.{u + 1} A) p s).hom =
      conjugateEquiv ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p))
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (p ≫ s))
        (upperStarComp (ModuleCat.{u + 1} A) p s).hom := by
    exact (congrArg Iso.hom (conjugateIsoEquiv_upperStarComp
      (ModuleCat.{u + 1} A) p s)).symm
  have hc := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (p ≫ s))
    (lowerStarComp (ModuleCat.{u + 1} A) p s)
    (upperStarComp (ModuleCat.{u + 1} A) p s) he
  rw [hc]
  simp only [rightDerivedLowerStarComp, conjugateIsoEquiv_iso_symm]
  rfl

private theorem tower_comp_unit
    (K : CochainComplex (Sheaf Xbar.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    towerUnit (A := A) s
        ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj K) ≫
      R((s)_*[ModuleCat.{u + 1} A]).map (towerUnit (A := A) p K) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom.app
        (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (lowerStarComp (ModuleCat.{u + 1} A) p s).hom (.up ℤ)).app K) ≫
      towerUnit (A := A) (p ≫ s) K := by
  rw [comp_eq]
  let F := ((p)_*[ModuleCat.{u + 1} A])
  let G := ((s)_*[ModuleCat.{u + 1} A])
  let e := lowerStarComp (ModuleCat.{u + 1} A) p s
  let H := (HomotopyCategory.quotient _ _).obj K
  have hc : (Functor.rightDerivedFunctorCompUnit F G).app H ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj H) =
      (F ⋙ G).rightDerivedFunctorUnit.app H ≫
        (Functor.rightDerivedFunctorNatTrans e.hom).app (DerivedCategory.Qh.obj H) := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso]
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app H =
      𝟙 _ := by
    rw [← cancel_epi
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app H),
      Iso.hom_inv_id_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp] at hc
  rw [hi] at hc
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at hc
  dsimp only [towerUnit]
  erw [← Category.assoc, hc]
  dsimp only [Functor.rightDerivedFunctorNatTrans]
  erw [Functor.rightDerivedNatTrans_app]
  rfl


private theorem tower_obj_cancel {T S : Scheme.{u}} (t : T ⟶ S)
    (M : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [M.IsKInjective] :
    towerUnit (A := A) t M ≫
      (((t)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso M).hom = 𝟙 _ := by
  have h := tower_unit_calc t M M (𝟙 M)
  erw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id] at h
  exact h

private theorem tower_comp_obj
    (M : CochainComplex (Sheaf Xbar.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [M.IsKInjective] :
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom.app
        (DerivedCategory.Q.obj M) ≫
      (((p ≫ s)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso M).hom ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (lowerStarComp (ModuleCat.{u + 1} A) p s).inv (.up ℤ)).app M) =
    R((s)_*[ModuleCat.{u + 1} A]).map
      ((((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso M).hom) ≫
      (((s)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso
        ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj M)).hom := by
  have hp := tower_obj_cancel p M
  have hs := tower_obj_cancel s
    ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj M)
  have ht := tower_obj_cancel (p ≫ s) M
  have hc := tower_comp_unit p s M
  have hi : IsIso (towerUnit (A := A) s
      ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj M)) := by
    dsimp only [towerUnit]
    infer_instance
  have hi' : IsIso (towerUnit (A := A) p M) := by
    dsimp only [towerUnit]
    infer_instance
  apply (cancel_epi (towerUnit (A := A) s
    ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj M) ≫
    R((s)_*[ModuleCat.{u + 1} A]).map (towerUnit (A := A) p M))).1
  simp only [Category.assoc]
  erw [reassoc_of% hc]
  rw [reassoc_of% ht]
  rw [← DerivedCategory.Q.map_comp]
  have he := (NatIso.mapHomologicalComplex
    (lowerStarComp (ModuleCat.{u + 1} A) p s) (.up ℤ)).hom_inv_id_app M
  erw [he, DerivedCategory.Q.map_id]
  erw [← CategoryTheory.Functor.map_comp_assoc, hp,
    CategoryTheory.Functor.map_id, Category.id_comp, hs]
  rfl

/-- The localized chain map equals its specified derived-unit expression.
Source: Stacks Project, more-etale.tex Tags 0F7B and 0F7J, and
sites-cohomology.tex Tag 0D6E (blueprint: lem-sfb-proper-open-tower-successive-unit-formula).

Proof: Naturality of the localization unit says that its composite with the derived
image of a resolution and the inverse unit at its K-injective target equals the
localized direct image of that resolution. Apply this first to q and u, and then
to s and w. Insert hrep at I and v. Naturality of Γ moves Q(u) across Γ; the exact
extension-by-zero localization comparisons move Q(u) across Db_!. The equation
hlift identifies Q(w) followed by Q(ell) with Q(χ_I) followed by Q(p_*v).
Finally the canonical direct-image composition comparison is normalized by the
composite derived unit (Stacks 0D6E). Its component at the K-injective M cancels
the two inverse units, leaving precisely the displayed localized chain map.
No direct-image functor is assumed to preserve quasi-isomorphisms.
-/
theorem properOpenTowerSuccessiveUnitFormula
    (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (I : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (M : CochainComplex (Sheaf Xbar.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] [M.IsKInjective]
    (u : (((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
    (v : (((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I ⟶ M)
    [QuasiIso u] [QuasiIso v]
    (χ : ((q)_*[ModuleCat.{u + 1} A]) ⋙ ((i)_!open[ModuleCat.{u + 1} A]) ≅
      ((b)_!open[ModuleCat.{u + 1} A]) ⋙ ((p)_*[ModuleCat.{u + 1} A]))
    (L : CochainComplex (Sheaf Ybar.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [L.IsKInjective]
    (w : (((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj
      ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj I) ⟶ L)
    [QuasiIso w]
    (ell : L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj M)
    (Γ : R(((q)_*[ModuleCat.{u + 1} A])) ⋙ D(((i)_!open[ModuleCat.{u + 1} A])) ≅
      D(((b)_!open[ModuleCat.{u + 1} A])) ⋙ R(((p)_*[ModuleCat.{u + 1} A])))
    (hlift : Nonempty (Homotopy (w ≫ ell)
      ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app I ≫
        (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map v)))
    (hrep : D(((i)_!open[ModuleCat.{u + 1} A])).map ((((q)_*[ModuleCat.{u + 1}
            A]).rightDerivedFunctorObjQIso (I)).hom) ≫
          ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app ((((q)_*[ModuleCat.{u
              + 1} A]).mapHomologicalComplex (.up ℤ)).obj (I)) ≫ DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app (I)) ≫ DerivedCategory.Q.map
              ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (v)) =
        Γ.hom.app (DerivedCategory.Q.obj (I)) ≫
          R(((p)_*[ModuleCat.{u + 1} A])).map (((b)_!open[ModuleCat.{u + 1}
              A]).mapDerivedCategoryFactors.hom.app (I) ≫ DerivedCategory.Q.map (v)) ≫
              (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso (M)).hom)
    : DerivedCategory.Q.map ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex
      (.up ℤ)).map ((((i)_!open[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).map ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex
      (.up ℤ)).map (u))) ≫ (((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
      (w) ≫ (((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (ell)) =
  ((s)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ _).obj ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex
      (.up ℤ)).obj ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj
      ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj J)))) ≫
    R(((s)_*[ModuleCat.{u + 1} A])).map (((i)_!open[ModuleCat.{u + 1}
        A]).mapDerivedCategoryFactors.inv.app ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex
        (.up ℤ)).obj ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (J))) ≫
      D(((i)_!open[ModuleCat.{u + 1} A])).map
        (((q)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj
            ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj J))) ≫
      Γ.hom.app (DerivedCategory.Q.obj ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex
          (.up ℤ)).obj (J)))) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom.app
      (D(((b)_!open[ModuleCat.{u + 1} A])).obj (DerivedCategory.Q.obj ((((j)_!open[ModuleCat.{u +
          1} A]).mapHomologicalComplex (.up ℤ)).obj (J)))) ≫
    R(((p ≫ s)_*[ModuleCat.{u + 1} A])).map (((b)_!open[ModuleCat.{u + 1}
        A]).mapDerivedCategoryFactors.hom.app ((((j)_!open[ModuleCat.{u + 1}
        A]).mapHomologicalComplex (.up ℤ)).obj (J)) ≫ DerivedCategory.Q.map
          (((((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (u) ≫ v))) ≫
    (((p ≫ s)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso (M)).hom ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lowerStarComp (ModuleCat.{u + 1} A) p
        s).inv (.up ℤ)).app M) := by
  let Fq := ((q)_*[ModuleCat.{u + 1} A])
  let Fi := ((i)_!open[ModuleCat.{u + 1} A])
  let Fb := ((b)_!open[ModuleCat.{u + 1} A])
  let Fp := ((p)_*[ModuleCat.{u + 1} A])
  let Fs := ((s)_*[ModuleCat.{u + 1} A])
  let Ft := ((p ≫ s)_*[ModuleCat.{u + 1} A])
  let qc := Fq.mapHomologicalComplex (.up ℤ)
  let ic := Fi.mapHomologicalComplex (.up ℤ)
  let bc := Fb.mapHomologicalComplex (.up ℤ)
  let pc := Fp.mapHomologicalComplex (.up ℤ)
  let sc := Fs.mapHomologicalComplex (.up ℤ)
  let K := (((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj J
  let a := Fb.mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map (bc.map u ≫ v)
  let z := Fi.mapDerivedCategoryFactors.inv.app (qc.obj K) ≫
    Fi.mapDerivedCategory.map (towerUnit (A := A) q K) ≫
      Γ.hom.app (DerivedCategory.Q.obj K)
  let c := ic.map (qc.map u) ≫
    (NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app I ≫ pc.map v
  have ha : a = Fb.mapDerivedCategory.map (DerivedCategory.Q.map u) ≫
      (Fb.mapDerivedCategoryFactors.hom.app I ≫ DerivedCategory.Q.map v) := by
    dsimp only [a]
    rw [DerivedCategory.Q.map_comp, ← Category.assoc]
    erw [← Fb.mapDerivedCategoryFactors.hom.naturality u]
    rw [Category.assoc]
    rfl
  have hinner : z ≫ Fp.rightDerivedFunctor.map a ≫
      (Fp.rightDerivedFunctorObjQIso M).hom = DerivedCategory.Q.map c := by
    dsimp only [z]
    rw [ha, Fp.rightDerivedFunctor.map_comp]
    simp only [Category.assoc]
    erw [← reassoc_of% (Γ.hom.naturality (DerivedCategory.Q.map u))]
    erw [← hrep]
    rw [← Fi.mapDerivedCategory.map_comp_assoc, ← Fi.mapDerivedCategory.map_comp_assoc]
    erw [Category.assoc, tower_unit_calc q K I u]
    erw [← reassoc_of% (Fi.mapDerivedCategoryFactors.inv.naturality (qc.map u)),
      Iso.inv_hom_id_app_assoc]
    simp only [c, Functor.map_comp]
    rfl
  change DerivedCategory.Q.map (sc.map (ic.map (qc.map u)) ≫ sc.map w ≫ sc.map ell) =
    towerUnit (A := A) s (ic.obj (qc.obj K)) ≫ Fs.rightDerivedFunctor.map z ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom.app
        (Fb.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      Ft.rightDerivedFunctor.map a ≫ (Ft.rightDerivedFunctorObjQIso M).hom ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (lowerStarComp (ModuleCat.{u + 1} A) p s).inv (.up ℤ)).app M)
  have hn := (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom.naturality a
  erw [← reassoc_of% hn, tower_comp_obj p s M]
  rw [← Fs.rightDerivedFunctor.map_comp_assoc, ← Fs.rightDerivedFunctor.map_comp_assoc]
  erw [Category.assoc, hinner]
  erw [tower_unit_calc s _ (pc.obj M) c]
  have hh := DerivedCategory.Q_map_eq_of_homotopy _
    (Fs.mapHomotopy hlift.some)
  change DerivedCategory.Q.map (sc.map (w ≫ ell)) =
    DerivedCategory.Q.map (sc.map
      ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app I ≫ pc.map v)) at hh
  simp only [c, Functor.map_comp] at hh ⊢
  erw [hh]

end AlgebraicGeometry.Etale
