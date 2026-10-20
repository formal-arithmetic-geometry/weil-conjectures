/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Sheaf.AlgebraicGeometry.DerivedModuleUnderlyingComparison

/-!
# Continuity for bounded-below étale complexes

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
lemma lem-weil-pbc-derived-cohomology-continuity
(blueprint: lem-weil-pbc-derived-cohomology-continuity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For a finite commutative coefficient ring, the canonical restriction cocone on
`(Over i₀)ᵒᵖ` is a colimit in every integer degree. The isomorphisms `e` and `eY`
only present its objects; `hm` and `hs` prescribe the canonical restriction maps
via the derived adjunction unit, Leray, and inverse-image composition.
Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
lemma lem-weil-pbc-derived-cohomology-continuity
(blueprint: lem-weil-pbc-derived-cohomology-continuity).

Proof: Restrict the inverse system along the initial functor `Over.forget i₀`.
Its limit is still the given cone point, and the restriction inherits quasi-compactness,
quasi-separatedness and affine transition maps. Forget coefficients to abelian groups.
The exact underlying-sheaf functor sends the bounded-below complex to a bounded-below
abelian complex. The constructed cohomology and pullback comparisons identify every
stage and the cone point. Their naturality identifies all three factors of each
prescribed restriction map, so `derivedEtaleCohomology_limit` applies to the resulting
abelian-group cocone. Finally the module-to-abelian-group functor reflects colimits,
giving the stated module colimit. No additional geometric finiteness statement or
truncation induction is needed here; those belong to the additive continuity theorem.
-/
theorem derived_cohomology_continuity
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i₀ : I)
    (K : DerivedCategory.Plus (Sheaf (D.obj i₀).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (F : (Over i₀)ᵒᵖ ⥤ (ModuleCat.{u + 1} Λ))
    (e : ∀ i : Over i₀, F.obj (op i) ≅
      (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj i.left) n).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map i.hom)).mapDerivedCategory.obj K.obj))
    (hm : ∀ {i j : Over i₀} (f : i ⟶ j), F.map f.op =
      (e j).hom ≫
      (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj j.left) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (D.map f.left)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map j.hom)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) (D.map f.left)).hom.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map f.left)).mapDerivedCategory.obj
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map j.hom)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj i.left) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map f.left) (D.map j.hom)
            (D.map i.hom) ((congrArg D.map f.w).symm.trans (D.map_comp f.left j.hom))) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map j.hom))
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map f.left))).inv.app K.obj) ≫
      (e i).inv)
    (s : Cocone F)
    (eY : s.pt ≅ (Etale.cohomology (ModuleCat.{u + 1} Λ) c.pt n).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app i₀)).mapDerivedCategory.obj K.obj))
    (hs : ∀ i : Over i₀, s.ι.app (op i) =
      (e i).hom ≫
      (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj i.left) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (c.π.app i.left)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map i.hom)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) (c.π.app i.left)).hom.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app i.left)).mapDerivedCategory.obj
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map i.hom)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology (ModuleCat.{u + 1} Λ) c.pt n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app i.left) (D.map i.hom) (c.π.app i₀)
            (c.w i.hom).symm) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map i.hom))
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app i.left))).inv.app K.obj) ≫
      eY.inv) : Nonempty (IsColimit s) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let KA := (Etale.moduleUnderlyingSheaf Λ (D.obj i₀)).mapDerivedCategoryPlus.obj K
  let a := Etale.moduleUnderlyingPullbackIso Λ (D.obj i₀) K n
  have ha := Etale.moduleUnderlyingPullbackIso_naturality Λ (D.obj i₀) K n
  let E : Over i₀ ⥤ Scheme.{u} := Over.forget i₀ ⋙ D
  let d : Cone E := c.whisker (Over.forget i₀)
  have hd : IsLimit d := (Functor.Initial.isLimitWhiskerEquiv _ c).symm hc
  let : ∀ i : Over i₀, CompactSpace (E.obj i) :=
    fun i ↦ inferInstanceAs (CompactSpace (D.obj i.left))
  let : ∀ i : Over i₀, QuasiSeparatedSpace (E.obj i) :=
    fun i ↦ inferInstanceAs (QuasiSeparatedSpace (D.obj i.left))
  let : ∀ {i j : Over i₀} (f : i ⟶ j), IsAffineHom (E.map f) :=
    fun f ↦ inferInstanceAs (IsAffineHom (D.map f.left))
  let t : E ⟶ (Functor.const (Over i₀)).obj (D.obj i₀) :=
    { app := fun i ↦ D.map i.hom
      naturality := fun i j f ↦ by
        dsimp [E]
        simpa only [Category.comp_id, ← D.map_comp] using congrArg D.map f.w }
  let aF : ∀ i : Over i₀, (F ⋙ U).obj (op i) ≅
      (Etale.cohomology AddCommGrpCat.{u + 1} (E.obj i) n).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (t.app i)).mapDerivedCategory.obj KA.obj) :=
    fun i ↦ U.mapIso (e i) ≪≫ a _ (D.map i.hom)
  let aY := U.mapIso eY ≪≫ a _ (c.π.app i₀)
  have hmA : ∀ {i j : Over i₀} (f : i ⟶ j), (F ⋙ U).map f.op =
      (aF j).hom ≫ Etale.presentationDerivedMap (E.map f) (t.app j) (t.app i)
        ((Category.comp_id _).symm.trans (t.naturality f).symm) KA.obj n ≫
      (aF i).inv := by
    intro i j f
    let w := (congrArg D.map f.w).symm.trans (D.map_comp f.left j.hom)
    have hmap : F.map f.op = (e j).hom ≫
        Etale.moduleDerivedRestriction Λ (D.map f.left) (D.map j.hom) (D.map i.hom)
          w K.obj n ≫ (e i).inv := hm f
    have hcomp := ha (D.obj i.left) (D.obj j.left) (D.map f.left)
      (D.map j.hom) (D.map i.hom) w
    have hr := (Iso.eq_comp_inv (a _ (D.map i.hom))).mpr hcomp
    change U.map (F.map f.op) = _
    rw [hmap, Functor.map_comp, Functor.map_comp, hr]
    simp only [aF, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Category.assoc]
    rfl
  have hsA : ∀ i : Over i₀, (U.mapCocone s).ι.app (op i) =
      (aF i).hom ≫ Etale.presentationDerivedMap (d.π.app i) (t.app i) (c.π.app i₀)
        (c.w i.hom).symm KA.obj n ≫ aY.inv := by
    intro i
    have hmap : s.ι.app (op i) = (e i).hom ≫
        Etale.moduleDerivedRestriction Λ (c.π.app i.left) (D.map i.hom) (c.π.app i₀)
          (c.w i.hom).symm K.obj n ≫ eY.inv := hs i
    have hcomp := ha c.pt (D.obj i.left) (c.π.app i.left)
      (D.map i.hom) (c.π.app i₀) (c.w i.hom).symm
    have hr := (Iso.eq_comp_inv (a _ (c.π.app i₀))).mpr hcomp
    change U.map (s.ι.app (op i)) = _
    rw [hmap, Functor.map_comp, Functor.map_comp, hr]
    simp only [aF, aY, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Category.assoc]
    rfl
  obtain ⟨h⟩ := derivedEtaleCohomology_limit (D.obj i₀) E d hd t (c.π.app i₀)
    (fun i ↦ c.w i.hom) KA n (F ⋙ U) aF hmA (U.mapCocone s) aY hsA
  exact ⟨isColimitOfReflects U h⟩

end AlgebraicGeometry
