/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Canonical adjunction maps in the geometric open-cover triangle

## References

* Stacks Project, Tags 08BU, 08BT and 08BW
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

noncomputable section

namespace SheafOfModules


/-- The canonical comparison between nested derived restrictions. -/
def openRestrictionComparison {S : Type u} [TopologicalSpace S]
    (R : Sheaf (Opens.grothendieckTopology S) RingCat.{u})
    {W U : Opens S} (i : W ⟶ U)
    [(overFunctor.{u} R U).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R U)]
    [PreservesFiniteColimits (overFunctor.{u} R U)]
    [(overFunctor.{u} R W).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R W)]
    [PreservesFiniteColimits (overFunctor.{u} R W)]
    [(overMap.{u} R i).Additive]
    [PreservesFiniteLimits (overMap.{u} R i)]
    [PreservesFiniteColimits (overMap.{u} R i)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over W))]
    : (overFunctor.{u} R U).mapDerivedCategory ⋙
      (overMap.{u} R i).mapDerivedCategory ≅ (overFunctor.{u} R W).mapDerivedCategory :=
  let A := overFunctor.{u} R U
  let B := overMap.{u} R i
  letI : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits A B
  letI : PreservesFiniteColimits (A ⋙ B) := comp_preservesFiniteColimits A B
  Functor.mapDerivedCategoryCompIso A B ≪≫
    Functor.mapDerivedCategoryNatIso (overFunctorMap.{u} R i)

private theorem openExtension_exact (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) (U : Opens X) :
    let S := extensionByZeroPresheaf.{u} R U ⋙
      PresheafOfModules.sheafification.{u} (𝟙 R.obj)
    PreservesFiniteLimits S ∧ PreservesFiniteColimits S ∧
      Nonempty (S ⊣ overFunctor.{u} R U) := by
  subst R
  have hJ : (Opens.grothendieckTopology X).toPrecoverage.toGrothendieck =
      Opens.grothendieckTopology X := by
    apply le_antisymm
    · exact GrothendieckTopology.toGrothendieck_toPrecoverage_le _
    · intro V S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
  let P (J : GrothendieckTopology (Opens X)) (O : Sheaf J CommRingCat.{u}) :=
    let R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O
    let S := extensionByZeroPresheaf.{u} R U ⋙
      PresheafOfModules.sheafification.{u} (𝟙 R.obj)
    PreservesFiniteLimits S ∧ PreservesFiniteColimits S ∧
      Nonempty (S ⊣ overFunctor.{u} R U)
  change P (Opens.grothendieckTopology X) X.sheaf
  have h : ∀ O, P (Opens.grothendieckTopology X) O := by
    rw [← hJ]
    intro O
    exact (localizedModule_adjunction_exact
      (Opens.grothendieckTopology X).toPrecoverage O U).2.2
  exact h X.sheaf

/-- The geometric Mayer–Vietoris triangle with its arrows defined as adjunction mates.
No Hom identifications or shifted Hom groups are part of this statement.
-/
theorem open_cover_adjunction_triangle (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R U)]
    [PreservesFiniteColimits (overFunctor.{u} R U)]
    [(overFunctor.{u} R V).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R V)]
    [PreservesFiniteColimits (overFunctor.{u} R V)]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R (U ⊓ V))]
    [PreservesFiniteColimits (overFunctor.{u} R (U ⊓ V))]
    [(overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).Additive]
    [PreservesFiniteLimits (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U))]
    [PreservesFiniteColimits (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U))]
    [(overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).Additive]
    [PreservesFiniteLimits (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V))]
    [PreservesFiniteColimits (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over (U ⊓ V)))]
    (E : DerivedCategory (SheafOfModules.{u} R))
    (LU : DerivedCategory (SheafOfModules.{u} (R.over U)) ⥤
      DerivedCategory (SheafOfModules.{u} R))
    (LV : DerivedCategory (SheafOfModules.{u} (R.over V)) ⥤
      DerivedCategory (SheafOfModules.{u} R))
    (LW : DerivedCategory (SheafOfModules.{u} (R.over (U ⊓ V))) ⥤
      DerivedCategory (SheafOfModules.{u} R))
    (adjU : LU ⊣ (overFunctor.{u} R U).mapDerivedCategory)
    (adjV : LV ⊣ (overFunctor.{u} R V).mapDerivedCategory)
    (adjW : LW ⊣ (overFunctor.{u} R (U ⊓ V)).mapDerivedCategory) :
    let RU := (overFunctor.{u} R U).mapDerivedCategory
    let RV := (overFunctor.{u} R V).mapDerivedCategory
    let RW := (overFunctor.{u} R (U ⊓ V)).mapDerivedCategory
    let TU := (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory
    let TV := (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory
    let cU := openRestrictionComparison R (homOfLE inf_le_left : U ⊓ V ⟶ U)
    let cV := openRestrictionComparison R (homOfLE inf_le_right : U ⊓ V ⟶ V)
    let κU := (adjW.homEquiv (RW.obj E) (LU.obj (RU.obj E))).symm
      (cU.inv.app E ≫ TU.map (adjU.unit.app (RU.obj E)) ≫ cU.hom.app (LU.obj (RU.obj E)))
    let κV := (adjW.homEquiv (RW.obj E) (LV.obj (RV.obj E))).symm
      (cV.inv.app E ≫ TV.map (adjV.unit.app (RV.obj E)) ≫ cV.hom.app (LV.obj (RV.obj E)))
    ∃ δ : E ⟶ (LW.obj (RW.obj E))⟦(1 : ℤ)⟧,
      Triangle.mk (biprod.lift κU (-κV))
        (biprod.desc (adjU.counit.app E) (adjV.counit.app E)) δ ∈ distTriang _ := by
  classical
  dsimp only
  let S (O : Opens X) := extensionByZeroPresheaf.{u} R O ⋙
    PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  let aU : S U ⊣ overFunctor.{u} R U :=
    Classical.choice (openExtension_exact X R hR U).2.2
  let aV : S V ⊣ overFunctor.{u} R V :=
    Classical.choice (openExtension_exact X R hR V).2.2
  let aW : S (U ⊓ V) ⊣ overFunctor.{u} R (U ⊓ V) :=
    Classical.choice (openExtension_exact X R hR (U ⊓ V)).2.2
  have : (S U).Additive := aU.left_adjoint_additive
  have : (S V).Additive := aV.left_adjoint_additive
  have : (S (U ⊓ V)).Additive := aW.left_adjoint_additive
  have : PreservesFiniteLimits (S U) := (openExtension_exact X R hR U).1
  have : PreservesFiniteColimits (S U) := (openExtension_exact X R hR U).2.1
  have : PreservesFiniteLimits (S V) := (openExtension_exact X R hR V).1
  have : PreservesFiniteColimits (S V) := (openExtension_exact X R hR V).2.1
  have : PreservesFiniteLimits (S (U ⊓ V)) := (openExtension_exact X R hR (U ⊓ V)).1
  have : PreservesFiniteColimits (S (U ⊓ V)) := (openExtension_exact X R hR (U ⊓ V)).2.1
  let K : CochainComplex (SheafOfModules.{u} R) ℤ := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hs := open_cover_mate_complex_shortExact
    X R hR U V hcover (S U) (S V) (S (U ⊓ V)) aU aV aW K
  dsimp only at hs
  rcases hs with ⟨f, hfU, hfV, hz, hses⟩
  let pU := aU.derivedPresentation adjU K e
  let pV := aV.derivedPresentation adjV K e
  let pW := aW.derivedPresentation adjW K e
  have hpU := aU.derivedPresentation_counit adjU K e
  have hpV := aV.derivedPresentation_counit adjV K e
  have hmU := Adjunction.derivedPresentation_mate aU aW
    (overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)) adjU adjW K e
    (f ≫ biprod.fst) hfU
  have hmV := Adjunction.derivedPresentation_mate aV aW
    (overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)) adjV adjW K e
    (-(f ≫ biprod.snd)) hfV
  have (A B : CochainComplex (SheafOfModules.{u} R) ℤ) :
      PreservesBinaryBiproduct A B DerivedCategory.Q :=
    preservesBinaryBiproduct_of_preservesBiproduct DerivedCategory.Q A B
  let pB := DerivedCategory.Q.mapBiprod _ _ ≪≫
    biprod.mapIso pU.symm pV.symm
  let δ := e.inv ≫ DerivedCategory.triangleOfSESδ hses ≫ pW.inv⟦(1 : ℤ)⟧'
  refine ⟨δ, ?_⟩
  apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hses) _
  refine Triangle.isoMk _ _ pW pB.symm e.symm ?_ ?_ ?_
  · dsimp only [DerivedCategory.triangleOfSES, Triangle.mk]
    change biprod.lift _ _ ≫ pB.inv = pW.hom ≫ DerivedCategory.Q.map f
    apply (cancel_mono pB.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext
    · dsimp only at hmU
      simpa [pB, Functor.mapBiprod_hom, Category.assoc, Functor.map_comp,
        openRestrictionComparison] using congrArg (fun z => z ≫ pU.inv) hmU.symm
    · dsimp only at hmV
      simpa [pB, Functor.mapBiprod_hom, Category.assoc, Functor.map_comp,
        openRestrictionComparison] using congrArg (fun z => -(z ≫ pV.inv)) hmV.symm
  · dsimp only [DerivedCategory.triangleOfSES, Triangle.mk]
    change biprod.desc _ _ ≫ e.inv = pB.inv ≫ DerivedCategory.Q.map _
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [pB, Iso.trans_inv, biprod.mapIso_inv, Iso.symm_inv, Category.assoc]
    apply biprod.hom_ext'
    · simpa [Functor.mapBiprod_inv, Category.assoc, ← Functor.map_comp_assoc] using hpU.symm
    · simpa [Functor.mapBiprod_inv, Category.assoc, ← Functor.map_comp_assoc] using hpV.symm
  · dsimp only [DerivedCategory.triangleOfSES, Triangle.mk_mor₃, δ]
    simp

end SheafOfModules
