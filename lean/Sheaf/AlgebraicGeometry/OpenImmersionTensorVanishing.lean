/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Tensor vanishing under open immersions

Source: Stacks Project, Tag 09U8.
(blueprint: lem-sc-open-immersion-tensor-vanishing).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wX wU wF

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Exact restriction along an open immersion preserves all-module tensor vanishing
in a fixed degree. Source: Stacks Project, Tag 09U8, open-immersion case.
(blueprint: lem-sc-open-immersion-tensor-vanishing).
Proof. For a module H on X, test the hypothesis on the ordinary direct image j_*H.
Choose the K-flat representative witnessing this vanishing. Exact restriction preserves
K-flatness and identifies its tensor with j_*H[0] with the restricted representative
with H[0], using the adjunction counit j^*j_*H = H. Restriction commutes with homology
and sends zero to zero, giving the required vanishing. Its factorization through Q
provides the representing isomorphism. Direct image is only used as a test object;
no exactness of direct image, boundedness, or quasi-coherence is used. Empty schemes
are included, and the degree i is arbitrary. -/
theorem openImmersion_tensor_vanishing {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    [HasDerivedCategory.{wU} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wF} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (R : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (eR : Nonempty (R ≅ Scheme.Modules.restrictFunctor j))
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (E : schemeDerivedCategory Y) (i : ℤ)
    (h : ∀ H : SheafOfModules.{u} (moduleRings Y.toRingedSpace),
      schemeDerivedTensorCohomologyVanishes Y E H i) :
    ∀ H : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      schemeDerivedTensorCohomologyVanishes X
        (R.mapDerivedCategory.obj E) H i := by
  classical
  obtain ⟨c⟩ := eR
  let RC := R.mapHomologicalComplex (.up ℤ)
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  have : PreservesColimitsOfSize.{0, 0}
      (Scheme.Modules.restrictFunctor j :
        SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings X.toRingedSpace)) := by
    infer_instance
  have : PreservesColimitsOfSize.{0, 0} R := by
    exact preservesColimits_of_natIso c.symm
  have total (P N : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
      Nonempty (RC.obj (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
        CochainComplex.mapBifunctor (RC.obj P) (RC.obj N) (curriedTensor _)) := by
    let K := (((curriedTensor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj P).obj N
    have : R.PreservesTotalComplex K (.up ℤ) := fun _ => inferInstance
    let e₁ := (HomologicalComplex₂.mapTotalIso R K (.up ℤ)).symm
    let : (Scheme.Modules.pullback j).Monoidal := Scheme.Modules.pullbackMonoidal j
    let : R.Monoidal := Functor.Monoidal.transport
      (c ≪≫ Scheme.Modules.restrictFunctorIsoPullback j).symm
    let e (F G : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
      (Functor.Monoidal.μIso R F G).symm
    have he (F F' G G' : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
        (f : F ⟶ F') (g : G ⟶ G') :
        R.map (f ⊗ₘ g) ≫ (e F' G').hom =
          (e F G).hom ≫ (R.map f ⊗ₘ R.map g) :=
      (Functor.OplaxMonoidal.δ_natural R f g).symm
    let e₂ :
        (((R.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj K) ≅
          (((curriedTensor (SheafOfModules.{u}
            (moduleRings X.toRingedSpace))).mapBifunctorHomologicalComplex
              (.up ℤ) (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj P)).obj
                ((R.mapHomologicalComplex (.up ℤ)).obj N) :=
      HomologicalComplex.Hom.isoOfComponents
        (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ e (P.X p) (N.X q))
          (by
            intro q q' hq
            change (e (P.X p) (N.X q)).hom ≫ R.obj (P.X p) ◁ R.map (N.d q q') =
              R.map (P.X p ◁ N.d q q') ≫ (e (P.X p) (N.X q')).hom
            simpa using (he (P.X p) (P.X p) (N.X q) (N.X q') (𝟙 _) (N.d q q')).symm))
        (by
          intro p p' hp
          apply HomologicalComplex.Hom.ext
          funext q
          change (e (P.X p) (N.X q)).hom ≫ R.map (P.d p p') ▷ R.obj (N.X q) =
            R.map (P.d p p' ▷ N.X q) ≫ (e (P.X p') (N.X q)).hom
          simpa using (he (P.X p) (P.X p') (N.X q) (N.X q) (P.d p p') (𝟙 _)).symm)
    exact ⟨e₁ ≪≫ HomologicalComplex₂.total.mapIso e₂ (.up ℤ)⟩
  intro G
  obtain ⟨P, hP, ⟨eP⟩, hz⟩ := h ((Scheme.Modules.pushforward j).obj G)
  have hRP : CochainComplex.IsKFlat (R := X.sheaf) (RC.obj P) := by
    have hk := isKFlat_restrict j P hP
    intro F hF n
    exact (hk F hF n).of_iso
      (((curriedTensor _).map₂CochainComplex.obj F).mapIso
        ((NatIso.mapHomologicalComplex c.symm (.up ℤ)).app P))
  refine ⟨RC.obj P, hRP, ?_, ?_⟩
  · exact ⟨(R.mapDerivedCategoryFactors.app P).symm ≪≫
      R.mapDerivedCategory.mapIso eP⟩
  · let N := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((Scheme.Modules.pushforward j).obj G)
    let L := CochainComplex.mapBifunctor P N (curriedTensor _)
    have hzR : IsZero ((RC.obj L).homology i) :=
      (R.map_isZero hz).of_iso ((L.sc i).mapHomologyIso R)
    obtain ⟨t⟩ := total P N
    let n : RC.obj N ≅ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G :=
      (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app _ ≪≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
          (c.app _ ≪≫ (Scheme.Modules.restrictFunctorAdjCounitIso j).app G)
    let B := ((curriedTensor (SheafOfModules.{u}
      (moduleRings X.toRingedSpace))).map₂CochainComplex).obj (RC.obj P)
    exact hzR.of_iso (HomologicalComplex.homologyMapIso (t ≪≫ B.mapIso n).symm i)


end AlgebraicGeometry
