/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module
public import Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCanonical

/-! # The reverse cycle-class comparison and the derived unit -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

private theorem affineReverseUnit_quotient_map_Qh {E : Type*} [Category* E] [Abelian E]
    [HasDerivedCategory E] {M N : CochainComplex E ℤ} (f : M ⟶ N) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) =
      DerivedCategory.Q.map f := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality f
  have hi : ∀ M, (DerivedCategory.quotientCompQhIso E).hom.app M = 𝟙 _ := fun _ ↦ rfl
  rw [hi, hi] at h
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

private theorem affineReverseUnit_unit_comp
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (P : C ⥤ D) [P.Additive] (I : CochainComplex C ℤ) [I.IsKInjective] :
    P.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) ≫
      (P.rightDerivedFunctorObjQIso I).hom = 𝟙 _ := by
  have h₁ : ∀ K, (DerivedCategory.quotientCompQhIso C).inv.app K = 𝟙 _ := fun _ ↦ rfl
  have h₂ : ∀ K, (DerivedCategory.quotientCompQhIso D).hom.app K = 𝟙 _ := fun _ ↦ rfl
  dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_inv, Iso.app]
  erw [h₁, h₂, P.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  exact IsIso.hom_inv_id _

private theorem affineReverseUnit_map_unit_comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    (P : C ⥤ D) [P.Additive] (I : CochainComplex C ℤ) [I.IsKInjective]
    (H : DerivedCategory D ⥤ E) {X : E}
    (t : H.obj (DerivedCategory.Q.obj ((P.mapHomologicalComplex (.up ℤ)).obj I)) ⟶ X) :
    H.map (P.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) ≫
      H.map (P.rightDerivedFunctorObjQIso I).hom ≫ t = t := by
  rw [← H.map_comp_assoc, affineReverseUnit_unit_comp, H.map_id, Category.id_comp]

private theorem affineReverseUnit_unit_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (P : C ⥤ D) [P.Additive] {K L : CochainComplex C ℤ} (s : K ⟶ L) :
    DerivedCategory.Q.map ((P.mapHomologicalComplex (.up ℤ)).map s) ≫
      P.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj L) =
      P.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
        P.rightDerivedFunctor.map (DerivedCategory.Q.map s) := by
  have hu := P.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ _).map s)
  dsimp only [Functor.comp_map] at hu
  erw [Functor.mapHomotopyCategory_map] at hu
  erw [affineReverseUnit_quotient_map_Qh s] at hu
  erw [affineReverseUnit_quotient_map_Qh
    ((P.mapHomologicalComplex (.up ℤ)).map s)] at hu
  exact hu

private theorem affineReverseUnit_comparison_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P]
    (i : ℤ) {K L : CochainComplex C ℤ} (s : K ⟶ L) :
    (DerivedCategory.homologyFunctor D i).map
      (DerivedCategory.Q.map ((P.mapHomologicalComplex (.up ℤ)).map s)) ≫
      ((DerivedCategory.homologyFunctorFactors _ i).app
        ((P.mapHomologicalComplex (.up ℤ)).obj L)).hom ≫
      (L.sc i).leftExactHomologyComparison P ≫
      P.map (((DerivedCategory.homologyFunctorFactors _ i).app L).inv) =
      ((DerivedCategory.homologyFunctorFactors _ i).app
        ((P.mapHomologicalComplex (.up ℤ)).obj K)).hom ≫
      (K.sc i).leftExactHomologyComparison P ≫
      P.map (((DerivedCategory.homologyFunctorFactors _ i).app K).inv) ≫
      P.map ((DerivedCategory.homologyFunctor C i).map (DerivedCategory.Q.map s)) := by
  have hn := ShortComplex.leftExactHomologyComparison_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map s) P
  simp only [Iso.app_hom, Iso.app_inv]
  erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
  change HomologicalComplex.homologyMap
      ((P.mapHomologicalComplex (.up ℤ)).map s) i ≫
      (L.sc i).leftExactHomologyComparison P =
    (K.sc i).leftExactHomologyComparison P ≫
      P.map (HomologicalComplex.homologyMap s i) at hn
  rw [← Category.assoc _ ((L.sc i).leftExactHomologyComparison P), hn]
  simp only [Category.assoc, ← P.map_comp]
  congr 2
  apply congrArg P.map
  exact (DerivedCategory.homologyFunctorFactors _ i).inv.naturality s

private theorem affineReverseUnit_map_square
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {X₁ X₂ Y₁ Y₂ : C} {a : X₁ ⟶ X₂} {v : X₂ ⟶ Y₂}
    {u : X₁ ⟶ Y₁} {b : Y₁ ⟶ Y₂} (h : a ≫ v = u ≫ b) :
    H.map a ≫ H.map v = H.map u ≫ H.map b := by
  simpa only [← H.map_comp] using congrArg H.map h

private theorem affineReverseUnit_cancel_square
    {C : Type*} [Category* C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    {u : X₁ ⟶ Y₁} {v : X₂ ⟶ Y₂} {a : X₁ ⟶ X₂} {b : Y₁ ⟶ Y₂}
    {c : Z₁ ⟶ Z₂} [Mono c] {tD : Y₁ ⟶ Z₁} {tI : Y₂ ⟶ Z₂}
    {βD : X₁ ⟶ Z₁} {βI : X₂ ⟶ Z₂}
    (hu : a ≫ v = u ≫ b) (ht : b ≫ tI = tD ≫ c)
    (hI : v ≫ tI = βI) (hβ : a ≫ βI = βD ≫ c) : u ≫ tD = βD := by
  apply (cancel_mono c).1
  calc
    (u ≫ tD) ≫ c = u ≫ b ≫ tI := by rw [Category.assoc, ← ht]
    _ = (a ≫ v) ≫ tI := by rw [← Category.assoc, ← hu]
    _ = βD ≫ c := by rw [Category.assoc, hI, hβ]

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- On an arbitrary representative with quasi-coherent cohomology, homology of the
right-derived unit followed by the fixed reverse comparison is the explicit kernel
lift/cokernel descent comparison. There is no module-valued exact family in this statement.
Source: Stacks Project, Tags 0AVW and 08D4, comparison with a K-injective resolution.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-reverse-unit).

Proof: Choose a quasi-isomorphism q:D→I with I K-injective. Preservation of kernels
makes the cycles lift natural in q; precomposition with the homology projection proves
naturality of the reverse homology map by the cokernel universal property. Apply this
square to q and transport through the localization/homology factors. Naturality of the
right-derived unit replaces its component at D by its component at I followed by the
mapped q. At I the asserted formula is the defining K-injective characterization of
the unique reverse comparison; the unit there is invertible. Naturality of that
comparison with Q(q), and cancellation of homology of Q(q), give the desired formula.
Only Q(q) needs to be invertible: termwise pushforward of q need not be a quasi-isomorphism.
This works for zero objects and arbitrary unbounded representatives. -/
theorem affineDerivedPushforwardSheafReverse_unit
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (D : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hD : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj D)) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
        (((RingedSpace.moduleDirectImage
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj D)) ≫
        (affineDerivedPushforwardSheafReverseIso A B φ i).hom.app ⟨_, hD⟩ =
      ((DerivedCategory.homologyFunctorFactors _ i).app
        (((RingedSpace.moduleDirectImage
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex
            (.up ℤ)).obj D)).hom ≫
      (D.sc i).leftExactHomologyComparison
        (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom) ≫
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
        (((DerivedCategory.homologyFunctorFactors _ i).app D).inv) := by
  let P := RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
  let HA := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) (.up ℤ)
  let τ := affineDerivedPushforwardSheafReverseIso A B φ i
  obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective D
  let : I.IsKInjective := hI
  let : QuasiIso s := hs
  have hQI : IsIso (DerivedCategory.Q.map s) := by infer_instance
  have hIQ : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj I) := by
    intro n
    exact (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso (asIso (DerivedCategory.Q.map s)))
      (hD n)
  have hKI : H.map (P.rightDerivedFunctorUnit.app (q.obj I)) ≫ τ.hom.app ⟨_, hIQ⟩ =
      ((DerivedCategory.homologyFunctorFactors _ i).app
        ((P.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
      (I.sc i).leftExactHomologyComparison P ≫
      P.map (((DerivedCategory.homologyFunctorFactors _ i).app I).inv) := by
    rw [affineDerivedPushforwardSheafReverseIso_KInjective]
    exact affineReverseUnit_map_unit_comp P I H _
  have hτ := τ.hom.naturality
    ((schemeDerivedQCohProperty (Spec (.of A))).homMk
      (X := ⟨_, hD⟩) (Y := ⟨_, hIQ⟩) (DerivedCategory.Q.map s))
  change H.map (P.rightDerivedFunctor.map (DerivedCategory.Q.map s)) ≫
      τ.hom.app ⟨_, hIQ⟩ = τ.hom.app ⟨_, hD⟩ ≫
      P.map (HA.map (DerivedCategory.Q.map s)) at hτ
  have hu' := affineReverseUnit_unit_naturality P s
  have hβ := affineReverseUnit_comparison_naturality P i s
  exact affineReverseUnit_cancel_square (affineReverseUnit_map_square H hu') hτ hKI hβ

end AlgebraicGeometry
