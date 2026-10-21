/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Sheaf.AlgebraicGeometry.CoefficientTorFlatModel
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated

/-! # Shifts and quantitative Tor bounds on the pro-etale site

Source: Stacks Project, Cohomology on Sites, Tags 06YU and 08FZ;
Homology, Tags 011G and 011H (blueprint: lem-weil-proetale-tor-interval-shift).
The coefficient-sized small model is equivalent to the original small pro-etale site.
All tensor tests use the published K-flat derived tensor and ordinary module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme

/-- Restrict the published derived tensor to module sheaves in degree zero in its
second argument. This is composition of existing functors, with no new resolutions.
Source: Stacks Tag 06YU (blueprint: lem-weil-proetale-tor-interval-shift). -/
def coefficientProEtaleTorTensorTest (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (ConstantCompletion.D (ConstantCompletion.constant
      (coefficientProEtaleModelTopology.{u, v} Y) A) ×
    ConstantCompletion.Mod (ConstantCompletion.constant
      (coefficientProEtaleModelTopology.{u, v} Y) A)) ⥤
    ConstantCompletion.D (ConstantCompletion.constant
      (coefficientProEtaleModelTopology.{u, v} Y) A) :=
  let R := ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} Y) A
  letI : HasSheafify (coefficientProEtaleModelTopology.{u, v} Y)
      AddCommGrpCat.{max v (u + 1)} := coefficientModelAdditiveSheafify Y
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  (𝟭 (ConstantCompletion.D R)).prod
    ((HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0) ⋙
      ConstantCompletion.Q R) ⋙
    SheafOfModules.siteDerivedTensorIndependentCoefficients.{max v (u + 1),
      max v (u + 1), max v (u + 1), max v (u + 1) + 1}
      (coefficientProEtaleModelTopology.{u, v} Y) R

private theorem amplitude_iso {C : Type*} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat)
    {K L : ConstantCompletion.D R} (e : K ≅ L) (a b : ℤ) :
    HasCoefficientModelTorAmplitude R K a b ↔ HasCoefficientModelTorAmplitude R L a b := by
  constructor
  · rintro ⟨hab, hK⟩
    exact ⟨hab, fun P hP ⟨f⟩ ↦ hK P hP ⟨f ≪≫ e.symm⟩⟩
  · rintro ⟨hab, hL⟩
    exact ⟨hab, fun P hP ⟨f⟩ ↦ hL P hP ⟨f ≪≫ e⟩⟩

private theorem amplitude_shift {C : Type*} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat)
    (K : ConstantCompletion.D R) (a b m : ℤ) (hab : a ≤ b)
    (hK : HasCoefficientModelTorAmplitude R K a b) :
    HasCoefficientModelTorAmplitude R (K⟦m⟧) (a - m) (b - m) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  obtain ⟨P, hPa, hPb, hflat, ⟨e⟩⟩ :=
    (coefficientModelTorAmplitude_iff_flatModel R K a b hab).mp hK
  have := hPa
  have := hPb
  have := P.isStrictlyGE_shift a m (a - m) (by omega)
  have := P.isStrictlyLE_shift b m (b - m) (by omega)
  apply (coefficientModelTorAmplitude_iff_flatModel R _ _ _ (by omega)).mpr
  refine ⟨P⟦m⟧, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · intro i
    simpa only [CochainComplex.shiftFunctor_obj_X'] using hflat (i + m)
  · exact ((ConstantCompletion.Q R).commShiftIso m).app P ≪≫
      (shiftFunctor _ m).mapIso e

private theorem amplitude_zero {C : Type*} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat) :
    HasCoefficientModelTorAmplitude R 0 0 0 := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := SheafOfModules.monoidalCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  apply (coefficientModelTorAmplitude_iff_flatModel R 0 0 0 le_rfl).mpr
  refine ⟨0, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · intro i
    exact (ObjectProperty.flat_of_isZero
      ((HomologicalComplex.eval (ConstantCompletion.Mod R) (.up ℤ) i).map_isZero
        (isZero_zero _))).2
  · exact (ConstantCompletion.Q R).map_isZero (isZero_zero _) |>.isoZero

/-- Natural tensor and cohomology shift comparisons, the exact interval translation,
isomorphism invariance, and the zero test for arbitrary commutative coefficients.
The natural isomorphisms are on the product of the derived category and the entire
module-sheaf category, so they include naturality in both K and N.

Source: Stacks Tags 06YU and 08FZ, and Homology Tags 011G and 011H
(blueprint: lem-weil-proetale-tor-interval-shift).

Proof (the node's five steps):
1. Apply lem-pc-kflat-resolution to each N[0]. The fixed-tensor exact descent of
   lem-weil-pbc-kflat-fixed-tensor-triangulated gives the shift comparison in K.
   Its compatibility with maps of flat-term K-flat fixed arguments, followed by
   lem-weil-pbc-site-derived-tensor-descent, gives naturality in every N as well.
   The representative comparison identifies this with def-weil-derived-tensor.
2. Apply def-weil-derived-cohomology-sheaves to that natural comparison and compose
   with lem-sp-derived-cohomology-shift: H^i(T[m]) is H^(i+m)(T).
3. Unfold def-weil-proetale-tor-amplitude. An integer i is outside [a-m,b-m]
   precisely when i+m is outside [a,b]. This proves one implication. For the
   converse substitute i=j-m for every j outside [a,b]. The ordered endpoints
   remain ordered under subtraction, for positive, zero and negative m.
4. Tensor a derived isomorphism with every N and then apply cohomology. IsZero
   is invariant under isomorphism, so every vanishing test is equivalent.
5. Compute the total tensor of zero with a K-flat resolution of N. By
   def-pc-tensor-complex-sheaves each term is a direct sum of zero modules and
   every differential is zero. Its derived object and all its cohomology vanish.
   The Tor tests outside [0,0] therefore vanish for every N.
-/
theorem coefficientProEtaleTor_interval_shift (Y : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (∀ m : ℤ, Nonempty
      (((shiftFunctor (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) m).prod
          (𝟭 (ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)))) ⋙
          coefficientProEtaleTorTensorTest Y A ≅
        coefficientProEtaleTorTensorTest Y A ⋙
          shiftFunctor (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) m)) ∧
    (∀ i m : ℤ, Nonempty
      (((shiftFunctor (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) m).prod
          (𝟭 (ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)))) ⋙
          coefficientProEtaleTorTensorTest Y A ⋙
          coefficientModelCohomology (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A) i ≅
        coefficientProEtaleTorTensorTest Y A ⋙
          coefficientModelCohomology (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A) (i + m))) ∧
    (∀ (K : ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) (a b m : ℤ), a ≤ b →
      (HasCoefficientProEtaleTorAmplitude Y A K a b ↔
        HasCoefficientProEtaleTorAmplitude Y A (K⟦m⟧) (a - m) (b - m))) ∧
    (∀ (K L : ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) (_e : K ≅ L)
      (a b : ℤ), a ≤ b →
      (HasCoefficientProEtaleTorAmplitude Y A K a b ↔
        HasCoefficientProEtaleTorAmplitude Y A L a b)) ∧
    (∀ N : ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A),
      Nonempty (@Functor.obj _
        (CategoryTheory.prod'.{max v (u + 1) + 1, max v (u + 1)}
          (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A))
          (ConstantCompletion.Mod (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)))
        (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A)) inferInstance
        (coefficientProEtaleTorTensorTest.{u, v} Y A)
        ((0 : (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A))), N) ≅
        (0 : (ConstantCompletion.D (ConstantCompletion.constant
          (coefficientProEtaleModelTopology.{u, v} Y) A))))) ∧
    HasCoefficientProEtaleTorAmplitude Y A 0 0 0 := by
  classical
  let J := coefficientProEtaleModelTopology.{u, v} Y
  let R := ConstantCompletion.constant J A
  let : HasSheafify J AddCommGrpCat.{max v (u + 1)} := coefficientModelAdditiveSheafify Y
  let : HasDerivedCategory.{max v (u + 1) + 1} (ConstantCompletion.Mod R) :=
    HasDerivedCategory.standard _
  let T : ConstantCompletion.D R × ConstantCompletion.D R ⥤ ConstantCompletion.D R :=
    SheafOfModules.siteDerivedTensorIndependentCoefficients.{max v (u + 1),
      max v (u + 1), max v (u + 1), max v (u + 1) + 1} J R
  let G := Functor.curry.obj T
  obtain ⟨s, hs⟩ :=
    SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated.{max v (u + 1),
      max v (u + 1), max v (u + 1), max v (u + 1) + 1} R
  let : G.CommShift₂Int := s
  let S := (HomologicalComplex.single (ConstantCompletion.Mod R) (.up ℤ) 0) ⋙
    ConstantCompletion.Q R
  have tensorShift (m : ℤ) :
      (shiftFunctor (ConstantCompletion.D R) m).prod (𝟭 (ConstantCompletion.D R)) ⋙
        Functor.uncurry.obj G ≅
      Functor.uncurry.obj G ⋙ shiftFunctor (ConstantCompletion.D R) m := by
    refine NatIso.ofComponents
      (fun X ↦ ((G.flip.obj X.2).commShiftIso m).app X.1) ?_
    intro X X' f
    change ((G.flip.obj X.2).map (f.1⟦m⟧') ≫
      (G.flip.map f.2).app (X'.1⟦m⟧)) ≫ _ =
      _ ≫ (shiftFunctor _ m).map
        ((G.flip.obj X.2).map f.1 ≫ (G.flip.map f.2).app X'.1)
    simp only [Iso.app_hom]
    rw [Category.assoc, Functor.map_comp]
    rw [← NatTrans.shift_app_comm (G.flip.map f.2) m X'.1]
    rw [← Category.assoc, Functor.commShiftIso_hom_naturality]
    simp only [Category.assoc]
  have shiftIso (m : ℤ) :
      (shiftFunctor (ConstantCompletion.D R) m).prod (𝟭 (ConstantCompletion.Mod R)) ⋙
        coefficientProEtaleTorTensorTest Y A ≅
      coefficientProEtaleTorTensorTest Y A ⋙ shiftFunctor (ConstantCompletion.D R) m := by
    have e := Functor.isoWhiskerLeft ((𝟭 (ConstantCompletion.D R)).prod S) (tensorShift m)
    convert e using 1 <;>
      simp only [G, T, S, coefficientProEtaleTorTensorTest, Functor.uncurry_obj_curry_obj]
    · exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (by intros; simp; rfl)
    · exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (by intros; simp; rfl)
  refine ⟨fun m ↦ ⟨shiftIso m⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i m
    exact ⟨Functor.isoWhiskerRight (shiftIso m) (coefficientModelCohomology R i) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        ((DerivedCategory.homologyFunctor (ConstantCompletion.Mod R) 0).shiftIso
          m i (i + m) (by omega))⟩
  · intro K a b m hab
    constructor
    · exact amplitude_shift R K a b m hab
    · intro h
      have h' := amplitude_shift R (K⟦m⟧) (a - m) (b - m) (-m) (by omega) h
      have e := (shiftFunctorCompIsoId (ConstantCompletion.D R) m (-m)
        (add_neg_cancel m)).app K
      have h'' := (amplitude_iso R e _ _).mp h'
      simpa using h''
  · intro K L e a b _
    exact amplitude_iso R e a b
  · intro N
    obtain ⟨P, hP, hf, ⟨e⟩⟩ := exists_coefficientModelFlatKFlatRepresentative R (S.obj N)
    have hf' (i : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X i) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R (P.X i)).symm (hf i)
    have : (G.flip.obj ((ConstantCompletion.Q R).obj P)).IsTriangulated :=
      (hs P hP hf').2.2.1.2
    let d : G.flip.obj ((ConstantCompletion.Q R).obj P) ≅ G.flip.obj (S.obj N) :=
      G.flip.mapIso e
    have : (G.flip.obj (S.obj N)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_iso d
    exact ⟨((G.flip.obj (S.obj N)).map_isZero (isZero_zero _)).isoZero⟩
  · exact amplitude_zero R

end AlgebraicGeometry.Scheme
