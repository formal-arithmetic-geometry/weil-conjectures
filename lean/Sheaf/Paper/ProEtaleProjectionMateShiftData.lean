/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Paper.ProEtaleFixedTensorRepresentativeComparison
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
# Shift and exactness data for the pro-etale projection mate

Source: Stacks, Cohomology on Sites, Tags 06YU, 07A4, 07A6 and 0B56.
(blueprint: lem-weil-pbc-proetale-projection-mate-shift-data-s4).

This is the first, strictly structural part of the native pro-etale projection-mate
argument: the two coefficient functors admit compatible integer shifts and are
triangulated.  The remaining natural transformation and its unit normalization are
recorded separately.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

private theorem tensorModel_exact (Z : Scheme.{u})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel Z RZ) (M : DerivedCategory (proEtaleRingModules Z RZ)) :
    ∃ _s : ((Functor.curryObj a.tensor).obj M).CommShift ℤ,
      ((Functor.curryObj a.tensor).obj M).IsTriangulated := by
  classical
  let A := proEtaleRingModules Z RZ
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  obtain ⟨P, q, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := RZ) (Q.objPreimage M)
  have hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology Z) (R := RZ)
      (P.X n) := fun n ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso RZ (P.X n)).symm (hf n)
  have hP : proEtaleFlatRepresentatives Z RZ P :=
    ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hp, hflat⟩
  have : QuasiIso q := hq
  let eM : Q.obj P ≅ M := asIso (Q.map q) ≪≫ Q.objObjPreimageIso M
  obtain ⟨s, hs⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated RZ
  let := s
  have ht := (hs P hp hflat).2.2.1.1
  obtain ⟨cL, _, _⟩ := (hs P hp hflat).2.2.2.1
  let F := (SheafOfModules.KFlatFixedTensor.derivedTensor RZ).obj (Q.obj P)
  have : F.IsTriangulated := ht
  obtain ⟨d, _⟩ := proEtale_fixed_tensor_representative_comparison Z RZ a P hP
  let T := SheafOfModules.KFlatFixedTensor.totalTensor RZ
  let j : T.obj P ⋙ Q ≅
      ((Functor.const _).obj P).prod' (𝟭 _) ⋙ Functor.uncurry.obj T ⋙ Q :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro B B' g
      simp [Functor.uncurry, Functor.prod'])
  let G := (Functor.curryObj a.tensor).obj (Q.obj P)
  let e : Q ⋙ F ≅ Q ⋙ G := cL.symm ≪≫ j ≪≫ d
  let i : F ≅ G := Localization.liftNatIso Q W (Q ⋙ F) (Q ⋙ G) F G e
  let k : F ≅ (Functor.curryObj a.tensor).obj M :=
    i ≪≫ (Functor.curryObj a.tensor).mapIso eM
  let := Functor.CommShift.ofIso k ℤ
  have : NatTrans.CommShift k.hom ℤ := Functor.CommShift.ofIso_compatibility k ℤ
  exact ⟨inferInstance, Functor.isTriangulated_of_iso k⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (E : DerivedCategory (proEtaleRingModules X S))

set_option linter.unusedVariables false in
/-- The source and target coefficient functors of the native pro-etale projection mate
have compatible integer shifts and are triangulated.
Source: Stacks, Tags 06YU, 07A4, 07A6 and 0B56.
(blueprint: lem-weil-pbc-proetale-projection-mate-shift-data-s4).
Proof: transport the signed total tensor shifts and the exact derived operations from
flat K-flat representatives through the native localization comparisons. -/
theorem proEtaleProjectionMateShiftData :
    ∃ (sF : ((Functor.curryObj a.tensor).obj
        ((proEtaleRingDerivedDirectImage f R S c).obj E)).CommShift ℤ)
      (sG : (proEtaleRingDerivedPullback f R S c ⋙
        (Functor.curryObj b.tensor).obj E ⋙
          proEtaleRingDerivedDirectImage f R S c).CommShift ℤ),
      ((Functor.curryObj a.tensor).obj
        ((proEtaleRingDerivedDirectImage f R S c).obj E)).IsTriangulated ∧
      (proEtaleRingDerivedPullback f R S c ⋙
        (Functor.curryObj b.tensor).obj E ⋙
          proEtaleRingDerivedDirectImage f R S c).IsTriangulated := by
  obtain ⟨sF, hF⟩ := tensorModel_exact Y R a
    ((proEtaleRingDerivedDirectImage f R S c).obj E)
  obtain ⟨sT, hT⟩ := tensorModel_exact X S b E
  let := sF
  let := sT
  have := hT
  refine ⟨sF, inferInstance, hF, ?_⟩
  infer_instance
end AlgebraicGeometry.Scheme
