/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import WeilConjectures.Algebra.Homology.BoundedHomologyTensorAcyclic
import WeilConjectures.Algebra.Homology.DualKoszulHomologyTorsion
import WeilConjectures.Algebra.Homology.NilpotentCoefficientTensorAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone

/-! # Finite Koszul tensor vanishing after residue vanishing

## References

* Stacks Project, more-algebra.tex, Tags 0G1T and 0G1U
* Stacks Project, algebraization.tex, Tag 0A0E
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Each finite negative Koszul tensor stage vanishes when residue extension vanishes.
There is no completeness, boundedness or Noetherian hypothesis on the input complex.
-/
theorem finiteKoszulTensor_acyclic_of_residue
    {C : Type u} [SmallCategory C] {T : GrothendieckTopology C}
    {R S : Sheaf T CommRingCat.{u}} (q : R ⟶ S) (r : ℕ)
    (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (hq : ∀ U : C, Function.Surjective (q.hom.app (op U)))
    (hker : ∀ U : C, RingHom.ker (q.hom.app (op U)).hom =
      Ideal.span (Set.range (fun i ↦ (b i).val (op U))))
    (P : ringedSiteComplex R)
    (h₀ : IsZero ((ConstantCompletion.extend q).obj ((ConstantCompletion.Q R).obj P)))
    (n : ℕ) :
    (((ringedKoszulTensor R).obj P).obj
      ((ringedKoszulDualTower R r b).obj (op n))).Acyclic := by
  let A := ConstantCompletion.Mod R
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard (ConstantCompletion.Mod S)
  let := SheafOfModules.monoidalCategory R
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  obtain ⟨P', f, hP', hflat, hf, _⟩ := CochainComplex.exists_isKFlatResolution P
  have : QuasiIso f := hf
  have hK : P'.IsKFlatTensor := hP'
  have hz : IsZero ((ConstantCompletion.extend q).obj ((ConstantCompletion.Q R).obj P')) :=
    h₀.of_iso ((ConstantCompletion.extend q).mapIso
      (asIso ((ConstantCompletion.Q R).map f)))
  have hc : IsIso ((ConstantCompletion.extendComparison q).app P') :=
    (ConstantCompletion.derivedExtension q).computation P' hK
  have hE : (((ConstantCompletion.change q).mapHomologicalComplex (.up ℤ)).obj P').Acyclic :=
    (DerivedCategory.isZero_Q_obj_iff _).1
      (hz.of_iso (asIso ((ConstantCompletion.extendComparison q).app P')).symm)
  obtain ⟨hb, ht⟩ := dualKoszul_bounded_torsion R r b n
  have hac : (((ringedKoszulTensor R).obj P').obj
      ((ringedKoszulDualTower R r b).obj (op n))).Acyclic := by
    apply tensor_acyclic_of_bounded_homology R P' _ hK hflat
      ⟨-(r : ℤ), 0, hb⟩
    intro i
    exact tensor_acyclic_of_nilpotent_coefficient q r b hq hker P' hK hflat hE
      _ (r * (n + 1) + 1) (ht i)
  let K := (ringedKoszulDualTower R r b).obj (op n)
  have hk := ringed_cech_koszul_dual_tower_isKFlat R r b n
  let g := HomologicalComplex.mapBifunctorMap f (𝟙 K)
    (MonoidalCategory.curriedTensor _) (.up ℤ)
  have : QuasiIso g := by
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic g).2
    exact (hk (CochainComplex.mappingCone f)
      ((CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf)).of_iso
        (CochainComplex.mapBifunctorMappingCone₁Iso f K (MonoidalCategory.curriedTensor _))
  intro i
  exact (quasiIsoAt_iff_exactAt g i (hac i)).1 inferInstance

end CategoryTheory
