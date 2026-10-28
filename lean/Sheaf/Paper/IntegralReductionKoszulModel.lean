/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
import all Sheaf.Paper.PrincipalKoszulStrictReplacement
import all Sheaf.Paper.FiniteReductionScalarNormalization
import all Sheaf.Paper.IntegralReductionTowerWellDefined
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Computing integral reduction on an arbitrary representative

Source: the finite-free quotient resolution in paragraph 1 of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 06YY, 08J7, and 07A6.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence

private noncomputable def tensorTowerFunctor
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (S : ℕᵒᵖ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ) :
    CochainComplex (Modules.{t, u} Y R) ℤ ⥤ (ℕᵒᵖ ⥤ Derived.{t, u} Y R) where
  obj N := S ⋙ (totalTensor.{t, u} Y R).obj N ⋙ DerivedCategory.Q
  map f := Functor.whiskerRight
    (Functor.whiskerLeft S ((totalTensor.{t, u} Y R).map f)) DerivedCategory.Q
  map_id N := by ext n; simp
  map_comp f g := by ext n; simp

private theorem tensorTower_inverts
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (S : ℕᵒᵖ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ)
    (hS : ∀ n, CochainComplex.IsKFlatIndependentCoefficients (R := R) (S.obj n)) :
    (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)).IsInvertedBy
      (tensorTowerFunctor.{t, u} Y R S) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective Y
  intro X X' f hf
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  have h := kFlatTensorPreservesQuasiIsoIndependentCoefficients R (S.obj n) (hS n) f hf
  change IsIso (DerivedCategory.Q.map (((totalTensor.{t, u} Y R).map f).app (S.obj n)))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
  exact h

private theorem tensorTower_representatives
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (S : ℕᵒᵖ ⥤ CochainComplex (Modules.{t, u} Y R) ℤ)
    (hS : ∀ n, CochainComplex.IsKFlatIndependentCoefficients (R := R) (S.obj n))
    (N P : CochainComplex (Modules.{t, u} Y R) ℤ)
    (e : DerivedCategory.Q.obj N ≅ DerivedCategory.Q.obj P) :
    Nonempty (S ⋙ (totalTensor.{t, u} Y R).obj N ⋙ DerivedCategory.Q ≅
      S ⋙ (totalTensor.{t, u} Y R).obj P ⋙ DerivedCategory.Q) := by
  let F := tensorTowerFunctor.{t, u} Y R S
  let hF := tensorTower_inverts.{t, u} Y R S hS
  let L := Localization.lift F hF DerivedCategory.Q
  let c := Localization.fac F hF DerivedCategory.Q
  exact ⟨(c.app N).symm ≪≫ L.mapIso e ≪≫ c.app P⟩

private theorem koszul_augmentation_tensor_quasiIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (P : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) P) (n : ℕ) :
    QuasiIso ((PrincipalKoszulStrictReplacement.comparison l E Y P).app (op n)) := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let M := PrincipalKoszulStrictReplacement.Modules l E Y
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let : MonoidalCategory M := SheafOfModules.monoidalCategory R
  let : SymmetricCategory M := SheafOfModules.symmetricCategory R
  let : MonoidalPreadditive M := SheafOfModules.tensorPreadditive R
  have (X : M) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X) := by
    have : PreservesColimitsOfSize.{max u (t + 1), max u (t + 1)}
        (MonoidalCategory.tensorLeft X) :=
      SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R X
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft X)
  have (X : M) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  let f := PrincipalKoszulStrictReplacement.augmentation l E Y n
  have hf := PrincipalKoszulStrictReplacement.augmentation_quasiIso l E Y n
  have := kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP f hf
  exact PrincipalKoszulStrictReplacement.quasiIso_conjugate
    (CochainComplex.Monoidal.braiding P (PrincipalKoszulStrictReplacement.koszul l E Y n))
    (CochainComplex.Monoidal.braiding P
      ((CochainComplex.singleFunctor M 0).obj
        (PrincipalKoszulStrictReplacement.residue l E Y n)))
    _ ((koszulTensorFunctor R P).map f)
    (CochainComplex.Monoidal.braiding_naturality_right (K := P) f)

private noncomputable def scalarReductionTowerIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) :
    PrincipalKoszulStrictReplacement.targetTower l E Y P ⋙ DerivedCategory.Q ≅
      integralReductionTower l E Y D hl P := by
  let F := ((CompletedTowerIndependent.reductionComplex l E Y).obj P).asFunctor
  let a : F ⋙ DerivedCategory.Q ⟶ integralReductionTower l E Y D hl P :=
    NatTrans.ofOpSequence (fun n ↦ 𝟙 _) (by
      intro n
      dsimp only [Functor.comp_map]
      rw [FiniteReductionTower.reduction_step]
      simp only [integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp]
      rw [integralTowerTransition_eq]
      rfl)
  exact Functor.isoWhiskerRight (FiniteReductionTower.scalarTowerIso l E Y P)
    DerivedCategory.Q ≪≫ NatIso.ofComponents (fun n ↦ Iso.refl _) (fun f ↦ a.naturality f)

/-- The fixed strict Koszul coefficient tower computes the actual reduction tower
on any representative of the resolved derived object.

Source: paragraph 1 of `lem-coef-integral-hom-reduction.proof.md`, and Stacks
Tags 06YY, 08J7, and 07A6 (blueprint: lem-sf-integral-reduction-koszul-model).

Proof: the compatible principal Koszul augmentations are quasi-isomorphisms by
regularity of the completed uniformizer, divisibility of the projection kernel,
and surjectivity of the projection. Tensor them with the given K-flat P. K-flat
invariance and the signed symmetry make this strict tower comparison objectwise
a quasi-isomorphism. The ordinary scalar-normalization isomorphism and the unique
pure-tensor formula for integralTowerTransition identify its target with the actual
reduction tower, including every transition. Localizing gives the desired model on P.
Each coefficient Koszul complex has bounded flat terms and is K-flat. Consequently
the functor taking N to its localized Koszul tensor tower inverts quasi-isomorphisms.
Descend the entire functor through DerivedCategory.Q and apply it to the composite
Q(P) ≅ Q(G) ≅ Q(N), using q and e. Compose with the model on P. No auxiliary
representative is chosen. The exponent n+1 is positive even at n=0; no boundedness
of N or flatness of its terms is used. The proof also applies to the zero complex
and empty site. -/
theorem integralReductionTower_koszul_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P G N : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (e : DerivedCategory.Q.obj N ≅ DerivedCategory.Q.obj G) :
    Nonempty (integralReductionTower l E Y D hl P ≅
      principalKoszulTower (completedIntegralCommRingSheaf l E Y D hl)
        (PrincipalKoszulStrictReplacement.uniformizer l E Y) ⋙
          (totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj N ⋙
            DerivedCategory.Q) := by
  let R := completedIntegralCommRingSheaf l E Y D hl
  let S := principalKoszulTower R (PrincipalKoszulStrictReplacement.uniformizer l E Y)
  have hS (n : ℕᵒᵖ) :
      CochainComplex.IsKFlatIndependentCoefficients (R := R) (S.obj n) := by
    have : (S.obj n).IsStrictlyLE 0 :=
      PrincipalKoszulStrictReplacement.koszul_bounded l E Y n.unop
    exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
      R (S.obj n) 0 (PrincipalKoszulStrictReplacement.koszul_flat l E Y n.unop)
  let b := Functor.whiskerRight
    (PrincipalKoszulStrictReplacement.comparison l E Y P) DerivedCategory.Q
  have hb : IsIso b := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    have := koszul_augmentation_tensor_quasiIso l E Y P hq.2 n.unop
    change IsIso (DerivedCategory.Q.map
      ((PrincipalKoszulStrictReplacement.comparison l E Y P).app n))
    infer_instance
  have : QuasiIso q := hq.1
  obtain ⟨c⟩ := tensorTower_representatives.{t, u} Y R S hS P N
    (asIso (DerivedCategory.Q.map q) ≪≫ e.symm)
  exact ⟨(scalarReductionTowerIso l E Y D hl P).symm ≪≫ (asIso b).symm ≪≫ c⟩

end WeilConjectures.IntegralHom
