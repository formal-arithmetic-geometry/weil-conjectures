/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorPresentationEvaluation
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.InternalHom
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorKoszulExistence
public import WeilConjectures.SixFunctors.IntegralHom.IntegralHomParameterAdjunction
import WeilConjectures.SixFunctors.IntegralHom.HomComplexTensorPureEquivalence
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationCoefficient
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SixFunctors.IntegralHom.IntegralHomParameterEvaluation

/-! # Canonical natural evaluation for a specified normalized tensor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.CoefDualFormulaScalarTranspose

/-- Fix the coefficient universe of the existing sheafification instance.
Source: Stacks 03DA (blueprint: def-coef-dual-formula-natural-evaluation). -/
theorem fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  IntegralHom.abSheafify.{u, u} X

/-- Fix the coefficient universe of the existing locally bijective criterion.
Source: Stacks 03DA (blueprint: def-coef-dual-formula-natural-evaluation). -/
theorem fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  IntegralHom.abLocallyBijective.{u, u} X

attribute [local instance 1000001] fixedSheafify fixedLocallyBijective

/-- Use the standard derived category in the fixed coefficient universe.
Source: derived localization (blueprint: def-coef-dual-formula-natural-evaluation). -/
@[instance_reducible]
def fixedDerivedCategory (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (IntegralHom.Modules.{u, u} X R) :=
  HasDerivedCategory.standard _

attribute [local instance 1000001] fixedDerivedCategory

/-- The native closed data with the fixed native monoidal structure and comparison.
Source: Stacks 08J9, native tensor-Hom localization
(blueprint: def-coef-dual-formula-natural-evaluation).
The defining theorem fixes the monoidal structure and the comparison exactly. Its
all-variable evaluation naturality and representative uncurrying fix the remaining
adjunctions: restriction to K-flat sources and parameters is fully faithful.
Thus its statement determines these data, rather than merely asserting existence
of an arbitrary closed structure. -/
def nativeClosed (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    CoefficientClosedStructure (IntegralHom.hom.{u, u} X R) := by
  let : HasDerivedCategory.{u + 2}
      (IntegralHom.Modules.{u, u} X R) :=
    HasDerivedCategory.standard _
  exact (RingedDerivedNative.closedAdjunction.{u + 1, u, u, u + 2}
    (ProEt.topology X) R).choose

/-- The native model has the fixed comparison; its other field is a proof.
Source: Stacks 08J9 (blueprint: def-coef-dual-formula-natural-evaluation). -/
def nativeModel (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    CoefficientTensorModels.{u, u + 1, u, u + 2} (ProEt.topology X) R (nativeClosed X R) := by
  let : HasDerivedCategory.{u + 2}
      (IntegralHom.Modules.{u, u} X R) :=
    HasDerivedCategory.standard _
  exact (RingedDerivedNative.closedAdjunction.{u + 1, u, u, u + 2}
    (ProEt.topology X) R).choose_spec.2.choose

/-- The natural exchange fixed by the Koszul value on every K-flat pair.
Source: Stacks 06YU, 0FPQ (blueprint: def-coef-dual-formula-natural-evaluation).
Its representative formula determines the natural isomorphism uniquely, by
faithfulness of restriction along the product K-flat localization. -/
def nativeExchange (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (nativeClosed X R).tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ (nativeClosed X R).tensor :=
  (ringedTensor_koszul_exists.{u + 1, u, u, u + 2}
    (ProEt.topology X) R (nativeClosed X R) (nativeModel X R)).choose

/-- Transport a closed right-tensor adjunction through a natural exchange.
Source: tensor-Hom adjunction (blueprint: def-coef-dual-formula-natural-evaluation). -/
def adjunctionOfExchange {A : Type*} [Category* A] {H : Aᵒᵖ × A ⥤ A}
    (T : A × A ⥤ A) (S : CoefficientClosedStructure H)
    (e : T ≅ CategoryTheory.Prod.swap A A ⋙ S.tensor) (K : A) :
    (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K) := by
  letI := S.monoidal
  exact (S.adjunction K).ofNatIsoLeft
    (NatIso.ofComponents (fun V ↦ (e.app (K, V)).symm) (by
      intro V V' f
      have h := e.inv.naturality (Prod.mkHom (𝟙 K) f)
      change (f ⊗ₘ 𝟙 K) ≫ e.inv.app (K, V') = _ at h
      rw [MonoidalCategory.tensorHom_id] at h
      exact h))

/-- The transported evaluation is the exchange followed by the native counit.
Source: adjunction transport (blueprint: def-coef-dual-formula-natural-evaluation). -/
theorem adjunctionOfExchange_counit {A : Type*} [Category* A] {H : Aᵒᵖ × A ⥤ A}
    (T : A × A ⥤ A) (S : CoefficientClosedStructure H)
    (e : T ≅ CategoryTheory.Prod.swap A A ⋙ S.tensor) (K W : A) :
    (adjunctionOfExchange T S e K).counit.app W =
      e.hom.app (K, H.obj (op K, W)) ≫ (S.adjunction K).counit.app W := by
  rfl

/-- Evaluation of the constructed adjunction is natural in its Hom source.
Source: closed evaluation naturality
(blueprint: def-coef-dual-formula-natural-evaluation).
Proof: move the two tensor maps through the natural exchange, then apply the
native all-variable evaluation equation. -/
theorem adjunctionOfExchange_natural {A : Type*} [Category* A] {H : Aᵒᵖ × A ⥤ A}
    (T : A × A ⥤ A) (S : CoefficientClosedStructure H)
    (e : T ≅ CategoryTheory.Prod.swap A A ⋙ S.tensor)
    (K K' W : A) (f : K' ⟶ K) :
    T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 W)))) ≫
        (adjunctionOfExchange T S e K').counit.app W =
      T.map (Prod.mkHom f (𝟙 _)) ≫
        (adjunctionOfExchange T S e K).counit.app W := by
  simp only [adjunctionOfExchange_counit]
  erw [e.hom.naturality_assoc, e.hom.naturality_assoc]
  congr 1
  let := S.monoidal
  simpa [CoefficientClosedStructure.tensor] using S.evaluation_naturality K K' W f

open WeilConjectures.IntegralHom CategoryTheory.MonoidalCategory

/-- The explicitly constructed adjunction has the signed chain evaluation field.
Source: Stacks 08J9, 06YU (blueprint: def-coef-dual-formula-natural-evaluation).
Proof: uncurry the chain map, precompose by the Koszul exchange, and compare pure
summands. The native model uncurrying square and the exchange comparison square
identify its localized map with the constructed adjunction counit. -/
theorem nativeAdjunction_evaluation (Y : Scheme.{u})
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    : ∀ (P I S' : CochainComplex (IntegralHom.Modules.{u,u} Y
      R) ℤ)
      (hP : flat.{u,u} Y R P)
      (hS : flat.{u,u} Y R S'), I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{u+1,u,u+1,u+1}
        (R := R) P I,
      ∃ beta : ((totalTensor.{u,u} Y R).obj P).obj S' ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S'.X j).val.obj U),
          (beta.f (i+j)).val.app U
            (totalPair.{u,u} Y R P S' i j U x s) =
            (i*j).negOnePow • evaluate.{u,u} Y R
              P I j i U ((q.f j).val.app U s) x) ∧
        (nativeModel Y R).comparison.inv.app (⟨P,hP⟩,⟨S',hS⟩) ≫ DerivedCategory.Q.map beta =
          (nativeClosed Y R).tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫ homModelMap.{u,u} Y
              R P I)) ≫
          (adjunctionOfExchange (nativeClosed Y R).tensor (nativeClosed Y R) (nativeExchange Y R)
            (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I) := by
  let J := ProEt.topology Y
  let S := nativeClosed Y R
  let T := nativeModel Y R
  have hkoszul := ringedTensor_koszul_exists.{u + 1, u, u, u + 2} J R S T
  let σ := nativeExchange Y R
  have hσ := hkoszul.choose_spec
  intro P I S' hP hS _ q
  have hrepresentative := hσ P S' hP hS
  let s := hrepresentative.choose
  have hs := hrepresentative.choose_spec.1
  have hsq := hrepresentative.choose_spec.2
  have hpure := homComplexTensor_pure_equivalence.{u, u} Y R S' P I
  change ∃ e : ((coefficientTotalTensor.{u, u + 1, u} J R).obj (S', P) ⟶ I) ≃
      (S' ⟶ homComplex.{u + 1, u, u + 1, u + 1} (R := R) P I),
    ∀ (f : (coefficientTotalTensor.{u, u + 1, u} J R).obj (S', P) ⟶ I)
      (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (x : (S'.X i).val.obj U) (y : (P.X j).val.obj U),
      evaluate.{u, u} Y R P I i j U (((e f).f i).val.app U x) y =
        (f.f (j + i)).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} J R S' P i j (j + i)
            (add_comm i j) U x y) at hpure
  let e := hpure.choose
  have he := hpure.choose_spec
  let ψ : (coefficientTotalTensor.{u, u + 1, u} J R).obj (S', P) ⟶ I := e.symm q
  have hψ : IsCoefficientTensorCurry.{u, u + 1, u} J R S' P I ψ q := by
    intro a b U x y
    have hc := (he ψ a b U x y).symm
    change _ = evaluate.{u, u} Y R P I a b U (((e (e.symm q)).f a).val.app U x) y at hc
    rw [Equiv.apply_symm_apply] at hc
    have hc' (k : ℤ) (h : b + a = k) :
        (ψ.f k).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} J R S' P a b k
            ((add_comm a b).trans h) U x y) =
        coefficientHomSectionApply.{u, u + 1, u} J R (P.X b) (I.X k) U
          ((coefficientHomComponent.{u, u + 1, u} J R P I a b k h).val.app U
            ((q.f a).val.app U x)) y := by
      subst k
      rw [evaluate_eq_coefficient] at hc
      exact hc
    exact hc' (a + b) (add_comm b a)
  have hn := coefficientTensorCurry_normalize.{u, u + 1, u, u + 2}
    J R S T S' P I hS hP ψ q hψ
  have hinput : DerivedCategory.Q.map
        (q ≫ ((homComplexFunctor (R := R)).obj (op P)).map
          ((coefficientHomAugmentation.{u, u + 1, u} J R).app I)) ≫
        (coefficientHomResolutionIso.{u, u + 1, u, u + 2} J R P I).inv =
      DerivedCategory.Q.map q ≫ homModelMap.{u, u} Y R P I := by
    dsimp only [homModelMap, coefficientHomAugmentation]
    erw [Functor.map_comp, Category.assoc]
    rfl
  rw [hinput] at hn
  refine ⟨s.hom ≫ ψ, ?_, ?_⟩
  · intro i j U x y
    change (ψ.f (i + j)).val.app U
      ((s.hom.f (i + j)).val.app U _) = _
    have hs' := hs i j (i + j) rfl (add_comm j i) U x y
    rw [show totalPair.{u, u} Y R P S' i j U x y =
      coefficientTensorGenerator.{u, u + 1, u} J R P S' i j (i + j) rfl U x y by
      simp only [IntegralHom.totalPair, IntegralHom.pair, IntegralHom.ordinaryTensor,
        coefficientTensorGenerator,
        CochainComplex.ιMapBifunctor]
      rfl]
    rw [hs']
    simp only [Units.smul_def, map_zsmul]
    congr 1
    have hc := (he ψ j i U y x).symm
    change _ = evaluate.{u, u} Y R P I j i U (((e (e.symm q)).f j).val.app U y) x at hc
    rw [Equiv.apply_symm_apply] at hc
    exact hc
  · change (T.iso J R S P S' hP hS).inv ≫ DerivedCategory.Q.map (s.hom ≫ ψ) = _
    have hswap : (T.iso J R S P S' hP hS).inv ≫ DerivedCategory.Q.map s.hom =
        σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj S') ≫
          (T.iso J R S S' P hS hP).inv := by
      apply (cancel_epi (T.iso J R S P S' hP hS).hom).1
      apply (cancel_mono (T.iso J R S S' P hS hP).hom).1
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
      with_unfolding_all exact hsq.symm
    exact (IntegralHom.map_comp_exchange DerivedCategory.Q _ _ _ _ s.hom ψ hswap hn.symm).trans
      ((IntegralHom.swappedAdjunction_uncurry S σ (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj S') (DerivedCategory.Q.obj I)
        (DerivedCategory.Q.map q ≫ homModelMap.{u, u} Y R P I)).symm.trans
          (IntegralHom.curry_counit S.tensor (DerivedCategory.Q.obj P)
            (IntegralHom.swappedAdjunction S σ (DerivedCategory.Q.obj P)) _ _ _))

/-- Fix the tensor comparison by its K-flat representative square.
Source: product localization (blueprint: def-coef-dual-formula-natural-evaluation). -/
def TensorComparisonNormalized (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) (e : (nativeClosed X R).tensor ≅ a.tensor) : Prop :=
  (nativeModel X R).comparison ≪≫ Functor.isoWhiskerLeft
    ((coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology X) R ⋙ DerivedCategory.Q).prod
      (coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology X) R ⋙ DerivedCategory.Q)) e =
    a.representative

/-- The native tensor has exactly one comparison with the prescribed representative.
Source: K-flat localization (blueprint: def-coef-dual-formula-natural-evaluation).
Proof: restrict along the product K-flat localization, take the fully faithful
preimage of the quotient of the representative comparisons, and use faithfulness
and cancellation of the source comparison to prove uniqueness. -/
theorem tensorComparison_existsUnique (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) :
    ∃! e : (nativeClosed X R).tensor ≅ a.tensor, TensorComparisonNormalized X R a e := by
  let : HasDerivedCategory.{u + 2}
      (IntegralHom.Modules.{u, u} X R) :=
    HasDerivedCategory.standard _
  let q := coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology X) R ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (IntegralHom.Modules.{u, u} X R) (.up ℤ)).inverseImage
    (coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology X) R)
  have : q.IsLocalization W :=
    RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2} (ProEt.topology X) R
  let FF := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (W.prod W)
    (Derived.{u, u} X R)
  let e := FF.preimageIso ((nativeModel X R).comparison.symm ≪≫ a.representative)
  have he : Functor.isoWhiskerLeft (q.prod q) e =
      (nativeModel X R).comparison.symm ≪≫ a.representative := by
    apply Iso.ext
    exact FF.map_preimage _
  have hn : TensorComparisonNormalized X R a e := by
    change (nativeModel X R).comparison ≪≫ Functor.isoWhiskerLeft (q.prod q) e = _
    erw [he]
    exact Iso.self_symm_id_assoc _ _
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply FF.map_injective
  ext Z
  have h := congrArg (fun i ↦ i.hom.app Z) he'
  have h0 := congrArg (fun i ↦ i.hom.app Z) hn
  exact (cancel_epi ((nativeModel X R).comparison.hom.app Z)).mp (h.trans h0.symm)

/-- The uniquely normalized comparison to the supplied tensor functor.
Source: K-flat localization (blueprint: def-coef-dual-formula-natural-evaluation). -/
def tensorComparison (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) :=
  (tensorComparison_existsUnique X R a).exists.choose

/-- Naturality-normalized evaluation, keeping the supplied tensor and representative.
Source: Stacks 08J9 (blueprint: def-coef-dual-formula-natural-evaluation). -/
def canonicalEvaluationAdjunction (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) (K : Derived.{u, u} X R) :=
  adjunctionOfExchange a.tensor (nativeClosed X R)
    ((tensorComparison X R a).symm ≪≫ nativeExchange X R) K

/-- The canonical evaluation retains the representative signed-evaluation field.
Source: Stacks 08J9, 06YU
(blueprint: def-coef-dual-formula-natural-evaluation).
Proof: use the explicit native signed-evaluation chain map. The normalized tensor
comparison identifies the two representative isomorphisms. Move the tensor map
through that comparison by naturality; the native counit equation is then exactly
the required equation for the transported adjunction. -/
theorem canonicalEvaluation_field (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R)
    (P I S : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (hP : flat.{u, u} X R P) (hS : flat.{u, u} X R S) (hI : I.IsKInjective)
    (q : S ⟶ homComplex.{u + 1, u, u + 1, u + 1} (R := R) P I) :
    ∃ beta : ((totalTensor.{u, u} X R).obj P).obj S ⟶ I,
      (∀ (i j : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X i).val.obj U) (s : (S.X j).val.obj U),
        (beta.f (i + j)).val.app U (totalPair.{u, u} X R P S i j U x s) =
          (i * j).negOnePow • evaluate.{u, u} X R P I j i U ((q.f j).val.app U s) x) ∧
      a.representative.inv.app (⟨P, hP⟩, ⟨S, hS⟩) ≫ DerivedCategory.Q.map beta =
        a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
          (DerivedCategory.Q.map q ≫ homModelMap.{u, u} X R P I)) ≫
        (canonicalEvaluationAdjunction X R a (DerivedCategory.Q.obj P)).counit.app
          (DerivedCategory.Q.obj I) := by
  obtain ⟨beta, hpure, hb⟩ := nativeAdjunction_evaluation X R P I S hP hS hI q
  refine ⟨beta, hpure, ?_⟩
  let e := tensorComparison X R a
  have he := (tensorComparison_existsUnique X R a).exists.choose_spec
  have hi := congrArg (fun z ↦ z.inv.app (⟨P, hP⟩, ⟨S, hS⟩)) he
  change e.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj S) ≫
    (nativeModel X R).comparison.inv.app (⟨P, hP⟩, ⟨S, hS⟩) = _ at hi
  erw [← hi, Category.assoc, hb]
  simp only [canonicalEvaluationAdjunction, adjunctionOfExchange_counit,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  erw [Category.assoc, ← e.inv.naturality_assoc]

/-- Evaluation normalized in all variables without changing tensor or its comparison.
Source: Stacks 08J9 (blueprint: def-coef-dual-formula-natural-evaluation). -/
def normalizedTensorPresentation (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : TensorPresentation.{u, u} X R) : TensorPresentation.{u, u} X R where
  tensor := a.tensor
  representative := a.representative
  parameterAdjunction := parameterAdjunctionOfCounit (canonicalEvaluationAdjunction X R a)
    (fun K K' W f ↦ adjunctionOfExchange_natural a.tensor (nativeClosed X R)
      ((tensorComparison X R a).symm ≪≫ nativeExchange X R) K' K W f)
  evaluation := canonicalEvaluation_field X R a

end WeilConjectures.CoefDualFormulaScalarTranspose
