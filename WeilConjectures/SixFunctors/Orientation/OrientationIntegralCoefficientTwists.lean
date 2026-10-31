/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChange
public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.PuritySourceTransports
import all WeilConjectures.SixFunctors.Supporting.PositiveRootGeneratorExt
import WeilConjectures.SixFunctors.Supporting.PositiveRootTensorProduct
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SixFunctors.Integral.IntegralPullbackAugmentationAmbient
import Mathlib.Data.Nat.Prime.Infinite
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Canonical positive coefficient-line comparisons

Source: main-20261015, def-coefficient-twists-detailed, completed tensor and
scheme pullback conventions (blueprint: def-sf-orientation-integral-line-comparisons).
The original coefficient lines are reexported. Their normalized inverse-image
maps are supplied for arbitrary scheme morphisms, as required by orientations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] WeilConjectures.IntegralOnSlice.completion
  WeilConjectures.IntegralOnSlice.completionComparison
  WeilConjectures.IntegralOnSlice.completionUnit
  WeilConjectures.IntegralOnSlice.duality WeilConjectures.IntegralOnSlice.roosUnit
  WeilConjectures.IntegralAmbient.tensorTowerIso HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.coefficientTotalTensor SheafOfModules.monoidalCategory
  WeilConjectures.IntegralOnSlice.tower WeilConjectures.IntegralOnSlice.augmentation
  WeilConjectures.integralOperationsTensorTowerFunctor
attribute [local implicit_reducible] WeilConjectures.completedIntegralCommRingSheafUnrestricted
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

section IntegralLinePullbackProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
attribute [local implicit_reducible] PurCompactSupport.completed

/-- The inverse-image map of a positive completed line for an arbitrary base map.
Every local scalar and every compatible root is retained. Unlike the Frobenius
interface, this statement does not require the map of schemes to be invertible.
Source: base naturality in clause 1 (blueprint: def-sf-orientation-integral-line-comparisons).
Proof: use the projection-normalized completed coefficient map and root-limit map.
The integral inverse-image theorem identifies their tensor product with the first
line. Apply tensor pullback recursively. At degree zero use the coefficient map.
The indicated pure tensors generate locally, so the formulas determine every map.
The locally free rank-one comparisons are invertible on a pro-etale cover, hence
globally. This proof applies to every morphism and to the empty scheme. -/
theorem sfOrientationIntegralLineMaps_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! tau : ∀ d : ℕ,
      (FrobeniusCoefficientTwists.modulePull l E g).obj
        (FrobeniusCoefficientTwists.positiveLine l E Y d) ≅
          FrobeniusCoefficientTwists.positiveLine l E X d,
      ∀ (d : ℕ) (V : Y.ProEt)
        (a : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
          (Opposite.op V)) (x : Fin d → (purTwistZlOne Y l).obj.obj (Opposite.op V)),
        (tau d).hom.val.app (Opposite.op ((proEtaleBaseChange g).obj V))
          (FrobeniusCoefficientTwists.moduleSection l E g
            (FrobeniusCoefficientTwists.positiveLine l E Y d) V
            (FrobeniusCoefficientTwists.generator l E Y (Opposite.op V) a d x)) =
        FrobeniusCoefficientTwists.generator l E X
          (Opposite.op ((proEtaleBaseChange g).obj V))
          ((sfCompletedCoefficientMap l E g).hom.app (Opposite.op V) a) d
          (fun i ↦ FrobeniusCoefficientTwists.rootSection l g V (x i)) := by
  obtain ⟨τ, hτ⟩ := sfIntegralPositiveRootLineMaps_exists l E g
  refine ⟨τ, hτ, ?_⟩
  intro other hother
  funext d
  apply Iso.ext
  apply ((proEtaleRingModuleAdjunction g
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull g)).homEquiv _ _).injective
  apply sfPositiveRootGenerator_hom_ext l E Y d
  intro V a x
  exact (hother d V.unop a x).trans (hτ d V.unop a x).symm

end IntegralLinePullbackProof

/-- The actual completed-module line map selected by its unique root formula.
Source: clause 1, pullback/twist comparison
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralLineMaps
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (FrobeniusCoefficientTwists.modulePull l E g).obj
      (FrobeniusCoefficientTwists.positiveLine l E Y d) ≅
        FrobeniusCoefficientTwists.positiveLine l E X d :=
  (sfOrientationIntegralLineMaps_existsUnique l E g).exists.choose d

/-- A positive Tate line with its even shift, in its one-term complex model.
Source: coefficient conventions, Lambda(d)[2d]
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralComplex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d : ℕ) :
    CochainComplex (integralTowerModules l E X) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).obj
    (FrobeniusCoefficientTwists.positiveLine l E X d)

/-- Insert a pure root tensor into the only nonzero term of the shifted line.
Source: positive tensor powers and cohomological shifts
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralComplexGenerator
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d : ℕ) (U : X.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (x : Fin d → (purTwistZlOne X l).obj.obj U) :
    ((sfOrientationIntegralComplex l E X d).X (-2 * (d : ℤ))).val.obj U :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (-2 * (d : ℤ))
    (FrobeniusCoefficientTwists.positiveLine l E X d)).inv.val.app U
      (FrobeniusCoefficientTwists.generator l E X U a d x)

/-- The shifted line is still a flat-term K-flat representative.
Source: coefficient-line conventions (blueprint: def-sf-orientation-integral-line-comparisons).
Proof: each positive root line is locally free of rank one, including the unit
at zero. The complex is supported in one degree, so tensoring with it is an exact
line tensor followed by a shift. It therefore preserves acyclic complexes; every
term is either this flat line or zero. -/
theorem sfOrientationIntegralComplex_good
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :
    integralOperationsGoodComplex l E X (sfOrientationIntegralComplex l E X d) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  have hline : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R)
      (FrobeniusCoefficientTwists.positiveLine l E X d) := by
    exact (coefficientTwistLine_exact X (R := R) (purTwistIntegralModule X l E) (d : ℤ)).2
  have hterms : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R)
      ((sfOrientationIntegralComplex l E X d).X i) := by
    intro i
    by_cases hi : i = -2 * (d : ℤ)
    · subst i
      simpa only [sfOrientationIntegralComplex, HomologicalComplex.single_obj_X_self]
        using hline
    · let M := (sfOrientationIntegralComplex l E X d).X i
      have hM : IsZero M := HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
      apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion R M
      intro U n a s hs
      refine ⟨⊤, (ProEt.topology X).top_mem U, ?_⟩
      intro V f hf
      refine ⟨0, (fun _ ↦ Fin.elim0), Fin.elim0, ?_, fun q ↦ Fin.elim0 q⟩
      intro p
      have : Subsingleton (M.val.obj (Opposite.op V)) :=
        ModuleCat.subsingleton_of_isZero
          ((SheafOfModules.evaluation _ (Opposite.op V)).map_isZero hM)
      change (M.val.map f.op (s p) : M.val.obj (Opposite.op V)) = _
      exact @Subsingleton.elim (M.val.obj (Opposite.op V)) this _ _
  have : (sfOrientationIntegralComplex l E X d).IsStrictlyLE (-2 * (d : ℤ)) := by
    dsimp only [sfOrientationIntegralComplex]
    infer_instance
  exact ⟨SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R _ (-2 * (d : ℤ)) hterms, hterms⟩

section SingleTensor
open CategoryTheory.MonoidalCategory
variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]
  [HasZeroObject C] [HasCountableCoproducts C]
  [(curriedTensor C).PreservesZeroMorphisms]
  [∀ M : C, ((curriedTensor C).obj M).PreservesZeroMorphisms]

private abbrev singleAt (M : C) (p : ℤ) :=
  (HomologicalComplex.single C (.up ℤ) p).obj M

private abbrev totalSingles (M N : C) (p q : ℤ) :=
  HomologicalComplex.mapBifunctor (singleAt M p) (singleAt N q) (curriedTensor C) (.up ℤ)

omit [HasCountableCoproducts C] in
private theorem singleTensorTermZero (M N : C) (p q a b : ℤ)
    (h : a ≠ p ∨ b ≠ q) :
    IsZero ((singleAt M p).X a ⊗ (singleAt N q).X b) := by
  rcases h with h | h
  · exact (tensorRight _).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  · exact (tensorLeft _).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

omit [HasCountableCoproducts C] in
private theorem singleTensorSupportZero (M N : C) (p q n : ℤ) (h : n ≠ p + q) :
    IsZero ((totalSingles M N p q).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  apply (singleTensorTermZero M N p q a b ?_).eq_of_src
  by_cases ha : a = p
  · right
    intro hb
    subst a
    subst b
    exact h hab.symm
  · exact Or.inl ha

private def singleTensorSummandIso (M N : C) (p q : ℤ) :
    (singleAt M p).X p ⊗ (singleAt N q).X q ≅
      (totalSingles M N p q).X (p + q) where
  hom := HomologicalComplex.ιMapBifunctor _ _ (curriedTensor C) (.up ℤ) p q (p + q) rfl
  inv := HomologicalComplex.mapBifunctorDesc (fun a b _ ↦
    if h : a = p ∧ b = q then
      (HomologicalComplex.XIsoOfEq _ h.1).hom ⊗ₘ
        (HomologicalComplex.XIsoOfEq _ h.2).hom
    else 0)
  hom_inv_id := by
    erw [HomologicalComplex.ι_mapBifunctorDesc]
    simp
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    by_cases ha : a = p
    · subst a
      have hb : b = q := by change p + b = p + q at hab; omega
      subst b
      erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
      simp
    · apply (singleTensorTermZero M N p q a b (Or.inl ha)).eq_of_src

private def singleTensorDegreeIso (M N : C) (p q : ℤ) :
    M ⊗ N ≅ (totalSingles M N p q).X (p + q) :=
  tensorIso (HomologicalComplex.singleObjXSelf (.up ℤ) p M).symm
      (HomologicalComplex.singleObjXSelf (.up ℤ) q N).symm ≪≫
    singleTensorSummandIso M N p q

private def singleTensorIso (M N : C) (p q : ℤ) :
    totalSingles M N p q ≅ singleAt (M ⊗ N) (p + q) := by
  let e := singleTensorDegreeIso M N p q
  let f : singleAt (M ⊗ N) (p + q) ⟶ totalSingles M N p q :=
    HomologicalComplex.mkHomFromSingle e.hom (by
      intro n hn
      apply (singleTensorSupportZero M N p q n
        (by change p + q + 1 = n at hn; omega)).eq_of_tgt)
  have hf (n : ℤ) : IsIso (f.f n) := by
    by_cases hn : n = p + q
    · subst n
      dsimp only [f]
      rw [HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) (p + q)
        (M ⊗ N) n hn).isIso (singleTensorSupportZero M N p q n hn) _
  let : ∀ n, IsIso (f.f n) := hf
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact (asIso f).symm

omit [HasCountableCoproducts C] in
private theorem singleTensorIso_inv_f (M N : C) (p q : ℤ) :
    (singleTensorIso M N p q).inv.f (p + q) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) (M ⊗ N)).hom ≫
        (singleTensorDegreeIso M N p q).hom := by
  unfold singleTensorIso
  dsimp only [Iso.symm_inv, asIso_hom]
  rw [HomologicalComplex.mkHomFromSingle_f]

omit [HasCountableCoproducts C] in
private theorem singleTensorIso_hom_f (M N : C) (p q : ℤ) :
    (singleTensorIso M N p q).hom.f (p + q) =
      (singleTensorDegreeIso M N p q).inv ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) (M ⊗ N)).inv := by
  have h := congrArg (fun f ↦ f.f (p + q)) (singleTensorIso M N p q).inv_hom_id
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, singleTensorIso_inv_f] at h
  rw [← cancel_epi (singleTensorDegreeIso M N p q).hom,
    ← cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) (M ⊗ N)).hom]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id] using h

private def singleTensorExtract (M N L : C) (p q : ℤ)
    (m : totalSingles M N p q ≅ singleAt L (p + q)) : M ⊗ N ≅ L :=
  singleTensorDegreeIso M N p q ≪≫
    (HomologicalComplex.eval C (.up ℤ) (p + q)).mapIso m ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) L

private def singleTensorLift (M N L : C) (p q : ℤ) (m : M ⊗ N ≅ L) :
    totalSingles M N p q ≅ singleAt L (p + q) :=
  singleTensorIso M N p q ≪≫ (HomologicalComplex.single C (.up ℤ) (p + q)).mapIso m

omit [HasCountableCoproducts C] in
private theorem singleTensorExtract_lift (M N L : C) (p q : ℤ) (m : M ⊗ N ≅ L) :
    singleTensorExtract M N L p q (singleTensorLift M N L p q m) = m := by
  apply Iso.ext
  simp only [singleTensorExtract, singleTensorLift, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.comp_f, HomologicalComplex.eval_map,
    singleTensorIso_hom_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

omit [HasCountableCoproducts C] in
private theorem singleTensorExtract_injective (M N L : C) (p q : ℤ) :
    Function.Injective (singleTensorExtract M N L p q) := by
  intro a b hab
  apply Iso.ext
  apply HomologicalComplex.to_single_hom_ext
  have h := congrArg Iso.hom hab
  dsimp only [singleTensorExtract, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.eval_map] at h
  change (singleTensorDegreeIso M N p q).hom ≫ a.hom.f (p + q) ≫ _ =
    (singleTensorDegreeIso M N p q).hom ≫ b.hom.f (p + q) ≫ _ at h
  exact (cancel_epi (singleTensorDegreeIso M N p q).hom).mp
    ((cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) L).hom).mp
      (by simpa only [Category.assoc] using h))

end SingleTensor

section RootTensor
attribute [local semireducible] coefficientTotalTensor
attribute [local implicit_reducible] coefficientTotalTensor
open CategoryTheory.MonoidalCategory

private theorem rootTensorExtract_pure
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (M N L : integralTowerModules l E X) (p q : ℤ) :
    letI := SheafOfModules.monoidalCategory
      (completedIntegralCommRingSheafUnrestricted l E X)
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedIntegralCommRingSheafUnrestricted l E X)
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedIntegralCommRingSheafUnrestricted l E X)
    ∀ (m : totalSingles M N p q ≅ singleAt L (p + q))
      (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      (singleTensorExtract M N L p q m).hom.val.app U
        (SheafOfModules.ScalarHomOrdinary.pure
          (completedIntegralCommRingSheafUnrestricted l E X) M N U x y) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) L).hom.val.app U
        ((m.hom.f (p + q)).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            (singleAt M p) (singleAt N q) p q (p + q) rfl U
            ((HomologicalComplex.singleObjXSelf (.up ℤ) p M).inv.val.app U x)
            ((HomologicalComplex.singleObjXSelf (.up ℤ) q N).inv.val.app U y))) := by
  let := SheafOfModules.monoidalCategory
    (completedIntegralCommRingSheafUnrestricted l E X)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E X)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (completedIntegralCommRingSheafUnrestricted l E X)
  intro m U x y
  dsimp only [singleTensorExtract, singleTensorDegreeIso, Iso.trans_hom,
    Functor.mapIso_hom, HomologicalComplex.eval_map]
  change (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) L).hom.val.app U
    ((m.hom.f (p + q)).val.app U
      ((singleTensorSummandIso M N p q).hom.val.app U
        ((tensorIso (HomologicalComplex.singleObjXSelf (.up ℤ) p M).symm
          (HomologicalComplex.singleObjXSelf (.up ℤ) q N).symm).hom.val.app U
            (SheafOfModules.ScalarHomOrdinary.pure
              (completedIntegralCommRingSheafUnrestricted l E X) M N U x y)))) = _
  simp only [CategoryTheory.MonoidalCategory.tensorIso_hom, Iso.symm_hom]
  exact congrArg (fun z ↦
    (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) L).hom.val.app U
      ((m.hom.f (p + q)).val.app U
        ((singleTensorSummandIso M N p q).hom.val.app U z)))
    (SheafOfModules.ScalarHomOrdinary.pure_map
      (completedIntegralCommRingSheafUnrestricted l E X)
      (HomologicalComplex.singleObjXSelf (.up ℤ) p M).inv
      (HomologicalComplex.singleObjXSelf (.up ℤ) q N).inv U x y)

/-- Multiplication in the ordinary total tensor is fixed on every pure root tensor.
This includes all scalar factors; no trivialization of the root line is chosen.
Source: coefficient multiplicativity and tensor-shift convention
(blueprint: def-sf-orientation-integral-line-comparisons).
Proof: the total tensor of the two single complexes has only the summand
(-2d,-2e). Reassociate the two positive root powers, with scalar multiplication
at exponent zero. The ordinary tensor universal property makes this a sheaf map.
Its inverse splits the ordered list of roots after d entries; balancing identifies
the scalar factors. Both differentials vanish. The degree identity is
-2d-2e=-2(d+e), with no odd Koszul sign. The two maps are inverse on pure tensors,
which generate after sheafification. These generators also prove uniqueness. -/
theorem sfOrientationIntegralComplexProduct_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d e : ℕ) :
    ∃! m : (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)).obj
          (sfOrientationIntegralComplex l E X d, sfOrientationIntegralComplex l E X e) ≅
        sfOrientationIntegralComplex l E X (d + e),
      ∀ (U : X.ProEtᵒᵖ)
        (a b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
        (x : Fin d → (purTwistZlOne X l).obj.obj U)
        (y : Fin e → (purTwistZlOne X l).obj.obj U),
        HEq ((m.hom.f (-2 * (d : ℤ) + -2 * (e : ℤ))).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X)
            (sfOrientationIntegralComplex l E X d) (sfOrientationIntegralComplex l E X e)
            (-2 * (d : ℤ)) (-2 * (e : ℤ)) (-2 * (d : ℤ) + -2 * (e : ℤ)) rfl U
            (sfOrientationIntegralComplexGenerator l E X d U a x)
            (sfOrientationIntegralComplexGenerator l E X e U b y)))
          (sfOrientationIntegralComplexGenerator l E X (d + e) U (a * b)
            (Fin.addCases x y)) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let M := FrobeniusCoefficientTwists.positiveLine l E X d
  let N := FrobeniusCoefficientTwists.positiveLine l E X e
  let L := FrobeniusCoefficientTwists.positiveLine l E X (d + e)
  let p : ℤ := -2 * (d : ℤ)
  let q : ℤ := -2 * (e : ℤ)
  have hdeg : -2 * ((d + e : ℕ) : ℤ) = p + q := by dsimp [p, q]; omega
  let P (r : ℤ) : Prop :=
    ∃! m : totalSingles M N p q ≅ singleAt L r,
      ∀ (U : X.ProEtᵒᵖ)
        (a b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
        (x : Fin d → (purTwistZlOne X l).obj.obj U)
        (y : Fin e → (purTwistZlOne X l).obj.obj U),
        HEq ((m.hom.f (p + q)).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R
            (singleAt M p) (singleAt N q) p q (p + q) rfl U
            ((HomologicalComplex.singleObjXSelf (.up ℤ) p M).inv.val.app U
              (FrobeniusCoefficientTwists.generator l E X U a d x))
            ((HomologicalComplex.singleObjXSelf (.up ℤ) q N).inv.val.app U
              (FrobeniusCoefficientTwists.generator l E X U b e y))))
          ((HomologicalComplex.singleObjXSelf (.up ℤ) r L).inv.val.app U
            (FrobeniusCoefficientTwists.generator l E X U (a * b) (d + e)
              (Fin.addCases x y)))
  change P (-2 * ((d + e : ℕ) : ℤ))
  suffices h : P (p + q) from hdeg.symm ▸ h
  dsimp only [P]
  simp only [heq_iff_eq]
  obtain ⟨μ, hμ, hμunique⟩ := positiveRootTensorProduct_existsUnique l E X d e
  let m := singleTensorLift M N L p q μ
  have hext := singleTensorExtract_lift M N L p q μ
  refine ⟨m, ?_, ?_⟩
  · intro U a b x y
    apply (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ U).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) L).hom)).1
    have h := rootTensorExtract_pure l E X M N L p q m U
      (FrobeniusCoefficientTwists.generator l E X U a d x)
      (FrobeniusCoefficientTwists.generator l E X U b e y)
    rw [hext] at h
    exact h.symm.trans ((hμ U a b x y).trans (congrArg (fun f ↦ f.val.app U
      (FrobeniusCoefficientTwists.generator l E X U (a * b) (d + e)
        (Fin.addCases x y)))
      (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) L).inv_hom_id).symm)
  · intro other hother
    apply singleTensorExtract_injective M N L p q
    rw [hext]
    apply hμunique
    intro U a b x y
    exact (rootTensorExtract_pure l E X M N L p q other U
      (FrobeniusCoefficientTwists.generator l E X U a d x)
      (FrobeniusCoefficientTwists.generator l E X U b e y)).trans
      ((congrArg
        (fun z ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) L).hom.val.app U z)
        (hother U a b x y)).trans
        (congrArg (fun f ↦ f.val.app U
          (FrobeniusCoefficientTwists.generator l E X U (a * b) (d + e)
            (Fin.addCases x y)))
          (HomologicalComplex.singleObjXSelf (.up ℤ) (p + q) L).inv_hom_id))

end RootTensor

/-- The uniquely specified multiplication of the positive shifted line complexes.
Source: coefficient multiplicativity (blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralComplexProduct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d e : ℕ) :=
  (sfOrientationIntegralComplexProduct_existsUnique l E X d e).exists.choose

private theorem isIso_map_comp_of_isIso_maps
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B C' : C} (f : A ⟶ B) (g : B ⟶ C')
    (hf : IsIso (F.map f)) (hg : IsIso (F.map g)) : IsIso (F.map (f ≫ g)) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso' hf hg

/-- Completion of the ordinary tensor of two shifted root lines changes no object.
The actual operation unit, including its zero shifted-product component, is retained.
Source: completed tensor in the coefficient conventions
(blueprint: def-sf-orientation-integral-line-comparisons).
Proof: ordinary multiplication identifies the total tensor with the single line
in degree -2(d+e). Intrinsic twist membership, shift stability and isomorphism
stability make this object derived complete. Convert to the legacy completeness
predicate, using an auxiliary prime distinct from l. The normalized Roos criterion
makes its specified completion unit invertible. The representative normalization
then makes Q(roosUnit) invertible. The tensor operation unit is roosUnit followed
by the Roos image of tensorTowerIso, so its localization is invertible. -/
theorem sfOrientationIntegralTensorUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (d e : ℕ) :
    IsIso (DerivedCategory.Q.map (IntegralAmbient.tensorOperationUnit l E X
      (sfOrientationIntegralComplex l E X d) (sfOrientationIntegralComplex l E X e))) := by
  let P := sfOrientationIntegralComplex l E X d
  let Q := sfOrientationIntegralComplex l E X e
  let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X)).obj (P, Q)
  have hT : IntegralOnSlice.Good l E X none T :=
    IntegralAmbient.tensor_good.{u, u} l E X P Q
      (sfOrientationIntegralComplex_good l E X d)
      (sfOrientationIntegralComplex_good l E X e)
  let es : DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X (d + e)) ≅
      (sfIntegralTwistingObject l E X ((d + e : ℕ) : ℤ))⟦2 * ((d + e : ℕ) : ℤ)⟧ :=
    ((DerivedCategory.singleFunctors _).shiftIso (2 * ((d + e : ℕ) : ℤ))
      (-2 * ((d + e : ℕ) : ℤ)) 0 (by omega)).symm.app
        (FrobeniusCoefficientTwists.positiveLine l E X (d + e))
  have hline := (sfIntegralConstructible l E X).le_shift
    (2 * ((d + e : ℕ) : ℤ)) _ (sfIntegralTwistingObject_mem l E X (d + e : ℕ))
  have hc : IsSfDerivedComplete l E X (DerivedCategory.Q.obj T) :=
    ((sfIntegralConstructible l E X).prop_of_iso
      ((DerivedCategory.Q.mapIso (sfOrientationIntegralComplexProduct l E X d e)) ≪≫
        es).symm hline).1
  obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := Nat.ne_of_lt (Nat.lt_of_succ_le hlp)
  have hcomplete :
      IntegralOnSlice.IsComplete l E X none (DerivedCategory.Q.obj T) :=
    ⟨D, hl, (sfDerivedComplete_iff_legacy l E X D hl _).mp hc⟩
  obtain ⟨datum, hdatum, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  let TG : (IntegralOnSlice.Good l E X none).FullSubcategory := ⟨T, hT⟩
  have hu : IsIso ((IntegralOnSlice.completionUnit l E X none).app
      (DerivedCategory.Q.obj T)) :=
    ((roosIntrinsicCompletenessEquivalence p l (by omega) E X datum hdatum
      (DerivedCategory.Q.obj T) TG (Iso.refl _)).out 0 4).mp hcomplete
  have hn : (IntegralOnSlice.completionUnit l E X none).app
      (DerivedCategory.Q.obj T) ≫
        (IntegralOnSlice.completionComparison l E X none).hom.app TG =
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none T) := by
    simpa only [IntegralOnSlice.completionUnit, IntegralOnSlice.qGood,
      Functor.comp_obj, ObjectProperty.ι_obj] using
      (IntegralOnSlice.completionUnit_existsUnique l E X none).exists.choose_spec TG
  have hr : IsIso (DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none T)) :=
    hn ▸ IsIso.comp_isIso' hu
      (NatIso.hom_app_isIso (IntegralOnSlice.completionComparison l E X none) TG)
  have hmap : IsIso (DerivedCategory.Q.map
      (integralOperationsRoosFunctor.map
        ((IntegralAmbient.tensorTowerIso l E X).hom.app (P, Q)))) :=
    (DerivedCategory.Q.mapIso
      (integralOperationsRoosFunctor.mapIso
        ((IntegralAmbient.tensorTowerIso l E X).app (P, Q)))).isIso_hom
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact isIso_map_comp_of_isIso_maps
    (DerivedCategory.Q (C := integralTowerModules l E X))
    (IntegralOnSlice.roosUnit l E X none T)
    (integralOperationsRoosFunctor.map
      ((IntegralAmbient.tensorTowerIso l E X).hom.app (P, Q))) hr hmap

/-- Actual multiplication of completed derived root lines, calculated by the
specified good representatives and the specified tensor-operation augmentation.
Source: completed tensor and Tate multiplication
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralDerivedProduct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (d e : ℕ) :
    (integralCompletedTensor l E X).obj
      (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d),
        DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X e)) ≅
      DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X (d + e)) :=
  (integralCompletedTensorComparison l E X).app
    (⟨sfOrientationIntegralComplex l E X d, sfOrientationIntegralComplex_good l E X d⟩,
      ⟨sfOrientationIntegralComplex l E X e, sfOrientationIntegralComplex_good l E X e⟩) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (IntegralAmbient.tensorOperationUnit l E X
      (sfOrientationIntegralComplex l E X d) (sfOrientationIntegralComplex l E X e)))
        (sfOrientationIntegralTensorUnit_isIso l E X d e)).symm ≪≫
    DerivedCategory.Q.mapIso (sfOrientationIntegralComplexProduct l E X d e)

/-- The specified pullback augmentation is invertible on each shifted root line.
Source: completed pullback in the coefficient conventions
(blueprint: def-sf-orientation-integral-line-comparisons).
Proof: the ambient ordinary pullback is the shifted root line on the source,
by the scalar/root comparison and the termwise adjoint comparison. Intrinsic
constructibility, shift stability and isomorphism stability make it derived
complete. The legacy comparison and the normalized Roos criterion make its
specified completion unit invertible. The representative normalization then
makes Q(roosUnit) invertible. The ambient operation unit is this map followed
by the Roos image of the tower comparison. Finally the generic normalized
augmentation identity compares the published augmentation with this ambient
unit, including its zero shifted-product component. -/
theorem sfOrientationIntegralPullUnit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    IsIso (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation l E g).app
        (sfOrientationIntegralComplex l E Y d))) := by
  let : (show integralTowerModules l E Y ⥤ integralTowerModules l E X from
      FrobeniusCoefficientTwists.modulePull l E g).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (show integralTowerModules l E Y ⥤ integralTowerModules l E X from
        FrobeniusCoefficientTwists.modulePull l E g)
      (proEtaleRingModulePullback_additive g
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull g))
  let : (IntegralAmbient.pull l E g).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (IntegralAmbient.pull l E g) (IntegralAmbient.pull_additive l E g)
  obtain ⟨b, hb⟩ := integralPullbackAugmentation_ambient l E g
  let P := sfOrientationIntegralComplex l E Y d
  let M := (IntegralAmbient.pullComplex l E g).obj P
  have hM : IntegralOnSlice.Good l E X none M :=
    IntegralAmbient.pull_good l E g P (sfOrientationIntegralComplex_good l E Y d)
  let eM : M ≅ sfOrientationIntegralComplex l E X d :=
    ((NatIso.mapHomologicalComplex b (.up ℤ)).app P).symm ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (FrobeniusCoefficientTwists.modulePull l E g) (.up ℤ) (-2 * (d : ℤ))).app
        (FrobeniusCoefficientTwists.positiveLine l E Y d)) ≪≫
      ((HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).mapIso
        (sfOrientationIntegralLineMaps l E g d))
  let es : DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d) ≅
      (sfIntegralTwistingObject l E X (d : ℤ))⟦2 * (d : ℤ)⟧ :=
    ((DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ))
      (-2 * (d : ℤ)) 0 (by omega)).symm.app
        (FrobeniusCoefficientTwists.positiveLine l E X d)
  have hline := (sfIntegralConstructible l E X).le_shift
    (2 * (d : ℤ)) _ (sfIntegralTwistingObject_mem l E X (d : ℕ))
  have hc : IsSfDerivedComplete l E X (DerivedCategory.Q.obj M) :=
    ((sfIntegralConstructible l E X).prop_of_iso
      ((DerivedCategory.Q.mapIso eM) ≪≫ es).symm hline).1
  obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := Nat.ne_of_lt (Nat.lt_of_succ_le hlp)
  have hcomplete : IntegralOnSlice.IsComplete l E X none (DerivedCategory.Q.obj M) :=
    ⟨D, hl, (sfDerivedComplete_iff_legacy l E X D hl _).mp hc⟩
  obtain ⟨datum, hdatum, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  let MG : (IntegralOnSlice.Good l E X none).FullSubcategory := ⟨M, hM⟩
  have hu : IsIso ((IntegralOnSlice.completionUnit l E X none).app
      (DerivedCategory.Q.obj M)) :=
    ((roosIntrinsicCompletenessEquivalence p l (by omega) E X datum hdatum
      (DerivedCategory.Q.obj M) MG (Iso.refl _)).out 0 4).mp hcomplete
  have hn : (IntegralOnSlice.completionUnit l E X none).app
      (DerivedCategory.Q.obj M) ≫
        (IntegralOnSlice.completionComparison l E X none).hom.app MG =
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none M) := by
    simpa only [IntegralOnSlice.completionUnit, IntegralOnSlice.qGood,
      Functor.comp_obj, ObjectProperty.ι_obj] using
      (IntegralOnSlice.completionUnit_existsUnique l E X none).exists.choose_spec MG
  have hr : IsIso (DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none M)) :=
    hn ▸ IsIso.comp_isIso' hu
      (NatIso.hom_app_isIso (IntegralOnSlice.completionComparison l E X none) MG)
  have hmap : IsIso (DerivedCategory.Q.map
      (integralOperationsRoosFunctor.map ((IntegralAmbient.pullTowerIso l E g).hom.app P))) :=
    (DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso
      ((IntegralAmbient.pullTowerIso l E g).app P))).isIso_hom
  have ha : IsIso (DerivedCategory.Q.map (IntegralAmbient.pullOperationUnit l E g P)) := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    exact isIso_map_comp_of_isIso_maps
      (DerivedCategory.Q (C := integralTowerModules l E X))
      (IntegralOnSlice.roosUnit l E X none M)
      (integralOperationsRoosFunctor.map ((IntegralAmbient.pullTowerIso l E g).hom.app P))
      hr hmap
  have hi : IsIso (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P)) :=
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex b (.up ℤ)).app P)).isIso_hom
  rw [hb P]
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact isIso_map_comp_of_isIso_maps
    (DerivedCategory.Q (C := integralTowerModules l E X))
    ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P)
    (IntegralAmbient.pullOperationUnit l E g P) hi ha

/-- The actual completed derived pullback comparison for the shifted root line.
Source: coefficient conventions, arbitrary scheme pullback
(blueprint: def-sf-orientation-integral-line-comparisons). -/
def sfOrientationIntegralDerivedPull
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :
    (integralDerivedPullback l E g).obj
        (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E Y d)) ≅
      DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d) :=
  (integralDerivedPullbackComparison l E g).app
      ⟨sfOrientationIntegralComplex l E Y d, sfOrientationIntegralComplex_good l E Y d⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation l E g).app
        (sfOrientationIntegralComplex l E Y d)))
        (sfOrientationIntegralPullUnit_isIso l E g d)).symm ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (FrobeniusCoefficientTwists.modulePull l E g) (.up ℤ) (-2 * (d : ℤ))).app
        (FrobeniusCoefficientTwists.positiveLine l E Y d)) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).mapIso
        (sfOrientationIntegralLineMaps l E g d))

end WeilConjectures
