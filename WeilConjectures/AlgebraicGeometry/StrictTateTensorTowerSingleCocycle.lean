/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTateTensorTowerLiftPre
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
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
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import WeilConjectures.CategoryTheory.DerivedCategory.ExactFaithfulSingleMorphisms

/-! Cocycle coherence for the strict ordinary Tate quotient pre-tower.
(blueprint: lem-pur-strict-tate-single-pre-cocycle)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem restrict_faithful
    {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (f : R ⟶ S) : (pbcRestrict f).Faithful where
  map_injective h := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

private theorem restrictComp_apply
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp a b c h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists a b c h).exists.choose_spec M U x

private theorem restriction_assoc
    {T : Scheme.{u}} {R S B V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ V)
    (ab : R ⟶ B) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : ab ≫ c = abc) (habc' : a ≫ bc = abc) :
    Functor.isoWhiskerLeft (pbcDerivedRestrict c) (pbcDerivedRestrictComp a b ab hab) ≪≫
        pbcDerivedRestrictComp ab c abc habc =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pbcDerivedRestrictComp b c bc hbc) (pbcDerivedRestrict a) ≪≫
        pbcDerivedRestrictComp a bc abc habc' := by
  apply SheafOfModules.SuccessiveDerivedQuotient.exactComp_assoc
  apply Iso.ext
  ext M U x
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  change ((pbcRestrictComp ab c abc habc).hom.app M).val.app U
      (((pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M)).val.app U x) =
    ((pbcRestrictComp a bc abc habc').hom.app M).val.app U
      (((pbcRestrictComp b c bc hbc).hom.app M).val.app U x)
  simp only [restrictComp_apply]

private theorem tower_comp (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    pbcTowerTransition T R c a (hab.trans hbc) =
      pbcTowerTransition T R c b hbc ≫ pbcTowerTransition T R b a hab := by
  unfold pbcTowerTransition
  rw [Localization.comp_liftNatTrans]
  congr 1
  rw [← Functor.whiskerRight_comp, ← NatTrans.mapHomologicalComplex_comp,
    ← Functor.map_comp]
  rfl

/-- The transitions of a pre-tower whose levels are single complexes in one
common degree satisfy the AdicTower cocycle, including equal indices.

Source: smooth-purity transport, normalized Tate tower, Step 3. The pre-tower
transition equations identify the completed-coefficient restrictions with the
strict tower transitions. The canonical restriction comparisons are associative:
they are identity maps on underlying sections, and exact derivation preserves
this coherence. Naturality and the strict tower composition law therefore show
that the restrictions of the two cocycle composites agree. Restriction of
scalars is faithful on ordinary sheaves, hence on derived morphisms between
objects in the same single degree. The supplied single-complex identifications
allow this faithfulness to conclude the desired equality. No strict inequality
is used, so all equal-index cases are included.

This statement uses the single-degree comparisons already supplied by the
strict Tate pre-tower construction; it makes no assertion about unrestricted
derived pre-towers.
(blueprint: lem-pur-strict-tate-single-pre-cocycle)
-/
theorem strictTateTensorTower_single_pre_cocycle
    (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (P : StrictTateTensorTowerPre T d)
    (k : ℤ)
    (L : ∀ n : ℕ, pbcModules T ((pbcAdicRings T d).obj (op n)))
    (q : ∀ n : ℕ, P.level n ≅ (DerivedCategory.singleFunctor _ k).obj (L n)) :
    P.Cocycle := by
  intro c b a hab hbc
  let p (n : ℕ) := pbcAdicProjection T d n
  let r (m n : ℕ) (h : n ≤ m) := pbcAdicQuotient T d m n h
  let v (m n : ℕ) (h : n ≤ m) :=
    adicTowerSemilinearTransition T d P.level P.normalization m n h
  let e (m n : ℕ) (h : n ≤ m) := pbcDerivedRestrictComp (p m) (r m n h) (p n)
    (pbcAdicProjection_comp T d m n h)
  let eca := pbcDerivedRestrictComp (r c b hbc) (r b a hab) (r c a (hab.trans hbc))
    (pbcAdicQuotient_comp T d c b a hab hbc)
  have hs := congrArg (fun i ↦ i.hom.app (P.level a))
    (restriction_assoc (p c) (r c b hbc) (r b a hab) (p b)
      (r c a (hab.trans hbc)) (p a)
      (pbcAdicProjection_comp T d c b hbc) (pbcAdicQuotient_comp T d c b a hab hbc)
      (pbcAdicProjection_comp T d b a hab) (pbcAdicProjection_comp T d c a (hab.trans hbc)))
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at hs
  have hn := (e c b hbc).hom.naturality (v b a hab)
  dsimp only [Functor.comp_map] at hn
  let : (pbcRestrict (p c)).Faithful := restrict_faithful (p c)
  apply Functor.mapDerivedCategory_injective_of_single (pbcRestrict (p c)) k (L c)
    ((pbcRestrict (r c a (hab.trans hbc))).obj (L a)) (q c)
    ((pbcDerivedRestrict (r c a (hab.trans hbc))).mapIso (q a) ≪≫
      (Functor.mapDerivedCategorySingleFunctor (pbcRestrict (r c a (hab.trans hbc))) k).app
        (L a))
  apply (cancel_mono ((e c a (hab.trans hbc)).hom.app (P.level a) ≫
    (P.evaluation a).hom)).mp
  change (pbcDerivedRestrict (p c)).map (v c a (hab.trans hbc)) ≫ _ =
    (pbcDerivedRestrict (p c)).map
      (v c b hbc ≫ (pbcDerivedRestrict (r c b hbc)).map (v b a hab) ≫
        eca.hom.app (P.level a)) ≫ _
  rw [P.transition c a (hab.trans hbc)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hs, reassoc_of% hn, P.transition b a hab]
  rw [reassoc_of% (P.transition c b hbc)]
  rw [← NatTrans.comp_app, ← tower_comp T (pbcAdicCompletion T d) c b a hab hbc]

end AlgebraicGeometry.Scheme.PurityIntegralTower
