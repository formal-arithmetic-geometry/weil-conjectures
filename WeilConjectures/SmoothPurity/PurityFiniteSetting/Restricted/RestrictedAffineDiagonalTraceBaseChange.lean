/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.RestrictedAffineDiagonalSectionTrace
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineCounitMateUnitChange
import WeilConjectures.AlgebraicGeometry.Section.SectionCoordinateCounitNormalization
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartCoefficientCore
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateSectionPullback
import all WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateExactOpenComposition
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Trace base change on the restricted affine diagonal

Source: smooth-purity, Agreement on the model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
open AlgebraicGeometry.Etale (purityTwistTransport)
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Etale.affineLinearCompactComparison
  Etale.affineLinearCoefficientDescent Etale.vectorIntegrationBaseCoefficientPullback

private theorem cancel_comparison
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {K L M : C} {Z : D} (a : Z ≅ F.obj L) (m : K ⟶ L) (b : L ⟶ M) :
    (F.map m ≫ a.inv) ≫ (a.hom ≫ F.map b) = F.map (m ≫ b) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp]

private theorem coefficient_square (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    {X X' Y Y' : Scheme.{u}} (p : X ⟶ Y) (p' : X' ⟶ Y')
    (v : X' ⟶ X) (b : Y' ⟶ Y) (sq : CommSq v p' p b)
    (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤)))
    (hX : IsUnit (P.diagonalExponent : Γ(X, ⊤)))
    (hY' : IsUnit (P.diagonalExponent : Γ(Y', ⊤))) (d : ℕ) :
    (Etale.ordinaryFinitePullback P.Coefficient v).mapIso
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t p hY d) ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t v hX d =
      (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} P.Coefficient) sq).symm.app _ ≪≫
        (Etale.ordinaryFinitePullback P.Coefficient p').mapIso
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t b hY d) ≪≫
        Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t p' hY' d := by
  apply Iso.ext
  apply (cancel_epi ((Etale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) v p).hom.app _)).mp
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Etale.derivedSquareUpperStarIso, Iso.symm_hom, Iso.trans_inv,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (Etale.coefficient_comp P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t v p (v ≫ p) rfl hY hX d).trans
      (Etale.coefficient_comp P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t p' b (v ≫ p) sq.w hY hY' d).symm

private def affine_monoidal_mate (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤))) (d : ℕ) :
    Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates (affineTraceTower Y d) d ⟶
      Etale.dualizingComplex P.Coefficient
        (affineTraceProjection Y d) :=
  P.diagonalAffineMate t D Y hY d ≫
    (OrientationCounit.unitChange P (affineTraceProjection Y d)).inv

private theorem normalized_comp_map
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (c : H ≅ F ⋙ G)
    {K M : C} {KU : D} {KT : E}
    (v : F.obj K ≅ KU) (p : G.obj KU ≅ KT) (w : H.obj K ≅ KT)
    (hw : c.hom.app K ≫ G.map v.hom ≫ p.hom = w.hom) (m : K ⟶ M) :
    p.inv ≫ G.map (v.inv ≫ F.map m) =
      w.inv ≫ H.map m ≫ c.hom.app M := by
  apply (cancel_epi w.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← hw]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← G.map_comp_assoc, v.hom_inv_id, G.map_id, Category.id_comp]
  exact (c.hom.naturality m).symm

private theorem section_coefficient_cancel
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (c : F ⋙ G ≅ 𝟭 C)
    {K M : C} {KT L : D} (v : F.obj K ≅ KT) (p : G.obj KT ≅ K)
    (b : F.obj M ≅ L)
    (hs : p.inv ≫ G.map v.inv ≫ c.hom.app K = 𝟙 K) (m : K ⟶ M) :
    (p.inv ≫ G.map (v.inv ≫ F.map m ≫ b.hom)) ≫
      G.map b.inv ≫ c.hom.app M = m := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc b.hom b.inv, b.hom_inv_id, G.map_id, Category.id_comp]
  have hn := c.hom.naturality m
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun k ↦ k ≫ m) hs

private theorem normalized_map_comp (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) (w : T ⟶ S)
    (hw : w = p ≫ v) (aS : S ⟶ Spec (.of P.field.k))
    (aU : U ⟶ Spec (.of P.field.k)) (d : ℕ)
    (M : Etale.DerivedCategoryModule P.Coefficient S)
    (m : P.diagonalTwistEtale S d ⟶ M) :
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t p (P.diagonalExponent_isUnit aU) d).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient p).map
        ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t v (P.diagonalExponent_isUnit aS) d).inv ≫
            (Etale.ordinaryFinitePullback P.Coefficient v).map m) =
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t w (P.diagonalExponent_isUnit aS) d).inv ≫
        (Etale.ordinaryFinitePullback P.Coefficient w).map m ≫
        (Etale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) p v w hw).hom.app M := by
  exact normalized_comp_map _ _ _ _ _ _ _
    (Etale.coefficient_comp P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t p v w hw
        (P.diagonalExponent_isUnit aS) (P.diagonalExponent_isUnit aU) d) m

private theorem affine_monoidal_mate_baseChange (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    {T S : Scheme.{u}} [IsNoetherian T] [IsNoetherian S]
    (f : T ⟶ S) (hS : IsUnit (P.diagonalExponent : Γ(S, ⊤)))
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (d : ℕ) :
    (Etale.ordinaryFinitePullback P.Coefficient (affineTraceMap f d)).map
        (affine_monoidal_mate P t D S hS d) ≫
      Etale.dualizingComplexBaseChangeMap P.Coefficient (affineTraceMap_isPullback f d) =
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t (affineTraceMap f d)
          (affineTraceInvertible P.diagonalExponent S hS d) d).hom ≫
      affine_monoidal_mate P t D T hT d := by
  let A := P.Coefficient
  let N := P.diagonalExponent
  let hA := P.diagonalExponent_annihilates
  let hN := pow_pos P.coefficients.prime.out.pos P.level
  let cS := Etale.affineLinearCoefficientDescent A N hA t S hS d ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback A N hA t
      (affineTraceProjection S d) hS d
  let cT := Etale.affineLinearCoefficientDescent A N hA t T hT d ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback A N hA t
      (affineTraceProjection T d) hT d
  let F := Etale.ordinaryFinitePullback A (affineTraceMap f d)
  let b := Etale.affineTraceRightBaseChange A N hA t f hS d
      (Etale.ordinaryFiniteUnit A S) ≪≫
    (Etale.affineTraceRight A N hA T d).mapIso (Etale.ordinaryFiniteUnitPullback A f)
  let k := Etale.vectorIntegrationBaseCoefficientPullback A N hA t
    (affineTraceMap f d) (affineTraceInvertible N S hS d) d
  have hc : F.mapIso cS ≪≫ k = b ≪≫ cT := by
    dsimp only [b, cS, cT, F, k]
    rw [Etale.affineTraceRightBaseChange_unit_coefficient A N hA t f hS hT d]
    simp only [Functor.mapIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]
    exact congrArg (fun e ↦ F.mapIso
      (Etale.affineLinearCoefficientDescent A N hA t S hS d) ≪≫ e)
        (coefficient_square P t (affineTraceProjection S d)
          (affineTraceProjection T d) (affineTraceMap f d) f
          (affineTraceMap_isPullback f d).toCommSq hS
          (affineTraceInvertible N S hS d) hT d)
  have hz := (Etale.affineCoordinateCounit_baseChange N hN A hA t D S hS d).2 T f
  change F.map (affine_monoidal_mate P t D S hS d) ≫ _ =
    k.hom ≫ affine_monoidal_mate P t D T hT d
  simp only [affine_monoidal_mate, affineCounitMate_unitChange, Functor.map_comp, Category.assoc]
  rw [hz]
  have hch := congrArg Iso.hom hc
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hch
  have hci : F.map cS.inv ≫ b.hom = k.hom ≫ cT.inv := by
    apply (cancel_epi (F.map cS.hom)).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
    rw [← Category.assoc, hch, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      F.map_id, Category.id_comp]
  simpa only [cS, cT, b, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc] using
    congrArg (fun a ↦ a ≫ Etale.CoordinateCounitArrows.towerAdjoint N hN A hA t D T hT d)
      hci

private theorem dualizing_base_comp_named
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (a : X'' ⟶ X) (b : Y'' ⟶ Y) (ha : a = w' ≫ v') (hb : b = w ≫ v)
    (sq : IsPullback a f'' f b) :
    Etale.dualizingComplexBaseChangeMap A sq =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' a ha).hom.app
        (Etale.dualizingComplex A f) ≫
      (Etale.ordinaryFinitePullback A w').map
        (Etale.dualizingComplexBaseChangeMap A sq₁) ≫
      Etale.dualizingComplexBaseChangeMap A sq₂ := by
  subst a
  subst b
  exact Etale.dualizing_base_comp A sq₁ sq₂

set_option maxHeartbeats 400000 in
-- The compositor and mate calculations need more than the default elaboration budget.
/-- Restriction of integration on the self-product is the affine counit on Y,
through the actual diagonal base-change and target-open exchange maps. There is
no DNC arrow or normal-bundle purity map in this equation.
Source: smooth-purity Agreement on the model, base-change compatibility of integration;
diagonal-dualizing-object proof Step 2 and combining paragraph.
(blueprint: lem-pur-restricted-affine-diagonal-trace-base-change).

Proof: apply affine-trace base change to B to Y. The Cartesian comparison of
towers is restrictedAffineDiagonalCoordinates: its two composites are exactly
the second point in A^d_Y and the first projection to B. The base-change formula
for the ordered counit therefore identifies the integration on the tower over B
with pullback of integration on Y. Transpose under the compact-support exceptional
adjunction. Naturality of its Hom bijection says that the transposed base-change
map is the prescribed dualizingComplexBaseChangeMap. Pull along the diagonal;
the inverse mate in alpha cancels this mate. The section pullback compositor
identifies the remaining pullback of the counit transpose with its restriction
to B. Paste the target-open square: the exchange map is precisely rho, since
both are the mates of the same compact-support exchange. The comparison from
the monoidal unit to A[0] is unitChange on both sides. Naturality cancels the
inner unit comparison, leaving the displayed final one. The normalized root
pullback and its ordered tensor powers give inverse tate on the right; inverse
image commutes with the comparison of sites. All these identities hold for any
normalized t,D by their Kummer generator and counit conditions. At rank zero
the ordered adjunction is the identity, and the same pasting applies; no point
or nonempty base is required. -/
theorem restrictedAffineDiagonalTraceBaseChange (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    [SmoothOfRelativeDimension d (affineTraceProjection Y d)]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (H : P.AffineDiagonalGeometry (affineTraceProjection Y d) aY d V)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    let ν := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (affineTraceTower Y d)).mapDerivedCategory
    OrientationCounit.restrictedAffineDiagonalSectionTrace P Y d aY V H t D ≫
        (OrientationRefinement.alpha P (affineTraceProjection Y d) aY d V H).hom ≫
        (OrientationRefinement.rho P (affineTraceProjection Y d) aY d V H).inv ≫
        ((OrientationRefinement.pull P (affineTraceProjection Y d ⁻¹ᵁ V.1).ι).mapIso
          (ν.mapIso (OrientationCounit.unitChange P (affineTraceProjection Y d)))).hom =
      (OrientationRefinement.tate P (affineTraceProjection Y d ⁻¹ᵁ V.1).ι
        (affineTraceProjection Y d ≫ aY) d).inv ≫
        (OrientationRefinement.pull P (affineTraceProjection Y d ⁻¹ᵁ V.1).ι).map
          (ν.map (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d)) := by
  let := H.separated
  let := H.finiteType
  let := H.quasiCompact
  let := H.smoothDimension
  let := H.baseFiniteType
  let := H.baseQuasiCompact
  let := H.sourceSeparated
  let := H.sourceFiniteType
  let := H.sourceQuasiCompact
  let p := affineTraceProjection Y d
  let h := p ∣_ V.1
  let B := (p ⁻¹ᵁ V.1).toScheme
  let aB := h ≫ V.1.ι ≫ aY
  let := P.noetherian aB
  let := SmoothOfRelativeDimension.smooth d h
  let g := pullback.fst h h
  let s := pullback.diagonal h
  let e := OrientationCounit.restrictedAffineDiagonalCoordinates Y d V.1
  let q := affineTraceProjection B d
  let := Dnc.compactifiable P q aB
  let := Dnc.compactifiable P h (V.1.ι ≫ aY)
  let := Dnc.compactifiable P g aB
  let r := s ≫ e.hom
  have he : e.hom ≫ q = g :=
    OrientationCounit.restrictedAffineDiagonalCoordinates_over Y d V.1
  let sq : IsPullback e.hom g q (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id g).symm⟩
  let : SmoothOfRelativeDimension d q :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension d) e.hom q).1 (by rw [he]; infer_instance)
  let := Dnc.invertibleExponent P (q ≫ aB)
  let := (P.comparedDiagonalBaseChange d h aB (V.1.ι ≫ aY) rfl).2.2.2.1
  let c := Dnc.sectionBaseChange P.Coefficient d q sq r s
    (Category.id_comp r).symm
  let mB := affine_monoidal_mate P t D B (P.diagonalExponent_isUnit aB) d
  let mY := affine_monoidal_mate P t D Y (P.diagonalExponent_isUnit aY) d
  let τr := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t r (P.diagonalExponent_isUnit (q ≫ aB)) d
  let j := (p ⁻¹ᵁ V.1).ι
  let τj := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (p ≫ aY)) d
  let n := τr.inv ≫ (Etale.ordinaryFinitePullback P.Coefficient r).map mB ≫
    (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).inv.app _ ≫ c.hom
  let bo := Etale.dualizingComplexBaseChangeMap P.Coefficient
    (isPullback_morphismRestrict p V.1).flip
  let bd := Etale.dualizingComplexBaseChangeMap P.Coefficient
    (IsPullback.of_hasPullback h h).flip
  have hordinary : n ≫ (P.diagonalComparedRestriction h (asIso bd)).hom =
      τj.inv ≫ (Etale.ordinaryFinitePullback P.Coefficient j).map mY ≫ bo := by
    let F := fun {T S : Scheme.{u}} (v : T ⟶ S) ↦
      Etale.ordinaryFinitePullback P.Coefficient v
    let τ := fun {T S : Scheme.{u}} (v : T ⟶ S) (aS : S ⟶ Spec (.of P.field.k)) ↦
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t v (P.diagonalExponent_isUnit aS) d
    let b := h ≫ V.1.ι
    let a := affineTraceMap b d
    let v := pullback.snd h h
    let z := v ≫ j
    let E := Etale.dualizingComplexBaseChangeMap P.Coefficient sq
    let C := Etale.dualizingComplexBaseChangeMap P.Coefficient
      (affineTraceMap_isPullback b d)
    let J := (τ e.hom (q ≫ aB)).inv ≫ (F e.hom).map mB ≫ E
    have hetop : e.hom ≫ a = z :=
      IsPullback.isoIsPullback_hom_fst _ _ _ _
    let c₁ := Etale.leftDerivedUpperStarComp
      (ModuleCat.{u + 1} P.Coefficient) e.hom a z hetop.symm
    let c₂ := Etale.leftDerivedUpperStarComp
      (ModuleCat.{u + 1} P.Coefficient) v j
    -- Both pastings are the counit-defined mate for the same outer square.
    have hx : c₁.hom.app _ ≫ (F e.hom).map C ≫ E =
        c₂.hom.app _ ≫ (F v).map bo ≫ bd := by
      let := affineTraceNoetherian Y d
      let := affineTraceNoetherian B d
      let := P.noetherian (g ≫ aB)
      let := P.noetherian (V.1.ι ≫ aY)
      let outer := (IsPullback.of_hasPullback h h).flip.paste_horiz
        (isPullback_morphismRestrict p V.1).flip
      have h₁ := dualizing_base_comp_named P.Coefficient
        (affineTraceMap_isPullback b d) sq z b hetop.symm
        (Category.id_comp b).symm outer
      have h₂ := dualizing_base_comp_named P.Coefficient
        (isPullback_morphismRestrict p V.1).flip
        (IsPullback.of_hasPullback h h).flip z b rfl rfl outer
      exact h₁.symm.trans h₂
    have hmb : mB = (τ a (p ≫ aY)).inv ≫ (F a).map mY ≫ C := by
      apply (cancel_epi (τ a (p ≫ aY)).hom).mp
      simp only [Iso.hom_inv_id_assoc]
      exact (affine_monoidal_mate_baseChange P t D b (P.diagonalExponent_isUnit aY)
        (P.diagonalExponent_isUnit aB) d).symm
    let Mh := τj.inv ≫ (F j).map mY ≫ bo
    have hJ : J = (τ v aB).inv ≫ (F v).map Mh ≫ bd := by
      calc
        J = ((τ e.hom (q ≫ aB)).inv ≫
            (F e.hom).map ((τ a (p ≫ aY)).inv ≫ (F a).map mY)) ≫
              (F e.hom).map C ≫ E := by
                simp only [J, hmb, Functor.map_comp, Category.assoc]
        _ = (τ z (p ≫ aY)).inv ≫ (F z).map mY ≫
            (c₁.hom.app _ ≫ (F e.hom).map C ≫ E) := by
              rw [normalized_map_comp P t e.hom a z hetop.symm (p ≫ aY) (q ≫ aB)]
              simp only [τ, F, c₁, Category.assoc]
        _ = (τ z (p ≫ aY)).inv ≫ (F z).map mY ≫
            (c₂.hom.app _ ≫ (F v).map bo ≫ bd) := by rw [hx]
        _ = _ := by
          simpa only [Mh, τ, F, c₂, Functor.map_comp, Category.assoc] using
            congrArg (fun k ↦ k ≫ (F v).map bo ≫ bd)
              (normalized_map_comp P t v j z rfl (p ≫ aY) aB d _ mY).symm
    -- Remove the identity-base compositor before restricting to the section.
    have hn : n = (τ s (g ≫ aB)).inv ≫ (F s).map J := by
      let I := Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B
      let cId := Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) (𝟙 B) r r (Category.id_comp r).symm
      have hu : I.inv.app _ ≫ cId.inv.app _ = 𝟙 ((F r).obj
          (Etale.dualizingComplex P.Coefficient q)) := by
        let M := Etale.dualizingComplex P.Coefficient q
        have hunit : cId.app M ≪≫ I.app ((F r).obj M) = Iso.refl _ :=
          Iso.ext (Etale.leftDerivedUpperStarComp_id_left_hom_app
            (ModuleCat.{u + 1} P.Coefficient) r M)
        exact congrArg Iso.inv hunit
      let M := Etale.dualizingComplex P.Coefficient q
      have hc : I.inv.app ((F r).obj M) ≫ c.hom =
          (Etale.leftDerivedUpperStarComp
            (ModuleCat.{u + 1} P.Coefficient) s e.hom r rfl).hom.app M ≫
              (F s).map E := by
        have hep := Etale.sectionPullback_endpoint
          P.Coefficient (𝟙 B) r s e.hom
          (𝟙 B ≫ r) r rfl (Category.id_comp r) (Category.id_comp r).symm rfl M
        have heph := congrArg Iso.hom hep
        simp only [Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
          at heph
        dsimp only [c, Dnc.sectionBaseChange]
        simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
          Functor.mapIso_hom, asIso_hom]
        rw [reassoc_of% heph]
        let tail := (Etale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) s e.hom r rfl).hom.app M ≫
            (F s).map E
        have hh := (congrArg (fun k ↦ k ≫ tail) hu).trans (Category.id_comp tail)
        simpa only [I, cId, F, M, E, tail, Etale.ordinaryFinitePullback,
          Category.assoc] using hh
      change τr.inv ≫ (F r).map mB ≫ (I.inv.app _ ≫ c.hom) = _
      rw [hc]
      simpa only [J, τ, F, Functor.map_comp, Category.assoc] using
        congrArg (fun k ↦ k ≫ (F s).map E)
          (normalized_map_comp P t s e.hom r rfl (q ≫ aB) (g ≫ aB) d M mB).symm
    -- The inverse diagonal mate cancels; Tate section coherence removes the remainder.
    rw [hn, hJ]
    have hsection := Etale.orderedTateSectionPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t v s (pullback.diagonal_snd h)
      (P.diagonalExponent_isUnit aB) (P.diagonalExponent_isUnit (g ≫ aB)) d
    exact section_coefficient_cancel (F v) (F s)
      (Etale.leftDerivedUpperStarCompSectionIso
        (ModuleCat.{u + 1} P.Coefficient) s v (pullback.diagonal_snd h))
      (τ v aB) (τ s (g ≫ aB)) (asIso bd) hsection Mh
  let νB := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let νX := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) (affineTraceTower Y d)).mapDerivedCategory
  let L := OrientationRefinement.pull P j
  -- Read the two sides through the same ordinary-etale comparison.
  have hleft : OrientationCounit.restrictedAffineDiagonalSectionTrace P Y d aY V H t D ≫
      (OrientationRefinement.alpha P p aY d V H).hom =
      νB.map (n ≫ (P.diagonalComparedRestriction h (asIso bd)).hom) := by
    unfold OrientationCounit.restrictedAffineDiagonalSectionTrace
      OrientationRefinement.alpha affineDiagonalAlpha
    exact cancel_comparison νB (Dnc.sourceComparison P d g aB s) n
      (P.diagonalComparedRestriction h (asIso bd)).hom
  have hright :
      (OrientationRefinement.tate P j (p ≫ aY) d).inv ≫
        L.map (νX.map mY) ≫ (OrientationRefinement.rho P p aY d V H).hom =
      νB.map (τj.inv ≫ (Etale.ordinaryFinitePullback P.Coefficient j).map mY ≫ bo) := by
    have ht := Etale.ordinaryFiniteTwistTransport_unique P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates
      (purityTwistTransport P.Coefficient P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates) t
    have hn := (OrientationCounit.comparisonPull P j).hom.naturality mY
    unfold OrientationCounit.comparisonPull at hn
    change L.map (νX.map mY) ≫ (Dnc.pullComparison P j _).hom =
      (Dnc.pullComparison P j _).hom ≫
        νB.map ((Etale.ordinaryFinitePullback P.Coefficient j).map mY) at hn
    unfold OrientationRefinement.tate OrientationRefinement.rho affineDiagonalRho
    rw [ht]
    simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    change νB.map τj.inv ≫ (Dnc.pullComparison P j _).inv ≫
      L.map (νX.map mY) ≫ (Dnc.pullComparison P j _).hom ≫ νB.map bo = _
    rw [reassoc_of% hn]
    simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp]
  have hS := hleft.trans ((congrArg νB.map hordinary).trans hright.symm)
  simp only [Functor.mapIso_hom]
  rw [← Category.assoc (OrientationCounit.restrictedAffineDiagonalSectionTrace
    P Y d aY V H t D)]
  change (OrientationCounit.restrictedAffineDiagonalSectionTrace P Y d aY V H t D ≫
    (OrientationRefinement.alpha P p aY d V H).hom) ≫
    (OrientationRefinement.rho P p aY d V H).inv ≫
    L.map (νX.map (OrientationCounit.unitChange P p).hom) = _
  rw [hS]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [mY, affine_monoidal_mate, Category.assoc,
    ← Functor.map_comp]
  change (OrientationRefinement.tate P j (p ≫ aY) d).inv ≫
    L.map (νX.map (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d ≫
      (OrientationCounit.unitChange P p).inv ≫
        (OrientationCounit.unitChange P p).hom)) = _
  rw [Iso.inv_hom_id, Category.comp_id]

end WeilConjectures.PurityFiniteSetting
