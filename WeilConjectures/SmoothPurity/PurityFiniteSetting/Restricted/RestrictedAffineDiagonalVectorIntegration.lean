/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Restricted.RestrictedAffineDiagonalDncVectorCoordinates
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.RestrictedAffineDiagonalSectionTrace
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineVectorTracePresentation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineCounitMateUnitChange
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTatePullbackSquare
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateCoefficientComposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.SmoothSectionExchangeComposition
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
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Integration in a vector presentation of the restricted diagonal

Source: smooth-purity, Agreement on the model.
(blueprint: lem-pur-restricted-affine-diagonal-vector-integration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
open AlgebraicGeometry.Etale (purityTwistTransport)
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Scheme.Modules Etale.dualizingComplex

private theorem integration_mate_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (ex : L ⋙ H ≅ G ⋙ L') {W : C} {W' : C'} {U : D} {U' : D'}
    (a : G.obj W ⟶ W') (t : L.obj W ⟶ U) (t' : L'.obj W' ⟶ U')
    (c : H.obj U ⟶ U')
    (ht : ex.hom.app W ≫ L'.map a ≫ t' = H.map t ≫ c) :
    G.map (adj.homEquiv W U t) ≫ (mateEquiv adj adj' ex.inv).app U ≫ R'.map c =
      a ≫ adj'.homEquiv W' U' t' := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := adj'.counit.naturality c
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  have ht' : L'.map (adj'.homEquiv W' U' t') ≫ adj'.counit.app U' = t' := by
    simpa only [Adjunction.homEquiv_counit] using
      (adj'.homEquiv W' U').symm_apply_apply t'
  rw [ht']
  rw [reassoc_of% (mateEquiv_counit adj adj' ex.inv U)]
  have he := ex.inv.naturality (adj.homEquiv W U t)
  dsimp only [Functor.comp_map] at he
  rw [reassoc_of% he]
  rw [← H.map_comp_assoc]
  rw [← adj.homEquiv_counit, Equiv.symm_apply_apply]
  have h := congrArg (fun k ↦ ex.inv.app W ≫ k) ht
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using h.symm

private theorem restrict_orientation_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (H : D ⥤ D') (G : C ⥤ C') (S : C ⥤ D) (S' : C' ⥤ D')
    (e : S ⋙ H ≅ G ⋙ S') {W V : C} {W' V' : C'} {U : D} {U' : D'}
    (cs : S.obj W ≅ U) (cs' : S'.obj W' ≅ U') (cb : H.obj U ≅ U')
    (cv : G.obj W ⟶ W') (ev : G.obj V ⟶ V') (a : W ⟶ V) (a' : W' ⟶ V')
    (ha : G.map a ≫ ev = cv ≫ a')
    (hc : H.map cs.inv ≫ e.hom.app W ≫ S'.map cv = cb.hom ≫ cs'.inv) :
    H.map (cs.inv ≫ S.map a) ≫ e.hom.app V ≫ S'.map ev =
      cb.hom ≫ cs'.inv ≫ S'.map a' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% e.hom.naturality a]
  change H.map cs.inv ≫ e.hom.app W ≫ S'.map (G.map a) ≫ S'.map ev = _
  rw [← S'.map_comp, ha, S'.map_comp]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ S'.map a') hc

private theorem coefficient_id (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (B : Scheme.{u}) (hB : IsUnit (N : Γ(B, ⊤))) (d : ℕ) :
    Etale.vectorIntegrationBaseCoefficientPullback A N hA t (𝟙 B) hB d =
      (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).app
        (Etale.affineLinearBaseCoefficient A N hA B d) := by
  let H := Etale.ordinaryFinitePullback A (𝟙 B)
  let I := Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B
  let W := Etale.affineLinearBaseCoefficient A N hA B d
  let c := Etale.vectorIntegrationBaseCoefficientPullback A N hA t (𝟙 B) hB d
  let e := Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (𝟙 B) (𝟙 B) (𝟙 B) (Category.id_comp _).symm
  have hc := Etale.orderedTateCoefficientComposition A N hA t
    (𝟙 B) (𝟙 B) (𝟙 B) (Category.id_comp _).symm hB hB d
  have hc' : e.hom.app W ≫ H.map c.hom = 𝟙 _ := by
    apply (cancel_mono c.hom).mp
    simpa only [Category.assoc, Category.id_comp] using hc
  have hu := Etale.leftDerivedUpperStarComp_id_left_hom_app
    (ModuleCat.{u + 1} A) (𝟙 B) W
  have hm : H.map c.hom = I.hom.app (H.obj W) := by
    apply (cancel_epi (e.hom.app W)).mp
    exact hc'.trans hu.symm
  have hn := I.hom.naturality c.hom
  change H.map c.hom ≫ I.hom.app W = I.hom.app (H.obj W) ≫ c.hom at hn
  rw [hm] at hn
  apply Iso.ext
  exact ((cancel_epi (I.hom.app (H.obj W))).mp hn).symm

private theorem affine_section_presentation (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsNoetherian B]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) [SmoothOfRelativeDimension d (affineTraceProjection B d)]
    (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates
        (purityTwistTransport P.Coefficient P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates) T hT) :
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    let q := affineTraceProjection B d
    let π := VectorBundleZeroSection.π B d F
    let z := VectorBundleZeroSection.zero B d F
    letI := Dnc.compactifiable P q aB
    letI := Dnc.compactifiable P π aB
    letI := Dnc.invertibleExponent P (q ≫ aB)
    let t := purityTwistTransport P.Coefficient P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
    ∀ (e : VectorBundleZeroSection.scheme B d F ≅ affineTraceTower B d)
      (we : e.hom ≫ q = π) (r : B ⟶ affineTraceTower B d)
      (hz : z ≫ e.hom = r),
      let sq : IsPullback e.hom π q (𝟙 B) :=
        IsPullback.of_horiz_isIso ⟨we.trans (Category.comp_id _).symm⟩
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t r (P.diagonalExponent_isUnit (q ≫ aB)) d).inv ≫
        (Etale.ordinaryFinitePullback P.Coefficient r).map
          (P.diagonalAffineMate t D B (P.diagonalExponent_isUnit aB) d ≫
            (OrientationCounit.unitChange P q).inv) ≫
        (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).inv.app _ ≫
        (Dnc.sectionBaseChange P.Coefficient d q sq r z
          (hz.trans (Category.id_comp r).symm)).hom =
      OrientationRefinement.vectorBetaInverse P B aB d F := by
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let q := affineTraceProjection B d
  let π := VectorBundleZeroSection.π B d F
  let z := VectorBundleZeroSection.zero B d F
  let := Dnc.compactifiable P q aB
  let := Dnc.compactifiable P π aB
  let := Dnc.invertibleExponent P (q ≫ aB)
  let t := purityTwistTransport P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
  dsimp only
  intro e we r hz
  let sq : IsPullback e.hom π q (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨we.trans (Category.comp_id _).symm⟩
  let c (T S : Scheme.{u}) (f : T ⟶ S) (aS : S ⟶ Spec (.of P.field.k)) :=
    Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t f (P.diagonalExponent_isUnit aS) d
  let L := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) q
  let L' := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) π
  let adj := Etale.rightDerivedUpperShriekAdjunction P.Coefficient q
  let adj' := Etale.rightDerivedUpperShriekAdjunction P.Coefficient π
  let τ := L.map
      ((Etale.affineLinearCoefficientDescent P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t B (P.diagonalExponent_isUnit aB) d) ≪≫
        c _ _ q aB).inv ≫
    (Etale.affineLinearCompactComparison P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d).inv ≫
    Etale.affineTraceCounit P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t D B (P.diagonalExponent_isUnit aB) d ≫
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom
  let τ' := L'.map (c _ _ π aB).inv ≫
    Etale.vectorBundleIntegration P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F ≫
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom
  let m := adj.homEquiv _ _ τ
  let m' := adj'.homEquiv _ _ τ'
  let G := Etale.ordinaryFinitePullback P.Coefficient e.hom
  let H := Etale.ordinaryFinitePullback P.Coefficient (𝟙 B)
  let S := Etale.ordinaryFinitePullback P.Coefficient r
  let S' := Etale.ordinaryFinitePullback P.Coefficient z
  have := Etale.isIso_rightDerivedLowerShriekBaseChangeMap P.Coefficient sq
  let ex : L ⋙ H ≅ G ⋙ L' :=
    asIso (Etale.rightDerivedLowerShriekBaseChangeMap P.Coefficient sq)
  have ht := affineVectorTracePresentation P B aB d F t D e we
  have hm := integration_mate_square adj adj' G H ex
    (c _ _ e.hom (q ≫ aB)).hom τ τ'
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) (𝟙 B)).hom ht
  change G.map m ≫ Etale.dualizingComplexBaseChangeMap P.Coefficient sq =
    (c _ _ e.hom (q ≫ aB)).hom ≫ m' at hm
  let ec : S ⋙ H ≅ G ⋙ S' :=
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) (𝟙 B) r).symm ≪≫
      Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        z e.hom ((𝟙 B) ≫ r) ((Category.id_comp r).trans hz.symm)
  have hc := Etale.orderedTatePullbackSquare P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t r z (𝟙 B) e.hom (hz.trans (Category.id_comp r).symm)
    (P.diagonalExponent_isUnit (q ≫ aB)) (P.diagonalExponent_isUnit aB)
    (P.diagonalExponent_isUnit (π ≫ aB)) d
  have hc' : H.map (c _ _ r (q ≫ aB)).inv ≫
      ec.hom.app (Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates (affineTraceTower B d) d) ≫
      S'.map (c _ _ e.hom (q ≫ aB)).hom =
      (c _ _ (𝟙 B) aB).hom ≫ (c _ _ z (π ≫ aB)).inv := by
    simpa only [ec, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Category.assoc] using hc
  have hr := restrict_orientation_square H G S S' ec
    (c _ _ r (q ≫ aB)) (c _ _ z (π ≫ aB)) (c _ _ (𝟙 B) aB)
    (c _ _ e.hom (q ≫ aB)).hom (Etale.dualizingComplexBaseChangeMap P.Coefficient sq)
    m m' hm hc'
  have hm_def : m = P.diagonalAffineMate t D B (P.diagonalExponent_isUnit aB) d ≫
      (OrientationCounit.unitChange P q).inv := by
    rw [affineCounitMate_unitChange]
    unfold Etale.CoordinateCounitArrows.towerAdjoint
    exact adj.homEquiv_naturality_left _ _
  have hm'_def : m' = (c _ _ π aB).inv ≫ adj'.homEquiv _ _
      (Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom) := by
    exact adj'.homEquiv_naturality_left _ _
  let ar := (c _ _ r (q ≫ aB)).inv ≫ S.map m
  have hr' : H.map ar ≫
      (Dnc.sectionBaseChange P.Coefficient d q sq r z
          (hz.trans (Category.id_comp r).symm)).hom =
      (c _ _ (𝟙 B) aB).hom ≫ OrientationRefinement.vectorBetaInverse P B aB d F := by
    simpa only [ar, OrientationRefinement.vectorBetaInverse, hm'_def, c, t, adj',
      H, S', π, z, Dnc.sectionBaseChange, ec, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, asIso_hom,
      Functor.map_comp, Etale.sectionInvariant, Etale.ordinaryFinitePullback,
      Category.assoc] using hr
  let I := Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B
  have hi : (c _ _ (𝟙 B) aB).hom = I.hom.app _ :=
    congrArg Iso.hom (coefficient_id P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t B (P.diagonalExponent_isUnit aB) d)
  have hh := congrArg (fun k ↦ I.inv.app _ ≫ k) hr'
  rw [hi] at hh
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hh
  have hn := I.inv.naturality ar
  change ar ≫ I.inv.app _ = I.inv.app _ ≫ H.map ar at hn
  rw [← hn] at hh
  simpa only [ar, hm_def, Etale.dualizingComplex, Category.assoc] using hh

/-- Restricting affine integration to the diagonal, then using a section-preserving
vector presentation, gives zero-section restriction of vector integration. This
assertion has no deformation, normal cone, delta, or beta.
Source: smooth-purity, Agreement on the model, translation and integration paragraphs;
vector integration, affine-frame normalization and base change.
(blueprint: lem-pur-restricted-affine-diagonal-vector-integration).

Proof: in restrictedAffineDiagonalCoordinates the diagonal is a section a of A^d_B.
Subtract a. Translation invariance of the ordered affine trace identifies restriction
of its adjunct to a with restriction to zero of the translated presentation.
In the free bundle frame, the normalization of vectorBundleIntegration is exactly
this affine counit, for every normalized t,D. Transpose that equality by the
compact-support adjunction and restrict to zero. Naturality of homEquiv and
section-exchange pasting give vectorModelSectionComparison, including its inverse
identity-pullback factor. The unit comparison unitChange converts the same adjunct
from the degree-zero coefficient to the monoidal unit. The canonical Tate pullback
comparisons compose, and their normalization fixes the answer independently of t.
To pass from the free presentation to the specified e, compose the two bundle
isomorphisms. This is a Cartesian map over identity preserving zero; apply
vector_zero_section_integration_baseChange. This theorem applies to arbitrary
zero-preserving bundle presentations, without a linearity hypothesis. Section
exchange composition cancels the intermediate free presentation. Finally transport
by nu-star and cancel the inverse sourceComparison in the definition of the
restricted trace. At d=0 all trace and Tate composites are unit composites; the
argument is also valid on the empty base. -/
theorem restrictedAffineDiagonalVectorIntegration (P : PurityFiniteSetting.{u})
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
    letI := H.separated
    letI := H.finiteType
    letI := H.quasiCompact
    letI := H.smoothDimension
    letI := H.baseFiniteType
    letI := H.baseQuasiCompact
    letI := H.sourceSeparated
    letI := H.sourceFiniteType
    letI := H.sourceQuasiCompact
    let h := affineTraceProjection Y d ∣_ V.1
    let B := (affineTraceProjection Y d ⁻¹ᵁ V.1).toScheme
    let aB := h ≫ V.1.ι ≫ aY
    letI := P.noetherian aB
    letI := SmoothOfRelativeDimension.smooth d h
    let g := pullback.fst h h
    let s := pullback.diagonal h
    letI := Dnc.compactifiable P g aB
    letI := Dnc.invertibleExponent P (g ≫ aB)
    ∀ (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d],
      letI := (Etale.vectorIntegration_geometry B d F).1
      letI := (Etale.vectorIntegration_geometry B d F).2.1
      letI := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
      ∀ (e : VectorBundleZeroSection.scheme B d F ≅ pullback h h)
        (we : e.hom ≫ g = VectorBundleZeroSection.π B d F)
        (ze : VectorBundleZeroSection.zero B d F ≫ e.hom = s),
        let ν := (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
        OrientationCounit.restrictedAffineDiagonalSectionTrace P Y d aY V H t D ≫
            (Dnc.sourceComparison P d g aB s).hom ≫
            ν.map (vectorModelSectionComparison P.Coefficient d g s F e we ze).hom =
          ν.map (OrientationRefinement.vectorBetaInverse P B aB d F) := by
  let tw := purityTwistTransport P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
  obtain rfl := Etale.ordinaryFiniteTwistTransport_unique P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t tw
  let := H.separated
  let := H.finiteType
  let := H.quasiCompact
  let := H.smoothDimension
  let := H.baseFiniteType
  let := H.baseQuasiCompact
  let := H.sourceSeparated
  let := H.sourceFiniteType
  let := H.sourceQuasiCompact
  let h := affineTraceProjection Y d ∣_ V.1
  let B := (affineTraceProjection Y d ⁻¹ᵁ V.1).toScheme
  let aB := h ≫ V.1.ι ≫ aY
  let := P.noetherian aB
  let := SmoothOfRelativeDimension.smooth d h
  let g := pullback.fst h h
  let s := pullback.diagonal h
  let := Dnc.compactifiable P g aB
  let := Dnc.invertibleExponent P (g ≫ aB)
  dsimp only
  intro F instF
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let π := VectorBundleZeroSection.π B d F
  let z := VectorBundleZeroSection.zero B d F
  let := Dnc.compactifiable P π aB
  intro e we ze
  let C := OrientationCounit.restrictedAffineDiagonalCoordinates Y d V.1
  let q := affineTraceProjection B d
  let := Dnc.compactifiable P q aB
  have hC : C.hom ≫ q = g :=
    OrientationCounit.restrictedAffineDiagonalCoordinates_over Y d V.1
  let : SmoothOfRelativeDimension d q :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension d) C.hom q).1 (by rw [hC]; infer_instance)
  let := Dnc.invertibleExponent P (q ≫ aB)
  let := affineTraceNoetherian B d
  let := P.noetherian (g ≫ aB)
  let := P.noetherian (π ≫ aB)
  let r := s ≫ C.hom
  let sqC : IsPullback C.hom g q (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨hC.trans (Category.comp_id _).symm⟩
  let sqe : IsPullback e.hom π g (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨we.trans (Category.comp_id _).symm⟩
  change e.hom ≫ g = π at we
  change z ≫ e.hom = s at ze
  have weC : (e ≪≫ C).hom ≫ q = π := by
    simpa only [Iso.trans_hom, Category.assoc, hC] using we
  have zeC : z ≫ (e ≪≫ C).hom = r := by
    simpa only [Iso.trans_hom, ← Category.assoc, r] using
      congrArg (fun f ↦ f ≫ C.hom) ze
  have hc := Dnc.section_baseChange_comp_over_id P.Coefficient d q g π sqC sqe
    r s z rfl ze
  have hi := affine_section_presentation P B aB d F D (e ≪≫ C) weC r zeC
  let c := Dnc.sectionBaseChange P.Coefficient d q sqC r s
    (Category.id_comp r).symm
  let a :=
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates tw r (P.diagonalExponent_isUnit (q ≫ aB)) d).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient r).map
        (P.diagonalAffineMate tw D B (P.diagonalExponent_isUnit aB) d ≫
          (OrientationCounit.unitChange P q).inv)
  have heq : a ≫
      (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).inv.app _ ≫
      c.hom ≫ (vectorModelSectionComparison P.Coefficient d g s F e we ze).hom =
      OrientationRefinement.vectorBetaInverse P B aB d F := by
    have hh := congrArg (fun k ↦ a ≫ k.hom) hc
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc] at hh
    calc
      _ = a ≫
          (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).inv.app _ ≫
          (Dnc.sectionBaseChange P.Coefficient d q
            (IsPullback.of_horiz_isIso ⟨weC.trans (Category.comp_id _).symm⟩)
            r z (zeC.trans (Category.id_comp r).symm)).hom := by
        simpa only [a, c, vectorModelSectionComparison, Iso.trans_hom,
          Iso.symm_hom, Iso.app_hom, Etale.sectionInvariant,
          Etale.ordinaryFinitePullback, Category.assoc] using hh.symm
      _ = _ := by
        simpa only [a, q, z, tw, Category.assoc] using hi
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  have hn := congrArg ν.map heq
  simp only [Functor.map_comp] at hn
  unfold OrientationCounit.restrictedAffineDiagonalSectionTrace
  simpa only [a, c, ν, r, C, q, g, s, h, B, aB, Etale.ordinaryFinitePullback,
    diagonalTwist, diagonalTwistEtale, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc] using hn

end WeilConjectures.PurityFiniteSetting
