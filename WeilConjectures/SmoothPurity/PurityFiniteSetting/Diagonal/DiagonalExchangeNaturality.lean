/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalBaseChangeCompared
public import WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Naturality of the section restriction of a dualizing exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem pullback_comp_endpoint (A : Type (u + 1)) [CommRing A]
    {B X Z : Scheme.{u}} (v : Z ⟶ X) (p : X ⟶ B) (z : Z ⟶ B)
    (hz : z = v ≫ p) (K : Etale.DerivedCategoryModule A B) :
    (eqToIso (congrArg (fun r ↦ (Etale.ordinaryFinitePullback A r).obj K) hz)).hom ≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).app K).hom =
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p z hz).app K).hom := by
  subst z
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

private theorem dualizing_base_congr (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' X X' : Scheme.{u}} {f : X ⟶ B} {f' : X' ⟶ B'}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    {v v' : X' ⟶ X} {b b' : B' ⟶ B}
    (sq : IsPullback v f' f b) (sq' : IsPullback v' f' f b')
    (hv : v = v') (hb : b = b') :
    Etale.dualizingComplexBaseChangeMap A sq =
      (eqToIso (congrArg (fun r ↦ (Etale.ordinaryFinitePullback A r).obj
        (Etale.dualizingComplex A f)) hv)).hom ≫
        Etale.dualizingComplexBaseChangeMap A sq' := by
  subst v'
  subst b'
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- Two factorizations of one Cartesian rectangle have the same dualizing exchange.
Source: smooth exceptional base change, adjunction mate pasting.
Proof: apply the base-change composition law to both factorizations, identify the
outer square by equality of its arrows, and cancel the first pullback compositor.

(blueprint: lem-pur-diagonal-exchange-naturality).
-/
theorem dualizing_base_rectangle (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X₁ X₂ X' B B₁ B₂ B' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X₁] [IsNoetherian X₂] [IsNoetherian X']
    [IsNoetherian B] [IsNoetherian B₁] [IsNoetherian B₂] [IsNoetherian B']
    {f : X ⟶ B} {f₁ : X₁ ⟶ B₁} {f₂ : X₂ ⟶ B₂} {f' : X' ⟶ B'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f₁]
    [HasCompactification f₂] [HasCompactification f']
    [QuasiCompact f₁] [QuasiCompact f₂] [QuasiCompact f']
    {v₁ : X₁ ⟶ X} {v₂ : X₂ ⟶ X} {w₁ : X' ⟶ X₁} {w₂ : X' ⟶ X₂}
    {b₁ : B₁ ⟶ B} {b₂ : B₂ ⟶ B} {a₁ : B' ⟶ B₁} {a₂ : B' ⟶ B₂}
    (sq₁ : IsPullback v₁ f₁ f b₁) (sq₂ : IsPullback v₂ f₂ f b₂)
    (sq₁' : IsPullback w₁ f' f₁ a₁) (sq₂' : IsPullback w₂ f' f₂ a₂)
    (hv : w₁ ≫ v₁ = w₂ ≫ v₂) (hb : a₁ ≫ b₁ = a₂ ≫ b₂) :
    (Etale.ordinaryFinitePullback A w₁).map
        (Etale.dualizingComplexBaseChangeMap A sq₁) ≫
        Etale.dualizingComplexBaseChangeMap A sq₁' =
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w₁ v₁).inv.app
          (Etale.dualizingComplex A f)) ≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
          w₂ v₂ (w₁ ≫ v₁) hv).hom.app
          (Etale.dualizingComplex A f)) ≫
        (Etale.ordinaryFinitePullback A w₂).map
          (Etale.dualizingComplexBaseChangeMap A sq₂) ≫
        Etale.dualizingComplexBaseChangeMap A sq₂' := by
  have h₁ := Etale.dualizing_base_comp A sq₁ sq₁'
  have h₂ := Etale.dualizing_base_comp A sq₂ sq₂'
  have h₃ := dualizing_base_congr A (sq₁'.paste_horiz sq₁)
    (sq₂'.paste_horiz sq₂) hv hb
  rw [h₁, h₂] at h₃
  apply (cancel_epi ((Etale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} A) w₁ v₁).hom.app _)).1
  dsimp only [Etale.ordinaryFinitePullback]
  rw [h₃]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have he := pullback_comp_endpoint A w₂ v₂ (w₁ ≫ v₁) hv
    (Etale.dualizingComplex A f)
  dsimp only [Etale.ordinaryFinitePullback, Iso.app_hom] at he
  rw [he]

/-- Restriction along compatible sections commutes with an inverse dualizing exchange.
This formal statement separates the section compositor from the geometric pasting equation.
Source: blueprint diagonal base-change comparison and inverse-image section coherence.
Proof: naturality moves the inverse exchange through the section-square compositor.
The assumed outer exchange equation cancels the two inverse exchanges. The remaining
identity is the inverse-image coherence equation for the two compatible sections.

(blueprint: lem-pur-diagonal-exchange-naturality).
-/
theorem section_inverse_exchange_naturality (A : Type (u + 1)) [CommRing A]
    {B B' W W' : Scheme.{u}} (a : B' ⟶ B) (p : W ⟶ B) (p' : W' ⟶ B')
    (v : W' ⟶ W) (s : B ⟶ W) (s' : B' ⟶ W')
    (hv : v ≫ p = p' ≫ a) (hs : s' ≫ v = a ≫ s)
    (h : s ≫ p = 𝟙 B) (h' : s' ≫ p' = 𝟙 B')
    (M : Etale.DerivedCategoryModule A B) (M' : Etale.DerivedCategoryModule A B')
    (N : Etale.DerivedCategoryModule A W) (N' : Etale.DerivedCategoryModule A W')
    (e : (Etale.ordinaryFinitePullback A p).obj M ≅ N)
    (e' : (Etale.ordinaryFinitePullback A p').obj M' ≅ N')
    (b : (Etale.ordinaryFinitePullback A a).obj M ≅ M')
    (c : (Etale.ordinaryFinitePullback A v).obj N ≅ N')
    (he : (Etale.ordinaryFinitePullback A v).mapIso e ≪≫ c =
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).symm.app M ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p' a (v ≫ p) hv).app M) ≪≫
          (Etale.ordinaryFinitePullback A p').mapIso b ≪≫ e') :
    (Etale.ordinaryFinitePullback A a).mapIso
        ((Etale.ordinaryFinitePullback A s).mapIso e.symm ≪≫
          (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).app M) ≪≫ b =
      Etale.sectionCoherencePullbackIso A a s s' v hs.symm N ≪≫
        (Etale.ordinaryFinitePullback A s').mapIso c ≪≫
        (Etale.ordinaryFinitePullback A s').mapIso e'.symm ≪≫
        (Etale.leftDerivedUpperStarCompSectionIso
          (ModuleCat.{u + 1} A) s' p' h').app M' := by
  let L := Etale.ordinaryFinitePullback A a
  let S := Etale.ordinaryFinitePullback A s
  let S' := Etale.ordinaryFinitePullback A s'
  let V := Etale.ordinaryFinitePullback A v
  let j := Etale.sectionCoherencePullbackIso A a s s' v hs.symm
  have hn := ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a s).symm ≪≫
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' v (a ≫ s) hs.symm).hom.naturality
      e.inv
  simp only [Functor.comp_map] at hn
  have hc := Etale.leftDerivedUpperStar_map_comp_compSectionIso
    (ModuleCat.{u + 1} A) a p p' v s s' hv hs h h' M
  have hb := (Etale.leftDerivedUpperStarCompSectionIso
    (ModuleCat.{u + 1} A) s' p' h').hom.naturality b.hom
  simp only [Functor.comp_map, Functor.id_map] at hb
  have hei : c ≪≫ e'.symm =
      (V.mapIso e).symm ≪≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v p).symm.app M ≪≫
          (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
            p' a (v ≫ p) hv).app M) ≪≫
        (Etale.ordinaryFinitePullback A p').mapIso b := by
    calc
      _ = (V.mapIso e).symm ≪≫ ((V.mapIso e ≪≫ c) ≪≫ e'.symm) := by
        simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
      _ = _ := by rw [he]; simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  apply Iso.ext
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  have heih := congrArg Iso.hom hei
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv] at heih
  rw [← S'.map_comp_assoc, heih]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  erw [hb]
  simp only [Functor.map_comp, Category.assoc] at hc
  erw [reassoc_of% hc]
  have hj := Etale.sectionPullback_endpoint A a s s' v (s' ≫ v) (a ≫ s)
    hs rfl rfl hs.symm ((Etale.ordinaryFinitePullback A p).obj M)
  have hji := congrArg Iso.inv hj
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, NatTrans.comp_app] at hji
  dsimp only [Etale.ordinaryFinitePullback] at hji ⊢
  erw [reassoc_of% hji]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]

end WeilConjectures.PurityFiniteSetting
