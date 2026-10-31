/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.SecSmoothPurity.ProEtaleDerivedOpenRestriction
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.ProEtaleOpenSquareExchange
import all WeilConjectures.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport
import all WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import all WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import all Mathlib.AlgebraicGeometry.Pullbacks
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import all WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Category.ULift
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import all WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.RestrictionRingedToposModuleDirectImageSupplement
import all WeilConjectures.SixFunctors.BaseChange.DerivedForget
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import all WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import all WeilConjectures.AlgebraicGeometry.FixSiteOpenExchangeSheaf

/-!
# Cartesian open restriction of the specified derived adjunction

Source: blueprint main-20261015, `prop-sf-pf-coherence.proof.md`, compactification
independence and the following open-factor/counit calculation; Stacks Project,
Cohomology on Sites, Tag 07A7, and Derived Categories, Tags 0DVC and 0FND
(blueprint: lem-sf-cartesian-open-adjunction-restriction).

The comparison is the conjugate of the specified inverse open exchange. Hence its
Hom map is the five-adjunction chain in the node, including the inverse of beta.
All categories are ordinary uncompleted unbounded constant-ring module categories.

## Main definitions

* `sfCartesianOpenPullPushAdjunction`: the published unbounded derived adjunction.
* `sfCartesianOpenHomComparison`: the conjugate of the specified inverse open exchange.

## Main statement

* `sfCartesianOpenAdjunctionRestriction`: normalization and the unit/counit equations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

/-- The specified inverse-image/direct-image adjunction, obtained from the canonical
constant-section module adjunction by exact inverse image and K-injective direct image.
This only names the existing construction in the intrinsic finite-coefficient coordinates.
Source: Stacks Tags 0DVC and 0FND; blueprint compactification-independence calculation
(blueprint: lem-sf-cartesian-open-adjunction-restriction). -/
def sfCartesianOpenPullPushAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfIntrinsicDerivedPullback A f ⊣ proEtaleConstantDerivedDirectImage f A :=
  (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction

/-- The comparison defined by the node's Hom chain. Conjugation first transposes by
`J_i ⊣ P_i` and `P_p ⊣ S_p`, precomposes with the specified `beta` inverse, and then
transposes by `J_b ⊣ P_b` and `P_q ⊣ S_q`. The inverse open exchange is the exact
termwise descent of the open-unit mate, namely `sfIntrinsicDerivedOpenMate`, rather
than a freely chosen isomorphism. Its normalization is that of
`lem-sf-open-tensor-normalization`. Here `b = pullback.fst p i` and
`q = pullback.snd p i`, so the square is the chosen scheme fibre product.
Source: blueprint compactification-independence calculation; Stacks Tag 07A7
(blueprint: lem-sf-cartesian-open-adjunction-restriction). -/
def sfCartesianOpenHomComparison (A : Type u) [CommRing A] [Finite A]
    {V Z W : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion i] :
    proEtaleConstantDerivedDirectImage p A ⋙ sfIntrinsicDerivedPullback A i ⟶
      sfIntrinsicDerivedPullback A (pullback.fst p i) ⋙
        proEtaleConstantDerivedDirectImage (pullback.snd p i) A :=
  conjugateEquiv
    ((exceptionalOpenAdjunction i A).comp (sfCartesianOpenPullPushAdjunction A p))
    ((sfCartesianOpenPullPushAdjunction A (pullback.snd p i)).comp
      (exceptionalOpenAdjunction (pullback.fst p i) A))
    (sfIntrinsicDerivedOpenMate A (pullback.snd p i) (pullback.fst p i) i p
      (pullback.condition (f := p) (g := i)).symm)

attribute [local irreducible] sfIntrinsicModuleEquivalence sfIntrinsicPullback
  sfIntrinsicExtensionByZero sfIntrinsicOpenMate sfIntrinsicSquarePullback
  sfIntrinsicOpenAdjunction

-- Changing the right-adjoint coordinates conjugates the mate by those coordinates.
private theorem mate_ofNatIsoRight
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R S : D ⥤ C} {L' : C' ⥤ D'} {R' S' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'} (a : L ⊣ R) (b : L' ⊣ R')
    (e : R ≅ S) (e' : R' ≅ S') (σ : TwoSquare G L L' H) :
    (mateEquiv (a.ofNatIsoRight e) (b.ofNatIsoRight e') σ).natTrans =
      whiskerRight e.inv G ≫ (mateEquiv a b σ).natTrans ≫ whiskerLeft H e'.hom := by
  apply Etale.mate_eq_of_unit
  intro M
  have hm := unit_mateEquiv a b σ M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc (e.hom.app _) (e.inv.app _), Iso.hom_inv_id_app,
    G.map_id, Category.id_comp, reassoc_of% hm]
  exact congrArg (fun f ↦ b.unit.app (G.obj M) ≫ f)
    (e'.hom.naturality (σ.app M)).symm

private theorem trMate_forward
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂) (e₃ : C₃ ≌ D₃) (e₄ : C₄ ≌ D₄)
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (G : C₁ ⥤ C₃) (H : C₂ ⥤ C₄)
    (σ : G ⋙ L₂ ⟶ L₁ ⋙ H) :
    (mateEquiv (trAdj e₁ e₂ a) (trAdj e₃ e₄ b)
      ((trComp e₁ e₃ e₄ G L₂).inv ≫ trNat e₁ e₄ σ ≫
        (trComp e₁ e₂ e₄ L₁ H).hom)).natTrans =
      (trComp e₂ e₁ e₃ R₁ G).inv ≫
        trNat e₂ e₃ (mateEquiv a b σ).natTrans ≫
          (trComp e₂ e₄ e₃ H R₂).hom := by
  have h := trMate e₁ e₂ e₃ e₄ a b G H (mateEquiv a b σ).natTrans
  rw [Equiv.symm_apply_apply] at h
  have hh := congrArg (fun t ↦
    (mateEquiv (trAdj e₁ e₂ a) (trAdj e₃ e₄ b) t).natTrans) h
  simpa only [Equiv.apply_symm_apply] using hh.symm

attribute [local semireducible] sfIntrinsicPullback

-- The sectionwise restriction square is the ordinary pullback-composition mate.
private theorem ordinaryRestriction_eq_mate (A : Type u) [CommRing A] [Finite A]
    {U V W T : Scheme.{u}} (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    (sfProperOpenPullbackRestriction A r k i p sq).hom =
      (mateEquiv (sfIntrinsicConstantModuleAdjunction p A)
        (sfIntrinsicConstantModuleAdjunction r A)
        (sfIntrinsicSquarePullback A r k i p sq.w).hom).natTrans := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have hb : (fixed_restriction A r k i p sq).hom =
      (mateEquiv (ProEtale.upperStarLowerStarAdjunction B p)
        (ProEtale.upperStarLowerStarAdjunction B r)
        (ProEtale.upperStarCompIso B sq.w).hom).natTrans := by
    rw [fixed_restriction_eq_baseChange]
    exact ProEtale.pro_baseChange_eq_mate _ sq.toCommSq
  rw [sfIntrinsicConstantModuleAdjunction, sfIntrinsicConstantModuleAdjunction,
    sfSquare_transport]
  rw [mate_ofNatIsoRight]
  simp only [Iso.trans_hom, Iso.symm_hom]
  erw [trMate_forward]
  rw [← hb]
  rfl

attribute [local irreducible] sfIntrinsicPullback

-- Exact localization preserves the unit equation characterizing a mate.
private theorem exactAdj_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : L ⊣ R) (b : L' ⊣ R') (β : G ⋙ L' ≅ L ⋙ H) (τ : R ⋙ G ≅ H ⋙ R')
    (hm : mateEquiv a b β.hom = τ.hom) :
    mateEquiv (exactAdj a) (exactAdj b) (mapDerivedCategorySquareIso β).hom =
      (mapDerivedCategorySquareIso τ).hom := by
  apply TwoSquare.ext
  intro K
  have he := Etale.mate_eq_of_unit (exactAdj a) (exactAdj b)
    (TwoSquare.mk _ _ _ _ (mapDerivedCategorySquareIso β).hom)
    (mapDerivedCategorySquareIso τ).hom
    (exact_unit_square a b (exactAdj a) (exactAdj b)
      (exactAdj_unit_Qh a) (exactAdj_unit_Qh b) G H τ β (fun M ↦ by
        have h := unit_mateEquiv a b β.hom M
        rw [hm] at h
        exact h.symm))
  exact congrArg (fun t ↦ t.app K) he

private theorem derivedOpenMate_mate (A : Type u) [CommRing A] [Finite A]
    {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) :
    mateEquiv (exceptionalOpenAdjunction j A) (exceptionalOpenAdjunction j' A)
      (sfIntrinsicDerivedOpenMate A gU j' j g sq.w) =
        (sfIntrinsicDerivedSquarePullback A gU j' j g sq.w).hom := by
  have := sfOpenMate_isIso A gU j' j g sq
  rw [sfDerivedMate_eq]
  exact exactAdj_mate (sfIntrinsicOpenAdjunction A j) (sfIntrinsicOpenAdjunction A j')
    (asIso (sfIntrinsicOpenMate A gU j' j g sq.w))
    (sfIntrinsicSquarePullback A gU j' j g sq.w) (sfOpenMate_mate A gU j' j g sq.w)

private theorem cartesianOpenHom_eq_mate (A : Type u) [CommRing A] [Finite A]
    {V Z W : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion i] :
    sfCartesianOpenHomComparison A p i =
      (mateEquiv (sfCartesianOpenPullPushAdjunction A p)
        (sfCartesianOpenPullPushAdjunction A (pullback.snd p i))
        (sfIntrinsicDerivedSquarePullback A (pullback.snd p i) (pullback.fst p i)
          i p (pullback.condition (f := p) (g := i)).symm).hom).natTrans := by
  rw [sfCartesianOpenHomComparison, ← iterated_mateEquiv_conjugateEquiv,
    derivedOpenMate_mate A _ _ _ _ (IsPullback.of_hasPullback p i).flip]

private theorem derivedRestriction_eq_mate (A : Type u) [CommRing A] [Finite A]
    {U V W T : Scheme.{u}} (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    (sfProperOpenDerivedRestriction A r k i p sq).hom =
      (mateEquiv (sfCartesianOpenPullPushAdjunction A p)
        (sfCartesianOpenPullPushAdjunction A r)
        (sfIntrinsicDerivedSquarePullback A r k i p sq.w).hom).natTrans := by
  rw [intrinsic_restriction_eq_square, ordinaryRestriction_eq_mate]
  exact (Etale.derived_mate_exact_eq_square
    (sfIntrinsicConstantModuleAdjunction p A) (sfIntrinsicConstantModuleAdjunction r A)
    (sfIntrinsicSquarePullback A r k i p sq.w)).symm

/-- Open restriction identifies the Hom-chain comparison with ordinary derived
restriction, with its identity-on-sections normalization, and preserves the actual
unit and counit. The pullback-square comparison is oriented `P_q P_i ≅ P_b P_p`.
There is no properness, quasi-compactness, constructibility, Tor, or boundedness
hypothesis. Naturality is built into the natural transformations and adjunctions.
Source: blueprint main-20261015, `prop-sf-pf-coherence.proof.md`, compactification
independence and open-factor/counit calculation; Stacks Tags 07A7, 0DVC and 0FND
(blueprint: lem-sf-cartesian-open-adjunction-restriction).

Proof plan (the node's five steps).
1. Expand the five adjunctions in the Hom chain. Put
`c_G = theta_(S_p G)` followed by `P_b(epsilon_(p,G))`.
The open-unit normalization of `lem-sf-open-tensor-normalization` identifies
`P_b(beta_H inverse)` after the b-open unit with `P_q` of the i-open unit
followed by `theta_(J_i H)`. Move the intervening maps using theta naturality
and cancel the i-open unit/counit using its triangle identity. The transpose
of a map f is consequently `P_q(f)` followed by `c_G`; at the identity this
identifies E with `eta_q` followed by `S_q(c_G)`.
2. For ordinary sheaves, the restriction map is the identity on sections under
`V times_Z Q = (V times_Z W) times_W Q`. The inverse-image colimit formula of
`def-weil-proetale-inverse-image` sends a representative (a,s) under the counit
to the restriction of s along a. Both ordinary transposes give that same map.
The actions, restrictions and sheafifications agree by their universal properties.
3. Choose a K-injective representative I of G. By
`lem-exc-proetale-derived-open-restriction`, open pullback preserves K-injectives
and rho is represented by the degreewise section identity. The representative
characterization in `lem-pc-pre-derived-adjoint-functors-general`, applied to the
specified operations of `def-weil-pbc-proetale-operations`, identifies its derived
transpose with the localization of the ordinary transpose in Step 2. Thus rho = E,
including the chosen counit and compositor, and E is invertible.
4. Transpose the proposed unit equation under `P_q ⊣ S_q`. The left transpose is
`c_(P_p F)` after `P_q P_i(eta_(p,F))`. Naturality of theta and the p-triangle
reduce this to theta_F. The right transpose is theta_F by the q-triangle.
Injectivity of the adjunction bijection gives the unit equation.
5. The counit equation is the defining transpose of E from Step 1. Equivalently,
expand E and apply counit naturality and the q-triangle identity. Every reduction
uses natural transformations, so both equalities are natural in their inputs. -/
theorem sfCartesianOpenAdjunctionRestriction (A : Type u) [CommRing A] [Finite A]
    {V Z W : Scheme.{u}} (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion i] :
    sfCartesianOpenHomComparison A p i = proEtaleOpenRestrictionComparison p i A ∧
    (∀ F : proEtaleDerivedCategory Z A,
      (sfIntrinsicDerivedPullback A i).map
          ((sfCartesianOpenPullPushAdjunction A p).unit.app F) ≫
        (sfCartesianOpenHomComparison A p i).app ((sfIntrinsicDerivedPullback A p).obj F) =
      (sfCartesianOpenPullPushAdjunction A (pullback.snd p i)).unit.app
          ((sfIntrinsicDerivedPullback A i).obj F) ≫
        (proEtaleConstantDerivedDirectImage (pullback.snd p i) A).map
          ((sfIntrinsicDerivedSquarePullback A (pullback.snd p i) (pullback.fst p i)
            i p (pullback.condition (f := p) (g := i)).symm).hom.app F)) ∧
    (∀ G : proEtaleDerivedCategory V A,
      (sfIntrinsicDerivedPullback A (pullback.snd p i)).map
          ((sfCartesianOpenHomComparison A p i).app G) ≫
        (sfCartesianOpenPullPushAdjunction A (pullback.snd p i)).counit.app
          ((sfIntrinsicDerivedPullback A (pullback.fst p i)).obj G) =
      (sfIntrinsicDerivedSquarePullback A (pullback.snd p i) (pullback.fst p i)
          i p (pullback.condition (f := p) (g := i)).symm).hom.app
          ((proEtaleConstantDerivedDirectImage p A).obj G) ≫
        (sfIntrinsicDerivedPullback A (pullback.fst p i)).map
          ((sfCartesianOpenPullPushAdjunction A p).counit.app G)) := by
  rw [cartesianOpenHom_eq_mate]
  refine ⟨?_, ?_, ?_⟩
  · exact (derivedRestriction_eq_mate A _ _ _ _
      (IsPullback.of_hasPullback p i).flip).symm
  · intro F
    exact unit_mateEquiv (sfCartesianOpenPullPushAdjunction A p)
      (sfCartesianOpenPullPushAdjunction A (pullback.snd p i)) _ F
  · intro G
    exact mateEquiv_counit (sfCartesianOpenPullPushAdjunction A p)
      (sfCartesianOpenPullPushAdjunction A (pullback.snd p i)) _ G

end AlgebraicGeometry.Scheme
