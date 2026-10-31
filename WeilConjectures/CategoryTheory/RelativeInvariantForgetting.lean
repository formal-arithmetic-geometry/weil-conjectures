/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RelativeCyclicTotal
import WeilConjectures.CategoryTheory.RelativeForgettingKInjectives
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
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
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # RelativeInvariantForgetting

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: def-sfb-relative-invariant-forgetting)

## Main definitions and statements

The primary declaration is `forgetDerived`.
The accompanying definitions fix the canonical maps, coordinates and normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate ProductInvariants)
namespace CategoryTheory.RelativeCyclic
variable (A : CondensedBar.Ring.{u}) (G J : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {A' : CondensedBar.Ring.{u}}
variable {J}
omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem fixed_iff (N : Equivariant A (G × J)) (S : Profinite.{u})
    (x : Profinite.CondensedAction.sectionModule A.toMon N.module S) :
    Profinite.CondensedAction.Fixed N (ContinuousMonoidHom.fst G J) S x ↔
      Profinite.CondensedAction.FixedAll ((forgetResidual A G J).obj N) S x := by
  constructor
  · intro h T f g
    exact h T f ((ContinuousMonoidHom.inr G J).toContinuousMap.comp g) (fun _ ↦ rfl)
  · intro h T f g hg
    have he : (ContinuousMonoidHom.inr G J).toContinuousMap.comp
        ((ContinuousMonoidHom.snd G J).toContinuousMap.comp g) = g := by
      apply ContinuousMap.ext
      intro t
      exact Prod.ext (hg t).symm rfl
    have hh := h T f ((ContinuousMonoidHom.snd G J).toContinuousMap.comp g)
    change (N.act T ((ContinuousMonoidHom.inr G J).toContinuousMap.comp
      ((ContinuousMonoidHom.snd G J).toContinuousMap.comp g))).toFun _ = _ at hh
    rw [he] at hh
    exact hh

set_option backward.isDefEq.respectTransparency.types false in
private def forgetInvariantsMapApp (N : Equivariant A (G × J)) :
    ((invariants A G J).functor.obj N).module ⟶
      (CondensedDerivedRestriction.invariants A J).functor.obj
        ((forgetResidual A G J).obj N) :=
  (CondensedDerivedRestriction.invariants A J).adjunction.homEquiv _ _
    ⟨(invariants A G J).inclusion.app N, by
      intro S g x
      have hx := ((invariants A G J).image N S _).mp ⟨x, rfl⟩
      have h := (fixed_iff A G N S _).mp hx S (𝟙 S) g
      change (((invariants A G J).inclusion.app N).hom.hom.app (op S)).hom x = _
      (convert! h.symm using 1 <;> simp); rfl⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem forgetInvariantsMapApp_inclusion (N : Equivariant A (G × J)) :
    forgetInvariantsMapApp A G N ≫
        (CondensedDerivedRestriction.invariants A J).inclusion.app
          ((forgetResidual A G J).obj N) = (invariants A G J).inclusion.app N :=
  (CondensedDerivedRestriction.invariants A J).transpose _ _ _

private theorem scalarInclusion_cancel (N : Equivariant A J) {M : Modules A}
    (f g : M ⟶ (CondensedDerivedRestriction.invariants A J).functor.obj N)
    (h : f ≫ (CondensedDerivedRestriction.invariants A J).inclusion.app N =
      g ≫ (CondensedDerivedRestriction.invariants A J).inclusion.app N) : f = g := by
  apply Mod.hom_ext
  ext S x
  apply (CondensedDerivedRestriction.invariants A J).injective N S.unop
  exact ConcreteCategory.congr_hom
    (congr_app (congrArg (fun k ↦ k.hom.hom) h) S) x

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem forgetInvariantsMapApp_isIso (N : Equivariant A (G × J)) :
    IsIso (forgetInvariantsMapApp A G N) := by
  let f := forgetInvariantsMapApp A G N
  have hf (S : Profinite.{u})
      (x : Profinite.CondensedAction.sectionModule A.toMon
        ((invariants A G J).functor.obj N).module S) :
      (((CondensedDerivedRestriction.invariants A J).inclusion.app
        ((forgetResidual A G J).obj N)).hom.hom.app (op S)).hom
          ((f.hom.hom.app (op S)).hom x) =
        (((invariants A G J).inclusion.app N).hom.hom.app (op S)).hom x :=
    ConcreteCategory.congr_hom (congr_app (congrArg (fun k ↦ k.hom.hom)
      (forgetInvariantsMapApp_inclusion A G N)) (op S)) x
  have hbij (S : Profinite.{u}) : Function.Bijective
      ((f.hom.hom.app (op S)).hom) := by
    constructor
    · intro x y h
      apply (invariants A G J).injective N S
      rw [← hf S x, ← hf S y, h]
    · intro y
      let z := (((CondensedDerivedRestriction.invariants A J).inclusion.app
        ((forgetResidual A G J).obj N)).hom.hom.app (op S)).hom y
      have hz := ((CondensedDerivedRestriction.invariants A J).image
        ((forgetResidual A G J).obj N) S z).mp ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := ((invariants A G J).image N S z).mpr
        ((fixed_iff A G N S z).mpr hz)
      refine ⟨x, (CondensedDerivedRestriction.invariants A J).injective
        ((forgetResidual A G J).obj N) S ?_⟩
      exact (hf S x).trans hx
  have (S : Profinite.{u}ᵒᵖ) : IsIso (f.hom.hom.app S) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hbij S.unop
  have : IsIso f.hom.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf _ _).map f.hom) := by
    change IsIso f.hom.hom
    infer_instance
  have : IsIso f.hom := isIso_of_reflects_iso f.hom (sheafToPresheaf _ _)
  have : IsIso ((Mod.forget _).map f) := by
    change IsIso f.hom
    infer_instance
  exact isIso_of_reflects_iso f (Mod.forget _)

set_option linter.unusedSectionVars false in
/-- Forgetting residual actions commutes with ordinary invariants, with its isomorphism
fixed by the two actual invariant-submodule inclusions.
Source: paragraph (3), step 6
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: both section modules consist of exactly the sections fixed by the second group
after every base change; compose both embeddings into the same underlying module. -/
theorem forgetInvariantsExist :
    ∃! e : (invariants A G J).functor ⋙ CondensedBar.forgetAction ≅
        forgetResidual A G J ⋙ (CondensedDerivedRestriction.invariants A J).functor,
      ∀ N, e.hom.app N ≫
          (CondensedDerivedRestriction.invariants A J).inclusion.app
            ((forgetResidual A G J).obj N) = (invariants A G J).inclusion.app N := by
  let b : (invariants A G J).functor ⋙ CondensedBar.forgetAction ⟶
      forgetResidual A G J ⋙ (CondensedDerivedRestriction.invariants A J).functor :=
    { app := forgetInvariantsMapApp A G
      naturality := by
        intro M N f
        apply scalarInclusion_cancel A (J := J) ((forgetResidual A G J).obj N)
        change ((invariants A G J).functor.map f).val ≫
            forgetInvariantsMapApp A G N ≫ _ =
          (forgetInvariantsMapApp A G M ≫
            (CondensedDerivedRestriction.invariants A J).functor.map
              ((forgetResidual A G J).map f)) ≫ _
        rw [forgetInvariantsMapApp_inclusion, Category.assoc,
          (CondensedDerivedRestriction.invariants A J).inclusion.naturality,
          ← Category.assoc, forgetInvariantsMapApp_inclusion]
        exact (invariants A G J).inclusion.naturality f }
  have (N : Equivariant A (G × J)) : IsIso (b.app N) :=
    forgetInvariantsMapApp_isIso A G N
  have : IsIso b := NatIso.isIso_of_isIso_app b
  refine ⟨asIso b, forgetInvariantsMapApp_inclusion A G, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply scalarInclusion_cancel A (J := J) ((forgetResidual A G J).obj N)
  exact (he N).trans (forgetInvariantsMapApp_inclusion A G N).symm

/-- The unique comparison of actual fixed submodules.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgetInvariants : (invariants A G J).functor ⋙ CondensedBar.forgetAction ≅
    forgetResidual A G J ⋙ (CondensedDerivedRestriction.invariants A J).functor :=
  Classical.choose (forgetInvariantsExist A G (J := J))

universe w

set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedDerivedComparison
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : A' ⥤ B') (x : A ⥤ A') (y : B ⥤ B')
    [F.Additive] [G.Additive] [x.Additive] [y.Additive]
    (rX : DerivedCategory.{w} A ⥤ DerivedCategory.{w} A')
    (rY : DerivedCategory.{w} B ⥤ DerivedCategory.{w} B')
    (phiX : DerivedCategory.Q.{w} ⋙ rX ≅
      x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w})
    (phiY : DerivedCategory.Q.{w} ⋙ rY ≅
      y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w})
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (RG : DerivedCategory.{w} A' ⥤ DerivedCategory.{w} B')
    (etaF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (etaG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RG)
    (hF : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (etaF.app I))
    (hG : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (etaG.app ((x.mapHomologicalComplex (.up ℤ)).obj I)))
    (c : F ⋙ y ≅ x ⋙ G) :
    ∃! kappa : RF ⋙ rY ≅ rX ⋙ RG,
      ∀ M : CochainComplex A ℤ,
        phiY.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
            rY.map (etaF.app M) ≫ kappa.hom.app (DerivedCategory.Q.{w}.obj M) =
          DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
            etaG.app ((x.mapHomologicalComplex (.up ℤ)).obj M) ≫ RG.map (phiX.inv.app M) := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let xc := x.mapHomologicalComplex (.up ℤ)
  let cc := NatIso.mapHomologicalComplex c (.up ℤ)
  -- Both units derive the same ordinary composite; exactness is encoded by phiX and phiY.
  let etaL : (F ⋙ y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (RF ⋙ rY) :=
    Functor.whiskerLeft Fc phiY.inv ≫ Functor.whiskerRight etaF rY
  let etaR : (F ⋙ y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (rX ⋙ RG) :=
    Functor.whiskerRight cc.hom DerivedCategory.Q.{w} ≫
      Functor.whiskerLeft xc etaG ≫ Functor.whiskerRight phiX.inv RG
  have hL : (RF ⋙ rY).IsRightDerivedFunctor etaL
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (derives (F ⋙ y)).isRightDerivedFunctor_of_isIso etaL
    intro I
    have := hF I.obj I.property
    change IsIso (phiY.inv.app (Fc.obj I.obj) ≫ rY.map (etaF.app I.obj))
    infer_instance
  have hR : (rX ⋙ RG).IsRightDerivedFunctor etaR
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (derives (F ⋙ y)).isRightDerivedFunctor_of_isIso etaR
    intro I
    have : IsIso (etaG.app (xc.obj I.obj)) := hG I.obj I.property
    change IsIso (DerivedCategory.Q.map (cc.hom.app I.obj) ≫
      etaG.app (xc.obj I.obj) ≫ RG.map (phiX.inv.app I.obj))
    apply IsIso.comp_isIso'
    · infer_instance
    · apply IsIso.comp_isIso'
      · exact hG I.obj I.property
      · infer_instance
  let _ := hL
  let _ := hR
  let kappa := Functor.rightDerivedUnique (RF ⋙ rY) (rX ⋙ RG) etaL etaR
    (HomologicalComplex.quasiIso A (.up ℤ))
  have hkappa (M : CochainComplex A ℤ) :
      etaL.app M ≫ kappa.hom.app (DerivedCategory.Q.obj M) = etaR.app M := by
    simpa only [kappa, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Iso.refl, NatTrans.id_app, Category.id_comp] using
      (Functor.rightDerivedNatTrans_app (RF ⋙ rY) (rX ⋙ RG) etaL etaR
        (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _).hom M)
  refine ⟨kappa, ?_, ?_⟩
  · intro M
    have hh := hkappa M
    dsimp only [etaL, etaR, cc, Fc, xc, NatIso.mapHomologicalComplex,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hh
    simp only [Category.assoc] at hh
    convert! hh using 1
  · intro k hk
    apply Iso.ext
    apply Functor.rightDerived_ext (RF ⋙ rY) etaL
      (HomologicalComplex.quasiIso A (.up ℤ))
    apply NatTrans.ext
    funext M
    change etaL.app M ≫ k.hom.app (DerivedCategory.Q.obj M) =
      etaL.app M ≫ kappa.hom.app (DerivedCategory.Q.obj M)
    rw [hkappa]
    dsimp only [etaL, etaR, cc, Fc, xc, NatIso.mapHomologicalComplex,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [Category.assoc]
    convert! hk M using 1

set_option backward.isDefEq.respectTransparency.types false in
/-- Exact forgetting preserves injectives, so its derived comparison is the unique
isomorphism normalized by the underived invariant-inclusion comparison and derived units.
Source: paragraph (3), step 6
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: use the exact free-induction left adjoint to forgetting, resolve in the full
action category, and identify the two invariant complexes. Naturality of injective
resolution comparisons and the derived universal property give the displayed equation. -/
theorem forgetDerivedExist :
    ∃! e : derived A G J ⋙ (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory ≅
        (forgetResidual A G J).mapDerivedCategory ⋙ CondensedDerivedRestriction.derived A J,
      ∀ N : CochainComplex (Equivariant A (G × J)) ℤ,
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory.map
            ((unit A G J) N) ≫
          e.hom.app (DerivedCategory.Q.obj N) ≫
          (CondensedDerivedRestriction.derived A J).map
            ((forgetResidual A G J).mapDerivedCategoryFactors.hom.app N) =
        (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategoryFactors.hom.app
            (((invariants A G J).functor.mapHomologicalComplex (.up ℤ)).obj N) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (forgetInvariants A G (J := J)) (.up ℤ)).hom.app N) ≫
          (scalarUnit A J)
            (((forgetResidual A G J).mapHomologicalComplex (.up ℤ)).obj N) := by
  have := forgetResidual_preservesKInjectiveComplexes A G J
  let F := (invariants A G J).functor
  let W := (CondensedDerivedRestriction.invariants A J).functor
  let X := forgetResidual A G J
  let Y := CondensedBar.forgetAction (A := A) (G := G)
  let etaF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derived A G J :=
    { app := unit A G J
      naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f }
  let etaW : W.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ CondensedDerivedRestriction.derived A J :=
    { app := scalarUnit A J
      naturality _ _ f := W.rightDerivedFunctorUnitQ_naturality f }
  obtain ⟨e, he, -⟩ := normalizedDerivedComparison F W X Y
    X.mapDerivedCategory Y.mapDerivedCategory
    X.mapDerivedCategoryFactors Y.mapDerivedCategoryFactors
    (derived A G J) (CondensedDerivedRestriction.derived A J) etaF etaW
    (fun I hI ↦ by
      have := hI
      change IsIso (F.rightDerivedFunctorUnitQ I)
      rw [F.rightDerivedFunctorUnitQ_eq]
      infer_instance)
    (fun I hI ↦ by
      have := hI
      change IsIso (W.rightDerivedFunctorUnitQ ((X.mapHomologicalComplex (.up ℤ)).obj I))
      rw [W.rightDerivedFunctorUnitQ_eq]
      infer_instance)
    (forgetInvariants A G (J := J))
  have hnorm (N : CochainComplex (Equivariant A (G × J)) ℤ) :
      Y.mapDerivedCategory.map ((unit A G J) N) ≫
          e.hom.app (DerivedCategory.Q.obj N) ≫
          (CondensedDerivedRestriction.derived A J).map
            (X.mapDerivedCategoryFactors.hom.app N) =
        Y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj N) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (forgetInvariants A G (J := J)) (.up ℤ)).hom.app N) ≫
          (scalarUnit A J) ((X.mapHomologicalComplex (.up ℤ)).obj N) := by
    have h := congrArg (fun z ↦
      Y.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj N) ≫
        z ≫ (CondensedDerivedRestriction.derived A J).map
          (X.mapDerivedCategoryFactors.hom.app N)) (he N)
    dsimp only [etaF, etaW] at h
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at h
    convert! h using 1
    first
    | rfl
    | erw [Category.assoc, Category.assoc, ← Functor.map_comp,
        Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]
      rfl
  refine ⟨e, hnorm, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  obtain ⟨I, hI, ⟨i⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have := hI
  have : IsIso (F.rightDerivedFunctorUnitQ I) := by
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hi : e'.hom.app (DerivedCategory.Q.obj I) = e.hom.app (DerivedCategory.Q.obj I) := by
    apply (cancel_epi (Y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I))).mp
    apply (cancel_mono ((CondensedDerivedRestriction.derived A J).map
      (X.mapDerivedCategoryFactors.hom.app I))).mp
    change (Y.mapDerivedCategory.map (unit A G J I) ≫
        e'.hom.app (DerivedCategory.Q.obj I)) ≫ _ =
      (Y.mapDerivedCategory.map (unit A G J I) ≫ e.hom.app (DerivedCategory.Q.obj I)) ≫ _
    simpa only [Category.assoc] using (he' I).trans (hnorm I).symm
  apply (cancel_mono ((X.mapDerivedCategory ⋙
    CondensedDerivedRestriction.derived A J).map i.hom)).mp
  rw [← e'.hom.naturality i.hom, ← e.hom.naturality i.hom, hi]

/-- The normalized relative-to-scalar derived comparison.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgetDerived :
    derived A G J ⋙ (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory ≅
      (forgetResidual A G J).mapDerivedCategory ⋙ CondensedDerivedRestriction.derived A J :=
  Classical.choose (forgetDerivedExist A G (J := J))

variable {A G}

set_option linter.unusedSectionVars false in
/-- Forgetting G and restricting J commute by the identity of the original module maps.
Source: paragraph (3), step 6
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: both actions precompose the original action with j maps to (1,v(j)). The underlying
identity is equivariant. Faithfulness gives uniqueness and naturality. -/
theorem forgetRestrictionExist (v : J →ₜ* H) :
    ∃! e : forgetResidual A G H ⋙ inflate (R := A.toMon) v ≅
        inflate (R := A.toMon) (productMap (G := G) v) ⋙ forgetResidual A G J,
      ∀ N, (e.hom.app N).val = 𝟙 N.module := by
  let e : forgetResidual A G H ⋙ inflate (R := A.toMon) v ≅
      inflate (R := A.toMon) (productMap (G := G) v) ⋙ forgetResidual A G J :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply Subtype.ext
  exact he' N

/-- The uniquely normalized commutation of group restriction with residual forgetting.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgetRestriction (v : J →ₜ* H) :
    forgetResidual A G H ⋙ inflate (R := A.toMon) v ≅
      inflate (R := A.toMon) (productMap (G := G) v) ⋙ forgetResidual A G J :=
  Classical.choose (forgetRestrictionExist (A := A) (G := G) v)

/-- Localization of the actual residual-forgetting commutation square.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgetRestrictionDerived (v : J →ₜ* H) :
    (forgetResidual A G H).mapDerivedCategory ⋙ (inflate (R := A.toMon) v).mapDerivedCategory ≅
      (inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategory ⋙
        (forgetResidual A G J).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (forgetResidual A G H) (inflate v)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (forgetRestriction (A := A) (G := G) v) ≪≫
    Functor.mapDerivedCategoryCompIso
      (inflate (R := A.toMon) (productMap (G := G) v)) (forgetResidual A G J)

/-- Forgetting residual actions carries the actual derived restriction to scalar restriction.
Source: paragraph (3), steps 6 and 12
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: use an equivariant K-injective resolution in the Grothendieck action category.
Forgetting preserves K-injectives because its free-induction left adjoint is exact,
also on complexes. The invariant inclusions agree, so both paths have the same
normalized derived-unit equation. The right-derived universal property identifies them. -/
theorem forgetBeta (v : J →ₜ* H)
    (N : DerivedCategory.{u + 1} (Equivariant A (G × H))) :
    (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory.map
        ((beta (A := A) (G := G) v).app N) ≫
      (forgetDerived A G (J := J)).hom.app
        ((inflate (productMap (G := G) v)).mapDerivedCategory.obj N) =
    (forgetDerived A G (J := H)).hom.app N ≫
      (CondensedDerivedRestriction.groupMap A v).app
        ((forgetResidual A G H).mapDerivedCategory.obj N) ≫
      (CondensedDerivedRestriction.derived A J).map
        ((forgetRestrictionDerived (A := A) (G := G) v).hom.app N) := by
  sorry



variable (A G)

/-- Forgetting the relative cyclic comparison gives the scalar ordinary derived comparison,
with exact-functor localization identifications included in the actual formula.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def forgottenLambda {K : TotalModel A G} (C : HasComparison A G K)
    (N : CochainComplex.Plus (Equivariant A (G × Z.{u}))) :
    DerivedCategory.Q.obj
        (((CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
          (K.functor.obj N.obj)) ≅
      (CondensedDerivedRestriction.derived A Z).obj
        (DerivedCategory.Q.obj
          (((forgetResidual A G Z).mapHomologicalComplex (.up ℤ)).obj N.obj)) :=
  ((CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategoryFactors.app
      (K.functor.obj N.obj)).symm ≪≫
    (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory.mapIso
      (lambda A G C N) ≪≫
    (forgetDerived A G (J := Z)).app (DerivedCategory.Q.obj N.obj) ≪≫
    (CondensedDerivedRestriction.derived A Z).mapIso
      ((forgetResidual A G Z).mapDerivedCategoryFactors.app N.obj)

/-- Forgetting comparisons commute with the canonical shifts and triangle boundaries.
Source: paragraph (3), steps 6 and 12
(blueprint: def-sfb-relative-invariant-forgetting).
Proof: forgetting takes equivariant injective resolutions to injective resolutions, and
the same invariant complexes and cone diagrams compute both sides. The canonical
resolution comparisons commute with their signed shifts; apply their uniqueness. -/
theorem forgetDerivedShift : NatTrans.CommShift (forgetDerived A G (J := J)).hom ℤ := by
  sorry


/-- Inflate a scalar cyclic action to a trivial residual action, on the same module.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def addTrivialResidual : Equivariant A Z.{u} ⥤ Equivariant A (PUnit.{u + 1} × Z.{u}) :=
  inflate (ContinuousMonoidHom.snd PUnit.{u + 1} Z)

/-- Trivial residual inflation retains addition of maps.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
instance addTrivialResidualAdditive : (addTrivialResidual A).Additive :=
  CondensedDerivedRestriction.restrictionAdditive (A := A)
    (ContinuousMonoidHom.snd PUnit.{u + 1} Z)

/-- Trivial residual inflation retains kernels.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
instance addTrivialResidualLimits : PreservesFiniteLimits (addTrivialResidual A) :=
  CondensedDerivedRestriction.restrictionLimits (A := A)
    (ContinuousMonoidHom.snd PUnit.{u + 1} Z)

/-- Trivial residual inflation retains cokernels.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
instance addTrivialResidualColimits : PreservesFiniteColimits (addTrivialResidual A) :=
  CondensedDerivedRestriction.restrictionColimits (A := A)
    (ContinuousMonoidHom.snd PUnit.{u + 1} Z)

/-- Adding and then forgetting the trivial residual action is the original action,
with its isomorphism fixed by the identity of every underlying module map.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting).
Proof: projection after inclusion is identity on every generalized cyclic section.
The original module identity and its inverse are equivariant and natural; faithfulness
of underlying modules gives uniqueness. -/
theorem unitResidualIsoExist :
    ∃! e : addTrivialResidual A ⋙ forgetResidual A PUnit.{u + 1} Z ≅
        𝟭 (Equivariant A Z), ∀ M, (e.hom.app M).val = 𝟙 M.module := by
  let e : addTrivialResidual A ⋙ forgetResidual A PUnit.{u + 1} Z ≅
      𝟭 (Equivariant A Z) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Subtype.ext
  exact he' M

/-- The identity-normalized forgetting isomorphism for a trivial residual action.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def unitResidualIso : addTrivialResidual A ⋙ forgetResidual A PUnit.{u + 1} Z ≅
    𝟭 (Equivariant A Z) := Classical.choose (unitResidualIsoExist A)

/-- The same normalization on every bounded-below scalar action complex.
Source: paragraph (3) (blueprint: def-sfb-relative-invariant-forgetting). -/
def scalarizationIso (N : CochainComplex.Plus (Equivariant A Z.{u})) :
    ((forgetResidual A PUnit.{u + 1} Z).mapHomologicalComplex (.up ℤ)).obj
        ((addTrivialResidual A).mapCochainComplexPlus.obj N).obj ≅ N.obj :=
  (NatIso.mapHomologicalComplex (unitResidualIso A) (.up ℤ)).app N.obj

end CategoryTheory.RelativeCyclic
