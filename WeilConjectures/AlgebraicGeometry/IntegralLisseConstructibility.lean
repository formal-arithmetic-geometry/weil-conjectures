/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.FiniteModelSheafQuotientData
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import all WeilConjectures.AlgebraicGeometry.DiagonalSupportedOrdinaryScalars
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import all Mathlib.Algebra.Homology.CochainComplexPlus
import all Mathlib.Data.Int.Interval
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import all WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import all Mathlib.Algebra.Homology.TotalComplex
import all Mathlib.CategoryTheory.Abelian.Basic
import all WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import all WeilConjectures.CategoryTheory.Triangulated.Recollement
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.Grp.Zero
import all Mathlib.Algebra.Category.Ring.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import all Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.AlgebraicGeometry.Pullbacks
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Adjunction.Triple
import all Mathlib.CategoryTheory.EffectiveEpi.Comp
import all Mathlib.CategoryTheory.Extensive
import all Mathlib.CategoryTheory.GradedObject.Bifunctor
import all Mathlib.CategoryTheory.GradedObject.Monoidal
import all Mathlib.CategoryTheory.GradedObject.Trifunctor
import all Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import all Mathlib.CategoryTheory.Limits.Preserves.Filtered
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import all Mathlib.CategoryTheory.Monad.Adjunction
import all Mathlib.CategoryTheory.Monoidal.Action.Basic
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.CommMon_
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Monoidal.Mod
import all Mathlib.CategoryTheory.Monoidal.Mon
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.CategoryTheory.Sites.Coherent.Basic
import all Mathlib.CategoryTheory.Sites.Coherent.Comparison
import all Mathlib.CategoryTheory.Sites.ConcreteSheafification
import all Mathlib.CategoryTheory.Sites.Grothendieck
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.Combinatorics.Quiver.ReflQuiver
import all Mathlib.Data.Int.ConditionallyCompleteOrder
import all Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import all Mathlib.Geometry.RingedSpace.PresheafedSpace
import all Mathlib.Geometry.RingedSpace.SheafedSpace
import all Mathlib.Topology.Category.CompHausLike.Basic
import all Mathlib.Topology.Category.CompHausLike.Limits
import all Mathlib.Topology.Category.Profinite.Basic
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Mathlib.Topology.Category.Profinite.Limits
import all Mathlib.Topology.Category.TopCat.Basic
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Mathlib.Topology.ContinuousMap.Defs
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.IntegralModelsGenerators
import all WeilConjectures.AlgebraicGeometry.ProperHeartBoundTorsion
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.DiagonalFlatScalarEndpoint

/-! # Constructibility and finite reductions of supported integral lisse modules

Source: Hemo--Richarz--Scholbach, Theorem 7.7; Bhatt--Scholze, Lemma 6.8.13;
latest blueprint, integral-models-generators proof, part (3)
(blueprint: lem-fd-integral-lisse-constructibility).

The canonical comparison is specified by the actual scalar-adjunction unit, extended
through the given open-then-closed factorization. The quotient module is ordinary scalar
extension along the actual map to O_E/pi^(n+1); hence it is L_0/pi^(n+1)L_0 with its quotient
coefficient action. The index n represents every positive exponent n+1.

## Main definitions

* `extension`: the given composite of the existing open and closed functors.
* `extensionScalarUnit`: the quotient unit transported through that composite.
* `extensionDerivedScalarMap`: its canonical derived adjunct.

## Main statements

* `integralLisse_constructibility`: integral constructibility, canonical finite reductions,
  quotient constructibility, and etale origin.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralLisseConstructibility

/-- Extension in the given factorization a = i o j, using the existing module functors.
Source: latest blueprint, integral-models-generators proof (3)
(blueprint: lem-fd-integral-lisse-constructibility). -/
abbrev extension
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S V Z : Scheme.{u}}
    (j : S ⟶ V) [IsOpenImmersion j] (i : V ⟶ Z) :=
  CondensedRing.openImmersionLowerShriek A j ⋙ CondensedRing.lowerStar A i

/-- Extend the actual scalar-adjunction unit along the given open and closed factors.
The two canonical restriction comparisons retain the quotient coefficient action.
Source: latest blueprint, integral-models-generators proof (3)
(blueprint: lem-fd-integral-lisse-constructibility). -/
def extensionScalarUnit
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S V Z : Scheme.{u}}
    (j : S ⟶ V) [IsOpenImmersion j] (i : V ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S)) :
    (extension A j i).obj M ⟶ (Mod.comap (coefficientMap c Z)).obj
      ((extension B j i).obj ((Mod.extendScalars (coefficientMap c S)).obj M)) :=
  (CondensedRing.lowerStar A i).map
    ((CondensedRing.openImmersionLowerShriek A j).map
        (Mod.extendUnit (coefficientMap c S) M) ≫
      (CondensedRing.comapOpenImmersionLowerShriekIso c j).inv.app
        ((Mod.extendScalars (coefficientMap c S)).obj M)) ≫
    (CondensedRing.comapLowerStarIso c i).inv.app
      ((CondensedRing.openImmersionLowerShriek B j).obj
        ((Mod.extendScalars (coefficientMap c S)).obj M))

/-- The canonical reduction arrow is the derived scalar/restriction adjunct of the
extended ordinary quotient unit. This fixes its normalization without choosing an iso.
Source: latest blueprint, integral-models-generators proof (3)
(blueprint: lem-fd-integral-lisse-constructibility). -/
def extensionDerivedScalarMap
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S V Z : Scheme.{u}}
    (j : S ⟶ V) [IsOpenImmersion j] (i : V ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S)) :
    (Mod.extendScalars (coefficientMap c Z)).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((extension A j i).obj M)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((extension B j i).obj ((Mod.extendScalars (coefficientMap c S)).obj M)) :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c Z)).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor _ 0).map (extensionScalarUnit c j i M) ≫
      ((Mod.comap (coefficientMap c Z)).mapDerivedCategorySingleFunctor 0).inv.app
        ((extension B j i).obj ((Mod.extendScalars (coefficientMap c S)).obj M)))

private theorem supported_constructible
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S V Z : Scheme.{u}} [IsNoetherian Z]
    (j : S ⟶ V) [IsOpenImmersion j] (i : V ⟶ Z) [IsClosedImmersion i]
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S))
    (hM : IsLisseCoefficientModule A M) :
    boundedConstructible (condensedRingObj A Z)
      ((DerivedCategory.singleFunctor _ 0).obj ((extension A j i).obj M)) := by
  have hfree : CondensedRing.LocallyFree (condensedRingObj A S) M := by
    obtain ⟨C, hC⟩ := hM
    exact ⟨C, fun t ↦ (CondensedRing.freeAt_iff_standard A (C.f t) M).mpr (hC t)⟩
  have h := WeilConjectures.SixFunctors.integralModel_extension_constructible A Z j i M hfree
  exact ⟨h.1, fun q ↦ WeilConjectures.SixFunctors.integralModel_constant_constructible
    A Z _ (h.2 q)⟩

private theorem fullyFaithful_mate_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {U : B ⥤ A} {F' : C ⥤ D} {U' : D ⥤ C}
    (a : F ⊣ U) (b : F' ⊣ U') {G : A ⥤ C} {H : B ⥤ D}
    (hG : G.FullyFaithful) (hH : H.FullyFaithful)
    (e : H ⋙ U' ≅ U ⋙ G) (M : A)
    (e₀ : F'.obj (G.obj M) ≅ H.obj (F.obj M)) :
    IsIso ((Adjunction.pushHomOfComapIso a b e).app M) := by
  let f := (Adjunction.pushHomOfComapIso a b e).app M
  let Q (N : B) : (F.obj M ⟶ N) ≃ (F'.obj (G.obj M) ⟶ H.obj N) :=
    (a.homEquiv _ _).trans (hG.homEquiv.trans
      ((Iso.homCongr (Iso.refl _) (e.app N).symm).trans (b.homEquiv _ _).symm))
  have hQ (N : B) (g : F.obj M ⟶ N) : Q N g = f ≫ H.map g := by
    apply (b.homEquiv _ _).injective
    rw [DiagonalCoefficients.scalar_push_transpose]
    simp [Q, Iso.homCongr]
  have hbij (N : B) : Function.Bijective
      (fun g : H.obj (F.obj M) ⟶ H.obj N ↦ f ≫ g) := by
    let T := (hH.homEquiv (X := F.obj M) (Y := N)).symm.trans (Q N)
    have hf : (fun g : H.obj (F.obj M) ⟶ H.obj N ↦ f ≫ g) = T.toFun := by
      funext g
      change f ≫ g = Q N (hH.preimage g)
      rw [hQ, hH.map_preimage]
    rw [hf]
    exact T.bijective
  obtain ⟨g, hg⟩ := (hbij (F.obj M)).2 e₀.hom
  let v := g ≫ e₀.inv
  have hfv : f ≫ v = 𝟙 _ := by simp [v, ← Category.assoc, hg]
  have hvf : v ≫ f = 𝟙 _ := by
    apply (hbij (F.obj M)).1
    change f ≫ (v ≫ f) = f ≫ 𝟙 _
    rw [← Category.assoc, hfv, Category.id_comp, Category.comp_id]
  exact ⟨⟨v, hfv, hvf⟩⟩

private def supported_fullyFaithful
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S V Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Z]
    (j : S ⟶ V) [IsOpenImmersion j] (i : V ⟶ Z) [IsClosedImmersion i] :
    (extension A j i).FullyFaithful := by
  have := CondensedRing.openUnitIsIso A j
  let ao := CondensedRing.openImmersionLowerShriekUpperStarAdjunction A j
  let ho := ao.fullyFaithfulLOfIsIsoUnit
  let U : Z.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have := CondensedRing.moduleCounitOfAbelian A i
    (ProEtale.abelian_closed_support i U.ι U.range_ι).1
  exact ho.comp (CondensedRing.upperStarLowerStarAdjunction A i).fullyFaithfulROfIsIsoCounit

private theorem supported_scalar_iso
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S V Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Z]
    (j : S ⟶ V) [IsOpenImmersion j] (i : V ⟶ Z) [IsClosedImmersion i]
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S)) :
    IsIso (((Mod.extendRestrictAdjunction (coefficientMap c Z)).homEquiv _ _).symm
      (extensionScalarUnit c j i M)) := by
  let e : extension B j i ⋙ Mod.comap (coefficientMap c Z) ≅
      Mod.comap (coefficientMap c S) ⋙ extension A j i :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CondensedRing.comapLowerStarIso c i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CondensedRing.comapOpenImmersionLowerShriekIso c j) _ ≪≫
      Functor.associator _ _ _
  have h := fullyFaithful_mate_iso
    (Mod.extendRestrictAdjunction (coefficientMap c S))
    (Mod.extendRestrictAdjunction (coefficientMap c Z))
    (supported_fullyFaithful A j i) (supported_fullyFaithful B j i) e M
    (WeilConjectures.SixFunctors.integralModel_extension_scalar c j i M)
  have he : ((Mod.extendRestrictAdjunction (coefficientMap c Z)).homEquiv _ _).symm
      (extensionScalarUnit c j i M) =
      (Adjunction.pushHomOfComapIso
        (Mod.extendRestrictAdjunction (coefficientMap c S))
        (Mod.extendRestrictAdjunction (coefficientMap c Z)) e).app M := by
    apply ((Mod.extendRestrictAdjunction (coefficientMap c Z)).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    have ht := DiagonalCoefficients.scalar_push_transpose
      (Mod.extendRestrictAdjunction (coefficientMap c S))
      (Mod.extendRestrictAdjunction (coefficientMap c Z)) e M _ (𝟙 _)
    have hη : (Mod.extendRestrictAdjunction (coefficientMap c S)).unit.app M =
        Mod.extendUnit (coefficientMap c S) M := by
      apply Mod.hom_ext
      exact Mod.extendRestrictAdjunction_unit_app_hom _ _
    simpa [e, extensionScalarUnit, Adjunction.homEquiv_unit, hη,
      Functor.map_comp, Category.assoc] using ht.symm
  rw [he]
  exact h

attribute [local irreducible] Functor.leftDerivedFunctor
  Mod.derivedExtendMapDerivedCategoryAdjunction

set_option maxHeartbeats 1600000 in
-- The normalized endpoint uses module-category abbreviations requiring extra defeq work.
private theorem supported_derived_scalar_iso
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S V Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Z]
    (j : S ⟶ V) [IsOpenImmersion j] (i : V ⟶ Z) [IsClosedImmersion i]
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj A S))
    (hM : IsLisseCoefficientModule A M) :
    IsIso (extensionDerivedScalarMap c j i M) := by
  have hfree : CondensedRing.LocallyFree (condensedRingObj A S) M := by
    obtain ⟨C, hC⟩ := hM
    exact ⟨C, fun t ↦ (CondensedRing.freeAt_iff_standard A (C.f t) M).mpr (hC t)⟩
  let adj := Mod.extendRestrictAdjunction (coefficientMap c Z)
  let U : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj B Z) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj A Z) :=
    Mod.comap (coefficientMap c Z)
  let q := (adj.homEquiv _ _).symm (extensionScalarUnit c j i M)
  have : IsIso q := supported_scalar_iso c j i M
  obtain ⟨e, he, _⟩ := DiagonalCoefficients.diagonal_flat_scalar_endpoint_iso c Z
    ((extension A j i).obj M)
    (WeilConjectures.SixFunctors.integralModel_extension_flat A j i M hfree)
  let d := e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso (asIso q)
  have hd : extensionDerivedScalarMap c j i M = d.hom := by
    apply ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap c Z)).homEquiv _ _).injective
    rw [extensionDerivedScalarMap, Equiv.apply_symm_apply]
    have hq : Mod.extendUnit (coefficientMap c Z) ((extension A j i).obj M) ≫
        U.map q = extensionScalarUnit c j i M :=
      (adj.homEquiv _ _).apply_symm_apply _
    dsimp only [d, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    rw [Adjunction.homEquiv_naturality_right, he, Category.assoc]
    have hn := (U.mapDerivedCategorySingleFunctor 0).inv.naturality q
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    erw [← hn, ← Functor.map_comp_assoc, hq]
    rfl
  rw [hd]
  infer_instance

/-- Supported integral lisse modules are bounded constructible; every positive finite
reduction is canonically the supported ordinary quotient in degree zero, is bounded
constructible over the quotient ring, and is the inverse image of an etale module sheaf.

Source: Hemo--Richarz--Scholbach, Theorem 7.7; Bhatt--Scholze, Lemma 6.8.13;
latest blueprint, integral-models-generators proof (3)
(blueprint: lem-fd-integral-lisse-constructibility).

Proof plan (the six steps of the node):
1. Use lem-sfb-coefficient-heart-locally-closed-extension to make the source and intermediate
scheme Noetherian and Z quasi-separated. Use lem-sfb-locally-closed-extension-coherence and
sk-prop-sfb-cartesian-coefficients to identify the given exact i_*j_! with canonical extension.
2. IsLisseCoefficientModule gives finite free local models, including rank zero. Apply
lem-sfb-scalar-model-immersion-extension to j and i. Finite free and zero models are finitely
presented, so def-sfb-constructible-module and det-def-sfb-bounded-constructible give the first
assertion, with only H^0 nonzero.
3. lem-sfb-integral-lisse-coefficient-quotients identifies the actual quotient map as the
cokernel of pi^(n+1). Transport it by lem-weil-pbc-continuous-coefficient-realizations and
lem-pe-internal-section-tensor-comparison. Apply lem-sfb-locally-free-derived-scalars to L_0:
its ordinary reduction is L_0/pi^(n+1)L_0, locally free over the actual quotient ring.
4. Apply lem-weil-pbc-proetale-closed-underived-projection and
lem-weil-pbc-ringed-slice-extension-tensor. Exactness of pullback, extension, and tensor by
L_0 shows i_*j_!L_0 is flat. lem-diagonal-flat-scalar-endpoint gives the unit-normalized derived
comparison. Compose with lem-sfb-condensed-locally-closed-scalar-extension; the canonical
restriction squares identify its adjoint with extensionScalarUnit. This proves invertibility
of the particular extensionDerivedScalarMap, without assuming the quotient ring is flat.
5. Apply lem-sfb-finite-model-sheaf-quotient-constructible to the finite constant models of
step 2 on qcqs Z. Step 4 removes degree -1; finite presentations of the remaining models give
bounded constructibility by def-sfb-constructible-module and det-def-sfb-bounded-constructible.
6. The finite quotient ring is Noetherian. Apply sk-thm-pe-constructible-comparison (Stacks
09AK) to get the etale module sheaf. The normalized section-action encoding from
lem-sf-module-object-ordinary-coefficient-equivalence keeps underlying abelian sheaves and
the actual quotient action, so its comparisonUpperStar is exactly nu_Z^* as required. -/
theorem integralLisse_constructibility
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {S V Z : Scheme.{u}}
    [CompactSpace Z] [IsLocallyNoetherian Z]
    (j : S ⟶ V) [IsOpenImmersion j] (i : V ⟶ Z) [IsClosedImmersion i]
    (L : AdicCompletion.Modules l E S)
    (hL : IsLisseCoefficientModule (DerivedNakayama.integerRing l E) L) :
    boundedConstructible (AdicCompletion.ring l E Z)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((extension (DerivedNakayama.integerRing l E) j i).obj L)) ∧
    ∀ n : ℕ,
      IsIso (extensionDerivedScalarMap (DerivedNakayama.reductionRing l E (n + 1)) j i L) ∧
      boundedConstructible (AdicCompletion.finiteRing l E Z n)
        ((AdicCompletion.derivedReduction l E Z n).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((extension (DerivedNakayama.integerRing l E) j i).obj L))) ∧
      ∃ e : FiniteModelQuotient.Encoding l E n Z,
        ∃ G : Sheaf Z.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))),
          Nonempty ((FiniteModelQuotient.fixedEncoding l E n Z e).functor.obj
              ((extension (DerivedNakayama.quotientRing l E (n + 1)) j i).obj
                ((Mod.extendScalars (AdicCompletion.quotient l E S n)).obj L)) ≅
            (comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              Z).obj G) := by
  classical
  have : IsNoetherian Z := {}
  refine ⟨supported_constructible _ j i L hL, fun n ↦ ?_⟩
  have hscalar : IsIso
      (extensionDerivedScalarMap (DerivedNakayama.reductionRing l E (n + 1)) j i L) := by
    exact supported_derived_scalar_iso _ j i L hL
  let := hscalar
  refine ⟨hscalar, ?_, ?_⟩
  · exact (boundedConstructible (AdicCompletion.finiteRing l E Z n)).prop_of_iso
      (asIso (extensionDerivedScalarMap
        (DerivedNakayama.reductionRing l E (n + 1)) j i L)).symm
      (supported_constructible _ j i _
        (scalarExtension_lisse _ _ (DerivedNakayama.reductionRing l E (n + 1)) S L hL))
  · let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    let : DiscreteTopology A := DerivedNakayama.quotientDiscrete l E (n + 1)
    let M : FiniteDiscreteOrdinary.Internal A Z :=
      (extension (DerivedNakayama.quotientRing l E (n + 1)) j i).obj
        ((Mod.extendScalars (AdicCompletion.quotient l E S n)).obj L)
    obtain ⟨enc⟩ := FiniteDiscreteOrdinary.encoding_exists A Z
    let G := (enc.ordinary.functor ⋙ enc.fixed.functor).obj M
    have hM := finiteExtension_stratified l E j i (n + 1) L hL
    have hG : FiniteDiscreteOrdinary.ordinaryStratified A Z G :=
      (FiniteDiscreteOrdinary.stratified_comparison A Z enc M).1 hM
    obtain ⟨F, _, eF⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
      (ULift.{u + 1} A) (ordinaryStratified_constructible A Z G hG)
    exact ⟨enc, F, eF.map Iso.symm⟩

end AlgebraicGeometry.ProEtale.IntegralLisseConstructibility
