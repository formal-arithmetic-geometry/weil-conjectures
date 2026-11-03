/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierScalars
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

/-! # The native and continuous Hom scalar actions agree

Source: current blueprint, sk-prop-sp-rational-adjunction.proof.md, paragraph (1),
constant-scalar linearity of the integral and rational Hom comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RationalLocalizedHom

attribute [local instance 2000] CategoryTheory.Linear.homModule

set_option maxHeartbeats 1000000 in
-- Normalize the explicit coefficient chart and its two monoidal adjunctions.
private theorem constantSections_chart (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (a : A) :
    Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map (Profinite.continuousMapConstRingHom A a).hom ≫
          chartComparison X A =
      (Sheaf.ringHomΓSheafCompose (Scheme.ProEt.topology X)
        (continuousMapRingSheaf X A)
        (fun _ ↦
          { toFun := fun b ↦ ULift.up (ContinuousMap.const _ b)
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl })
        (fun _ _ ↦ rfl) a).hom := by
  let t := (Sheaf.ringHomΓSheafCompose (Scheme.ProEt.topology X)
    (continuousMapRingSheaf X A)
    (fun _ ↦
      { toFun := fun b ↦ ULift.up (ContinuousMap.const _ b)
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })
    (fun _ _ ↦ rfl) a).hom
  change _ = t
  let F := upperStarFromPoint X
  let G := lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : adj.IsMonoidal := Adjunction.isMonoidal_comp _ _
  have hu : adj.unit.app (𝟙_ _) = Functor.LaxMonoidal.ε G ≫
      G.map (Functor.LaxMonoidal.ε F) := by
    have h := NatTrans.IsMonoidal.unit (τ := adj.unit)
    change 𝟙 _ ≫ adj.unit.app (𝟙_ _) = Functor.LaxMonoidal.ε G ≫
      G.map (Functor.LaxMonoidal.ε F) at h
    simpa only [Category.id_comp] using h
  dsimp only [F, G, upperStarFromPoint] at hu
  apply (cancel_epi (inv (Functor.LaxMonoidal.ε F))).1
  dsimp only [F]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  apply (adj.homEquiv _ _).injective
  dsimp only [upperStarFromPoint]
  rw [adj.homEquiv_naturality_left]
  simp only [chartComparison, adj, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit, hu, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, IsIso.hom_inv_id, Functor.map_id,
    Category.id_comp]
  apply Sheaf.hom_ext_of_ε_comp
  rw [Functor.map_comp, ← Category.assoc]
  dsimp only [Profinite.continuousMapConstRingHom]
  rw [Sheaf.ε_comp_ringHomΓSheafCompose_hom (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheaf A) (Profinite.continuousMapConstSectionRingHom A)
    (fun _ _ ↦ rfl) a]
  simp only [Functor.LaxMonoidal.comp_ε, Functor.map_comp, Functor.comp_map,
    Functor.map_id, Category.comp_id, Category.id_comp]
  ext S n
  change _ = ((Functor.LaxMonoidal.ε
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1})).app S ≫
    (Functor.LaxMonoidal.ε pointLowerStar).hom.app S ≫
    (Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} (toSpecZ X))).hom.app
      (op (profiniteToProEt.obj S.unop)) ≫
    t.hom.app (op ((profiniteToProEtOf X).obj S.unop))) n
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc,
    Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  change _ = ((Functor.LaxMonoidal.ε
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫ t.hom).app
      (op ((profiniteToProEtOf X).obj S.unop))) n
  have ht := Sheaf.ε_comp_ringHomΓSheafCompose_hom (Scheme.ProEt.topology X)
    (continuousMapRingSheaf X A)
    (fun _ ↦
      { toFun := fun b ↦ ULift.up (ContinuousMap.const _ b)
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })
    (fun _ _ ↦ rfl) a
  change Functor.LaxMonoidal.ε
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫ t.hom = _ at ht
  rw [ht]
  rfl

set_option maxHeartbeats 1000000 in
-- The explicit encoding contains several coefficient equivalences.
private theorem continuousEncoding_linear (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    letI := Mod.linearOfRingHom
      ((MonObj.Γ.mapFunctor (upperStarFromPoint X)
        (R := Profinite.continuousMapRingObj A)).comp
          (Profinite.continuousMapConstRingHom A))
    (CondensedRing.continuousRingModuleEquivalence X A).functor.Linear A := by
  letI := Mod.linearOfRingHom
    ((MonObj.Γ.mapFunctor (upperStarFromPoint X)
      (R := Profinite.continuousMapRingObj A)).comp
        (Profinite.continuousMapConstRingHom A))
  apply (Functor.linear_iff A _).2
  intro M a
  rw [Mod.linearOfRingHom_smul_id]
  ext U x
  let t := (Sheaf.ringHomΓSheafCompose (Scheme.ProEt.topology X)
    (continuousMapRingSheaf X A)
    (fun _ ↦
      { toFun := fun b ↦ ULift.up (ContinuousMap.const _ b)
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })
    (fun _ _ ↦ rfl) a).hom
  let φ := chartComparison X A
  let σ := (((MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
    (Profinite.continuousMapConstRingHom A)) a).hom
  have hconst : σ ≫ φ = t := constantSections_chart X A a
  have ht : t ≫ inv φ = σ := by
    rw [← hconst]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  let M' := (Mod.comap (inv φ)).obj M
  have hg : Mod.globalSmul σ M = Mod.globalSmul t M' := by
    dsimp only [M']
    rw [Mod.globalSmul_comap, ht]
  change ((Mod.globalSmul
    (((MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
      (Profinite.continuousMapConstRingHom A)) a).hom M).hom.app U) x = _
  change ((Mod.globalSmul σ M).hom.app U) x = _
  rw [hg]
  change (((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
    (Mod.globalSmul t M')).app U) x = _
  rw [← Mod.globalSmul_mapMod]
  dsimp only [t]
  rw [Sheaf.ε_comp_ringHomΓSheafCompose_hom]
  change ((((1 : ℤ) : ULift.{u + 1} C(U.unop.left, A)) *
    ULift.up (ContinuousMap.const _ a)) • x) =
      (ULift.up (ContinuousMap.const _ a) : ULift.{u + 1} C(U.unop.left, A)) • x
  rw [Int.cast_one, one_mul]

/-- The continuous-encoding Hom action equals the derived global-section action.
Source: sk-prop-sp-rational-adjunction.proof.md, paragraph (1), scalar linearity.
Proof: the monoidal point adjunction and the explicit chart identify constant
coefficient sections. Restriction along the inverse chart and the presheaf module
encoding then preserve multiplication by those sections, computed on each section.
The exact encoding is therefore linear. Its derived functor remains linear, and
full faithfulness identifies the two Hom actions, including on unbounded objects.
The argument also applies to zero rings, zero complexes and empty schemes.
(blueprint: lem-sp-native-continuous-scalar-action). -/
theorem nativeContinuousScalarAction (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TotallyDisconnectedSpace A] :
    letI := Mod.linearOfRingHom
      ((MonObj.Γ.mapFunctor (upperStarFromPoint X)
        (R := Profinite.continuousMapRingObj A)).comp
          (Profinite.continuousMapConstRingHom A))
    ∀ {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))}
      (h : K ⟶ L) (a : A),
      @SMul.smul A (K ⟶ L) (homModule X A K L).toSMul a h = a • h := by
  letI := Mod.linearOfRingHom
    ((MonObj.Γ.mapFunctor (upperStarFromPoint X)
      (R := Profinite.continuousMapRingObj A)).comp
        (Profinite.continuousMapConstRingHom A))
  haveI := continuousEncoding_linear X A
  haveI : (encoding X A).functor.Linear A := by
    change Functor.Linear A
      (CondensedRing.continuousRingModuleEquivalence X A).functor.mapDerivedCategory
    infer_instance
  intro K L h a
  apply (encoding X A).functor.map_injective
  exact (((encoding X A).fullyFaithfulFunctor.homEquiv).apply_symm_apply _).trans
    (Functor.map_smul (encoding X A).functor a h).symm

end AlgebraicGeometry.ProEtale.RationalLocalizedHom
