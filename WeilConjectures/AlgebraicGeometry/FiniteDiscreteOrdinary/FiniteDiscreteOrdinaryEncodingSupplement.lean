/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Homology.DerivedTensor
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding

/-! # Finite discrete internal and ordinary coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-rf-shriek-preservation, coefficient-identification step
(blueprint: lem-sf-finite-discrete-normalized-encoding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

attribute [instance] Encoding.ordinaryAdditive Encoding.ordinaryInverseAdditive
  Encoding.fixedAdditive Encoding.fixedInverseAdditive

/-- The canonical shift comparison on the actual termwise derived functor.
Source: blueprint proof step 4 and Stacks 015F
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
instance Encoding.fixedDerivedShift {T : Scheme.{u}} (e : Encoding A T) :
    e.fixedDerived.functor.CommShift ℤ := by
  letI : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  letI : (e.ordinary.trans e.fixed).inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  change (e.ordinary.trans e.fixed).functor.mapDerivedCategory.CommShift ℤ
  infer_instance

private instance pointConstants_locallySurjective [Finite A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u}) (pointConstants A) where
  imageSieve_mem {S} s := by
    let f : C(S, A) := s.down
    have hclosed (a : A) : IsClosed {x : S | f x = a} :=
      isClosed_singleton.preimage f.continuous
    let (a : A) : CompactSpace {x : S // f x = a} :=
      isCompact_iff_compactSpace.mp (hclosed a).isCompact
    let := Fintype.ofFinite A
    let e := (Fintype.equivFin A).symm
    let U (i : Fin (Fintype.card A)) : Profinite.{u} :=
      Profinite.of {x : S // f x = e i}
    let incl (i : Fin (Fintype.card A)) : U i ⟶ S :=
      CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl :=
      Profinite.effectiveEpiFamily_of_jointly_surjective U incl
        (fun x ↦ ⟨e.symm (f x), ⟨x, (e.apply_symm_apply (f x)).symm⟩, rfl⟩)
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨Fin (Fintype.card A), inferInstance, U, incl, hι, ?_⟩
    intro i
    refine ⟨ULift.up (e i), ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

private instance pointConstants_locallyInjective :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u}) (pointConstants A) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (ULift.ext a b (congrArg
        (fun t : ULift.{u + 1} C(S.unop, A) ↦ t.down x) h))⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

private theorem canonicalAbelianMap_isIso [Finite A] [DiscreteTopology A] (T : Scheme.{u}) :
    IsIso (canonicalAbelianMap A T) := by
  let J := coherentTopology Profinite.{u}
  have hφ : J.W (A := Ab.{u + 1}) (pointConstants A) :=
    J.W_of_isLocallyBijective (pointConstants A)
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map (pointConstants A)) :=
    (J.W_iff _).mp hφ
  have h : ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ (coefficient A)).symm
      (pointConstants A) =
      (presheafToSheaf J Ab.{u + 1}).map (pointConstants A) ≫
        (sheafificationAdjunction J Ab.{u + 1}).counit.app (coefficient A) := rfl
  unfold canonicalAbelianMap
  rw [h]
  infer_instance

private local instance schemeConstantsTargetMonObj (T : Scheme.{u}) :
    MonObj (condensedRingObj (coefficient A) T).obj :=
  (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}).monObjObj
    (condensedRingObj (coefficient A) T)

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
