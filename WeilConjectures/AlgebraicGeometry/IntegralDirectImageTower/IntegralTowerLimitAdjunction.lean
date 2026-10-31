/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
import WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.SmoothPurity.Ringed.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
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
import WeilConjectures.SmoothPurity.Supporting.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.Cochain.CochainHomotopyComparison

/-! # Deriving the normalized integral reduction/limit adjunction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Derive a normalized ordinary reduction/limit adjunction using K-flat and K-injective
resolutions. Source: Stacks 09T5, 06YS and 07A6.
Proof: K-flat resolutions form a left resolving class. The fixed reduction counit is
invertible on this class, so its naturality proves that ordinary reduction inverts
quasi-isomorphisms between its objects. K-injective resolutions of the Grothendieck
category of strict towers construct the right derived limit. The resolving-class
adjunction theorem then gives the derived adjunction and its formula on every chain
map, with precisely the fixed counit. Ordinary normalization is retained unchanged.
(blueprint: lem-sp-integral-tower-limit-adjunction). -/
theorem limit_of_normalized_ordinary_adjunction (s : Presentation l E) (T : Scheme.{u})
    (adj : (s.reduction T).ordinary ⊣ ordinaryLimit l E s T)
    (hnorm : IsOrdinaryAdjunctionNormalized l E s T adj) :
    Nonempty (Limit l E s T) := by
  letI := (s.towers T).hasDerived
  letI := (s.towers T).grothendieck
  letI : Abelian.HasKInjectiveResolutions (spCoefficientTowers l E T) := inferInstance
  letI : (ordinaryLimit l E s T).Additive := adj.right_adjoint_additive
  let G := (s.reduction T).ordinary
  let q := HomotopyCategory.quotient (spIntegralSectionModules l E T) (.up ℤ)
  let P : Set (HomotopyCategory (spIntegralSectionModules l E T) (.up ℤ)) :=
    fun X ↦ ∃ K : CochainComplex (spIntegralSectionModules l E T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) K ∧
        q.obj K = X
  have hres : ∀ X : HomotopyCategory (spIntegralSectionModules l E T) (.up ℤ),
      ∃ (X' : HomotopyCategory (spIntegralSectionModules l E T) (.up ℤ)) (f : X' ⟶ X),
        X' ∈ P ∧ HomotopyCategory.quasiIso (spIntegralSectionModules l E T) (.up ℤ) f := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, _, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := spIntegralSectionRing l E T) K
    exact ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  obtain ⟨εh, hεh, hεapp⟩ := exists_homotopy_leftDerived_comparison G
    (s.reduction T).red (s.reduction T).counit (s.reduction T).universal
  have hinv : ∀ X Y (f : X ⟶ Y), X ∈ P → Y ∈ P →
      HomotopyCategory.quasiIso (spIntegralSectionModules l E T) (.up ℤ) f →
      IsIso ((G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map f) := by
    rintro X Y f ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hf
    obtain ⟨f, rfl⟩ := q.map_surjective f
    have : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hf
    have : IsIso (εh.app (q.obj K)) := by
      rw [hεapp]
      exact (s.reduction T).computes K hK
    have : IsIso (εh.app (q.obj L)) := by
      rw [hεapp]
      exact (s.reduction T).computes L hL
    have : IsIso ((DerivedCategory.Qh ⋙ (s.reduction T).red).map (q.map f)) := by
      change IsIso ((s.reduction T).red.map (DerivedCategory.Q.map f))
      infer_instance
    exact IsIso.of_isIso_fac_left (εh.naturality (q.map f)).symm
  obtain ⟨R, η, hR, hη⟩ := CategoryTheory.exists_derived (ordinaryLimit l E s T)
  obtain ⟨d, hd⟩ := derivedAdjunctionOfResolvingClass G (ordinaryLimit l E s T) adj
    P hres hinv (s.reduction T).red εh hεh R η hR
  refine ⟨{
    ordinaryAdjunction := adj
    ordinary_normalization := hnorm
    derived := R
    unit := η
    universal := hR
    computes := hη
    adjunction := d
    normalization := ?_ }⟩
  intro K I f
  rw [← hεapp K]
  exact hd K I f

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
