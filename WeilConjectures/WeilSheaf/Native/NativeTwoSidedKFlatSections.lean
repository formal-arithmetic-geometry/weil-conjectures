/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionComparisons
import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
import Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorRepresentatives
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgettingMonoidal
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData

/-! # Two-sided native K-flatness of the actual section complex -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients

universe u

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.MonoidalCategory
open ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance ordinary_forget_additive (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    (ProEtale.AdicSheaf.forgetAb l Y).Additive where
  map_add := by
    intro M N f g
    apply Mod.hom_ext
    ext V x
    rfl

attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem acyclic_test_map
    {M D : Type*} [Category M] [Category D] [Abelian M] [Abelian D]
    [MonoidalCategory M] [MonoidalCategory D]
    [MonoidalPreadditive M] [MonoidalPreadditive D]
    [HasCountableCoproducts M] [HasCountableCoproducts D]
    (E : M ≌ D) [E.functor.Additive] [E.functor.Monoidal]
    (P : CochainComplex M ℤ)
    (hP : ∀ N : CochainComplex M ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor N P (curriedTensor M)).Acyclic) :
    ∀ N : CochainComplex D ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor N
        ((E.functor.mapHomologicalComplex (.up ℤ)).obj P) (curriedTensor D)).Acyclic := by
  intro N hN
  let e := E.mapHomologicalComplex (.up ℤ)
  let L := e.inverse.obj N
  let i : e.functor.obj L ≅ N := e.counitIso.app N
  have hL : L.Acyclic := by
    intro n
    apply ((L.sc n).exact_map_iff_of_faithful E.functor).mp
    exact (hN n).of_iso i.symm
  have ht := (hP L hL).map E.functor
  let j := InternalAbelianSheafModule.comparison_totalIso E.functor
    (fun X Y ↦ asIso (Functor.OplaxMonoidal.δ E.functor X Y))
    (fun _ _ _ _ f g ↦ (Functor.OplaxMonoidal.δ_natural E.functor f g).symm) L P
  let T := (curriedTensor D).map₂CochainComplex
  let a := (T.mapIso i).app ((E.functor.mapHomologicalComplex (.up ℤ)).obj P)
  intro n
  exact ((ht n).of_iso j).of_iso a

set_option maxHeartbeats 2000000 in
-- Comparing the actual section complex involves three nested mapped functors.
attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem ordinary_sections_kflat (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (R : LocallyFiniteAdicRealization.RealizationCore l Y)
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
    (hP : NativeOrdinaryKFlat l Y P) :
    letI := R.commutative
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology Y) (R := LocallyFiniteAdicRealization.ringSheaf l Y)
      (((InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) (LocallyFiniteAdicRealization.abRing l Y)
          ).mapHomologicalComplex (.up ℤ)).obj
        (((ProEtale.AdicSheaf.forgetAb l Y).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let := R.commutative
  let := R.sectionsAdditive
  exact (InternalAbelianSheafModule.comparison_kflat.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Y) (LocallyFiniteAdicRealization.abRing l Y)
    (((ProEtale.AdicSheaf.forgetAb l Y).mapHomologicalComplex (.up ℤ)).obj P)).mp (by
    have : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    let U := ProEtale.AdicSheaf.forgetAb l Y
    obtain ⟨m⟩ := ProEtale.nativeScalarForgetting_monoidal l Y
    let := m
    have : U.IsEquivalence := ProEtale.nativeScalarForgetting_isEquivalence l Y
    let : U.asEquivalence.functor.Additive := ordinary_forget_additive l Y
    let : U.asEquivalence.functor.Monoidal := m
    have hright (N : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) (hN : N.Acyclic) :
        (CochainComplex.mapBifunctor N P
          (curriedTensor (ProEtale.AdicSheaf l Y))).Acyclic := by
      let j := HomologicalComplex₂.total.mapIso
        (GenericOrdinaryTensor.ordinaryBicomplexIso.{u + 2, u + 1}
          (C := Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l))
          (R := ProEtale.adicConstantSheaf l Y) P N) (.up ℤ) ≪≫
        HomologicalComplex.mapBifunctorFlipIso N P
          (curriedTensor (ProEtale.AdicSheaf l Y)) (.up ℤ)
      intro n
      exact (hP N hN n).of_iso j
    exact acyclic_test_map.{u + 2, u + 2, u + 1, u + 1} U.asEquivalence P hright
)

set_option maxHeartbeats 2000000 in
-- Comparing the actual section complex involves three nested mapped functors.
attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Two-sided native K-flatness is retained by the actual section-module functor.
Source: Stacks 06YN and BS 6.8.14
(blueprint: lem-sf-native-two-sided-kflat-sections).

Proof: the native two-sided quasi-isomorphism test implies ordinary K-flatness
by exact orbit induction and its split degree-zero summand. Forgetting ambient
scalars is an additive strong monoidal equivalence. For an acyclic internal
module complex, use its inverse image under this equivalence; faithfulness and
exactness detect its acyclicity. The natural tensor bicomplex comparison and
preservation of direct-sum totalization then transfer the acyclic tensor test.
Finally the canonical internal-module/section-module comparison transfers this
test to section modules. All functors are the existing section functors, and
mapping their composites on complexes is definitionally the same operation. -/
theorem native_two_sided_kflat_sections
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (R : LocallyFiniteAdicRealization.Realization l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (R := WeilConjectures.AdicQbarRealization.ring l _ R)
      ((properSectionCochain k₀ l X R).obj P) := by
  let := R.commutative
  let := R.sectionsAdditive
  have h := native_two_sided_kflat_forget k₀ l X P hP
  have hs := ordinary_sections_kflat l _ R.toRealizationCore _ h
  exact hs

end AlgebraicGeometry.ProEtaleWeilSheaf
