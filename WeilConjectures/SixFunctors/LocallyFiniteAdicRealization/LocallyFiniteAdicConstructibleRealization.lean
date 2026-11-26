/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientBasicSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SixFunctors.ProEtale.Adic.Truncation

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicRealizationData

import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicNormalizedFunctor
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicFunctorDescent
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicConstructibleSmall
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Algebra.CharP.Basic

/-! # Assembly of ordinary native constructible realization

Ordinary common-field constructible realization in the native locally finite adic
coefficient sheaf, for every finite-type scheme over the chosen algebraic closure.

## Implementation details

The existing realization definitions are reexported unchanged from the data module.

The condensed algebraic-closure coefficient is the sheafification of functions valued in
one finite coefficient field, hence the native locally finite function sheaf. At a finite
field the continuous rational derived realization is fully faithful; the finite-stage
realizations descend to the common-field pair category, and the Hom-colimit bijection
gives full faithfulness at the algebraic closure. Essential smallness comes from
constructible-module counting and bounded Postnikov towers.

## References

* [Bhatt--Scholze, Section 6.8, Lemma 6.8.2, Definitions 6.8.3 and 6.8.8,
  Proposition 6.8.14]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

/-- Ordinary common-field constructible realization in the native locally finite adic
coefficient sheaf, for every finite-type scheme over the chosen algebraic closure.
No separatedness is required and no individual finite stage is asserted equivalent. -/
theorem locally_finite_adic_constructible_realization
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k]
    [Algebra k₀ k] [IsAlgClosure k₀ k]
    (l : ℕ) [Fact l.Prime] (hl : l ≠ ringChar k₀)
    (T : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    Nonempty (Realization l T.left) := by
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  have : IsNoetherian T.left := ⟨⟩
  have : Fact (∃ n : ℕ, topologicalKrullDim T.left ≤ n) :=
    ⟨exists_topologicalKrullDim_le T.hom⟩
  have h₀ : IsUnit (l : k₀) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime k₀
      (Fact.out : l.Prime) hl.symm)
  have hk : IsUnit (l : k) := by
    simpa only [map_natCast] using h₀.map (algebraMap k₀ k)
  have : Fact (∀ x : T.left, IsUnit (l : T.left.presheaf.stalk x)) := ⟨by
    intro x
    simpa only [map_natCast] using hk.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ T.hom.appTop) ≫
        T.left.presheaf.germ ⊤ x trivial).hom⟩
  obtain ⟨D⟩ := normalizedFunctor_exists l T.left
  obtain ⟨hhom, himage⟩ := normalizedFunctor_descent l T.left D
  have : D.J.Full := ⟨fun {K L} ↦ (hhom K L).surjective⟩
  have : D.J.Faithful := ⟨fun {K L} ↦ (hhom K L).injective⟩
  have ht := nativeConstructible_essentiallySmall l T.left
  let P := ProEtale.DerivedCategory.boundedAdicConstructible l T.left
  let F := P.lift D.J (fun A ↦ (himage (D.J.obj A)).mpr ⟨A, ⟨Iso.refl _⟩⟩)
  have hs : EssentiallySmall.{u + 1}
      (generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.left) :=
    essentiallySmall_of_fully_faithful F
  exact ⟨{
    commutative := D.commutative
    sectionsAdditive := D.sectionsAdditive
    sectionsLimits := D.sectionsLimits
    sectionsColimits := D.sectionsColimits
    coefficient := D.coefficient
    coefficient_scalar := D.coefficient_scalar
    J := D.J
    additive := D.additive
    shift := D.shift
    triangulated := D.triangulated
    fully_faithful := hhom
    image := himage
    integral := D.integral
    sourceSmall := hs
    targetSmall := ht
    common_field := D.common_field }⟩

end WeilConjectures.LocallyFiniteAdicRealization
