/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.Algebra.Homology.ProperBaseChange.ConstantCoefficientScalarExtensionPresentations
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.Perfect.PerfectScalarExceptionalExtension

/-! # Dualizing objects under a regular principal coefficient quotient -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] _root_.DerivedCategory.braidedCategory'
attribute [local instance 2000] CommRing.toRing
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The regular principal quotient is perfect over its source ring. -/
private lemma iv_quotientPerfect {R : Type (u + 1)} [CommRing R]
    {r : R} (hr : r ∈ nonZeroDivisors R) (m : ℕ) :
    _root_.DerivedCategory.IsPerfectRingComplex
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r ^ m}))).obj
          (ModuleCat.of (R ⧸ Ideal.span {r ^ m}) (R ⧸ Ideal.span {r ^ m})))) := by
  let S := _root_.DerivedCategory.quotPowShortComplex (Ideal.span {r ^ m})
    (r ^ m) (Ideal.mem_span_singleton_self _) 1
  have hS : S.ShortExact :=
    _root_.DerivedCategory.quotPowShortComplex_shortExact (pow_mem hr m) rfl 1
  have hR : _root_.DerivedCategory.IsPerfect
      ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj
        (ModuleCat.of R R)) := by
    exact _root_.DerivedCategory.isPerfect_singleFunctor_obj_of_projective
      (ModuleCat.of R R) 0
  have hQ := _root_.DerivedCategory.isPerfect_obj₂_of_distTriang
    hS.singleTriangle.rotate (Pretriangulated.rot_of_distTriang _ hS.singleTriangle_distinguished)
    hR (hR.shift 1)
  change _root_.DerivedCategory.IsPerfect _
  let e := (Submodule.quotEquivOfEq _ _ (pow_one (Ideal.span {r ^ m}))).toModuleIso
  exact hQ.of_iso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso e)

/-- Extension of a dualizing object along a regular principal quotient.

Source: latest blueprint, thm-coef-integral-verdier.proof.md, paragraph 1.
(blueprint: lem-k7-principal-dualizing-reduction)

Proof: the regular two-term resolution makes the quotient perfect. The geometric
hypotheses make X Noetherian. Apply perfect scalar exceptional extension to the chosen
integral and finite adjunctions, at the coefficient unit. Uniqueness of left adjoints
identifies its scalar extension with the source derived extension of scalars. Map the
specified isomorphism from W to the integral dualizing object and compose. -/
theorem principalDualizingReduction {Λ : Type (u + 1)} [CommRing Λ]
    {r : Λ} (hr : r ∈ nonZeroDivisors Λ) (m : ℕ)
    [Finite (Λ ⧸ Ideal.span {r ^ m})] {k : Type u} [Field k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
    (W : DerivedCategoryModule Λ X)
    (eW : W ≅ (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
      (constantComplex Λ (Spec (.of k)))) :
    Nonempty ((derivedExtendScalars
      (Ideal.Quotient.mk_surjective (I := Ideal.span {r ^ m})) Ideal.mk_ker X).obj W ≅
      dualizingComplex (Λ ⧸ Ideal.span {r ^ m}) aX) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  let c := HasCompactification.compactification aX
  let φ := Ideal.Quotient.mk (Ideal.span {r ^ m})
  let aR := Adjunction.ofIsLeftAdjoint (R(aX)_![ModuleCat.{u + 1} Λ])
  let aB := rightDerivedUpperShriekAdjunction (Λ ⧸ Ideal.span {r ^ m}) aX
  obtain ⟨w⟩ := (perfectScalarExceptionalExtension φ aX c
    (iv_quotientPerfect hr m) aR aB).2.2
  let eE : derivedExtendScalars
      (Ideal.Quotient.mk_surjective (I := Ideal.span {r ^ m})) Ideal.mk_ker X ≅
        scalarExtension φ X :=
    Adjunction.leftAdjointUniq
      (derivedExtendScalarsAdjunction Ideal.Quotient.mk_surjective Ideal.mk_ker X)
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
  exact ⟨eE.app W ≪≫ (scalarExtension φ X).mapIso eW ≪≫ w⟩

end AlgebraicGeometry.Etale
