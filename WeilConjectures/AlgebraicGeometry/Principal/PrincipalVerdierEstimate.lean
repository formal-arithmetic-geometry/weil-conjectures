/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

import WeilConjectures.AlgebraicGeometry.Principal.PrincipalDualizingReduction
import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.VerdierDualBound

/-! # One finite-level Verdier estimate for integral coefficients -/

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

section IntegralVerdierFiniteSteps
variable {Λ : Type (u + 1)} [CommRing Λ]
  {r : Λ} (hr : r ∈ nonZeroDivisors Λ) (m : ℕ) (hm : 1 ≤ m)
  [Finite (Λ ⧸ Ideal.span {r ^ m})] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ Ideal.span {r ^ m}) (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
  [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
  (W : DerivedCategoryModule Λ X)
  (eW : W ≅ (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
    (constantComplex Λ (Spec (.of k))))
  {K : DerivedCategoryModule Λ X} {a b : ℤ}
  (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
    ((reductionModIdeal Λ X (Ideal.span {r ^ m})).obj K))
  (ht : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
    ((reductionModIdeal Λ X (Ideal.span {r ^ m})).obj K))

include hr eW hbc ht in
end IntegralVerdierFiniteSteps
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The source coefficient extension, abbreviated only inside this proof module. -/
private noncomputable abbrev ivExtension {R : Type (u + 1)} [CommRing R]
    (r : R) (m : ℕ) (X : Scheme.{u}) :
    DerivedCategoryModule R X ⥤ DerivedCategoryModule (R ⧸ Ideal.span {r ^ m}) X :=
  derivedExtendScalars (Ideal.Quotient.mk_surjective (I := Ideal.span {r ^ m})) Ideal.mk_ker X

/-- The actual source coefficient restriction. -/
private noncomputable abbrev ivRestriction {R : Type (u + 1)} [CommRing R]
    (r : R) (m : ℕ) (X : Scheme.{u}) :
    DerivedCategoryModule (R ⧸ Ideal.span {r ^ m}) X ⥤ DerivedCategoryModule R X :=
  Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk _)

/-- Restriction of derived coefficient extension is ordinary reduction. -/
private lemma iv_restrictionExtension {R : Type (u + 1)} [CommRing R]
    (r : R) (m : ℕ) (X : Scheme.{u}) (K : DerivedCategoryModule R X) :
    Nonempty ((ivRestriction r m X).obj ((ivExtension r m X).obj K) ≅
      (reductionModIdeal R X (Ideal.span {r ^ m})).obj K) := by
  obtain ⟨e⟩ := nonempty_iso_derivedRestrictScalars_derivedExtendScalars
    (Ideal.Quotient.mk_surjective (I := Ideal.span {r ^ m})) Ideal.mk_ker X K
  let eQ := (Submodule.quotEquivOfEq _ _
    (Ideal.mk_ker (I := Ideal.span {r ^ m}))).toModuleIso
  exact ⟨e ≪≫ ((derivedTensor (ModuleCat.{u + 1} R) X).obj K).mapIso
    ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).mapIso eQ))⟩

/-- Compare the named derived Homs without unfolding the closed structures. -/
private lemma iv_reducedHom {R : Type (u + 1)} [CommRing R]
    {r : R} (hr : r ∈ nonZeroDivisors R) (m : ℕ) (X : Scheme.{u})
    (K W : DerivedCategoryModule R X) :
    Nonempty ((reductionModIdeal R X (Ideal.span {r ^ m})).obj
        (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj W) ≅
      (ivRestriction r m X).obj
        (((derivedHom (ModuleCat.{u + 1} (R ⧸ Ideal.span {r ^ m})) X).obj
          (op ((ivExtension r m X).obj K))).obj
            ((ivExtension r m X).obj W))) := by
  let P (J : Ideal R) := Nonempty ((reductionModIdeal R X J).obj
    (((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj W) ≅
      ((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj
        ((reductionModIdeal R X J).obj W))
  have h : P (Ideal.span {r ^ m}) :=
    (congrArg P (pow_one (Ideal.span {r ^ m}))).mp
      (nonempty_iso_reductionModIdeal_derivedHom_obj (pow_mem hr m) 1 K W)
  obtain ⟨e⟩ := h
  obtain ⟨eW⟩ := iv_restrictionExtension r m X W
  exact ⟨e ≪≫ ((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).mapIso eW.symm ≪≫
    (derivedHomRestrictScalarsIso Ideal.Quotient.mk_surjective Ideal.mk_ker X K).app
      ((ivExtension r m X).obj W)⟩

/-- The finite Verdier functor uses the named derived Hom. -/
private lemma iv_verdierDual_obj (B : Type (u + 1)) [CommRing B] [Finite B]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (M : DerivedCategoryModule B X) :
    (verdierDual B f).obj (op M) =
      ((derivedHom (ModuleCat.{u + 1} B) X).obj (op M)).obj (dualizingComplex B f) := rfl

/-- Constructibility and the exact restricted-coefficient Tor estimate for one reduction.

Source: latest blueprint, thm-coef-integral-verdier.proof.md, paragraph 1.
(blueprint: lem-k7-principal-verdier-estimate)

Proof: restriction of derived extension is the given reduction, so its constructibility
transfers to the quotient category and its Tor interval becomes [a+1,b]. Identify the
extended dualizing object by principalDualizingReduction. Hom reduction followed by the
scalar Hom adjunction identifies the reduction of Hom(K,W) with the restricted finite
Verdier dual of the extension of K. Finite Verdier duality gives [-b-2d,-a-1] over the
quotient. Restriction adds the degree -1 coefficient term and gives [-b-2d-1,-a-1].
Transport both properties through these isomorphisms. The source Tor lemmas allow
reversed intervals and the zero quotient, so no ordering or nonzero-quotient assumption
is required. -/
theorem principalVerdierEstimate (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        ((reductionModIdeal Λ X (Ideal.span {r ^ m})).obj
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj W)) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X
      (-b - 2 * (d : ℤ) - 1) (-a - 1)
      ((reductionModIdeal Λ X (Ideal.span {r ^ m})).obj
          (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj W)) := by
  let B := Λ ⧸ Ideal.span {r ^ m}
  let E := ivExtension r m X
  let U := ivRestriction r m X
  obtain ⟨eK⟩ := iv_restrictionExtension r m X K
  have hKbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} B) X (E.obj K) :=
    (boundedConstructible_derivedRestrictScalars_iff (Ideal.span {r ^ m}) _).1
      ((DerivedCategory.boundedConstructible _ X).prop_of_iso eK.symm hbc)
  have hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) X (a + 1) b (E.obj K) := by
    apply torAmplitudeIn_derivedExtendScalars Ideal.Quotient.mk_surjective Ideal.mk_ker
      (pow_mem hr m)
    let eQ := (Submodule.quotEquivOfEq _ _
      (Ideal.mk_ker (I := Ideal.span {r ^ m}))).toModuleIso
    let e := ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso eQ))
    exact (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm ht
  obtain ⟨w⟩ := principalDualizingReduction hr m aX W eW
  obtain ⟨eH⟩ := iv_reducedHom hr m X K W
  let eFin := ((derivedHom (ModuleCat.{u + 1} B) X).obj (op (E.obj K))).mapIso w
  let eV := eqToIso (iv_verdierDual_obj B aX (E.obj K)).symm
  let e := eH ≪≫ U.mapIso (eFin ≪≫ eV)
  have hfin := boundedConstructible_and_torAmplitudeIn_verdierDual_of_isAlgClosed B aX d hd
    hKbc hKt
  have hres := torAmplitudeIn_derivedRestrictScalars Ideal.Quotient.mk_surjective Ideal.mk_ker
    (pow_mem hr m) hfin.2
  exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso e.symm
      ((boundedConstructible_derivedRestrictScalars_iff (Ideal.span {r ^ m}) _).2 hfin.1),
    (DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso e.symm
      (hres.mono (by omega) (by omega))⟩

end AlgebraicGeometry.Etale
