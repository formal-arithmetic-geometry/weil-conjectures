/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Endofunctor.DerivedFixedPairRealization
public import WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Strict Weil complexes with actual condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/_section.md (blueprint: sk-def-sf-weil-complexes).

The category is the recorded fixed-pair category on the recorded finite-constant-model
Dctf. Its dual data live in the ambient derived category. No triangulated structure
on strict pairs, or automatic constructibility of duals, is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The inverse of the exact derived action is pullback by the inverse automorphism.
Source: latest blueprint, inverse and monoidal equivalence clauses
(blueprint: sk-def-sf-weil-complexes).
Proof: inverse image composition and identity comparisons give both functor isomorphisms
on modules. Exact-functor localization descends them to the ordinary derived categories. -/
theorem action_inverse {T : Scheme.{u}} (g : T ≅ T) :
    Nonempty (action Λ g ⋙ action Λ g.symm ≅ 𝟭 _) ∧
    Nonempty (action Λ g.symm ⋙ action Λ g ≅ 𝟭 _) := by
  sorry

section Native

open CategoryTheory.Endofunctor.IsoAlgebra

variable {T : Scheme.{u}} (g : T ≅ T) [HasDerivedCategory.{w} (WeilModule Λ g)]

/-- For field coefficients the native underlying object belongs to the recorded Dctf.
Source: latest blueprint, field-coefficient comparison paragraph
(blueprint: sk-def-sf-weil-complexes).
Proof: exact forgetting commutes with homology and the standard truncations, so preserves
boundedness and the finite-constant-model constructibility condition. Over a field each
constructible cohomology object has Tor amplitude zero; boundedness supplies one common
finite interval. This is the field case of integral_ctf_equals_bc. -/
theorem native_mem (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (K : Native Λ g) :
    (constantModelBoundedConstructible Λ T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L)
      (((ambientComparison Λ g).obj K.obj).carrier) := by
  sorry

/-- The specified termwise forgetful functor, restricted to the finite-Tor subcategory.
Source: latest blueprint, For in the displayed comparison
(blueprint: sk-def-sf-weil-complexes). -/
def nativeForget (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    Native Λ g ⥤ ConstantModelConstructibleFiniteTor Λ T :=
  ObjectProperty.lift _ ((fixedPairRealizationSource (upperStar Λ g.hom)
    (IsConstantModelConstructible Λ T)).ι ⋙
      (CategoryTheory.Endofunctor.IsoAlgebra.forget (upperStar Λ g.hom)).mapDerivedCategory)
    (native_mem Λ g ell hΛ)

/-- The comparison sends K to (For K, theta_K), using the localized termwise isomorphism.
Source: latest blueprint, displayed native-to-strict comparison
(blueprint: sk-def-sf-weil-complexes). -/
def nativeComparison (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    Native Λ g ⥤ Complex Λ g :=
  lift (nativeForget Λ g ell hΛ)
    (NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _
        ((cyclicDerivedStructure (upperStar Λ g.hom)).app K.obj))
      (fun f ↦ ObjectProperty.hom_ext _
        ((cyclicDerivedStructure (upperStar Λ g.hom)).hom.naturality f.hom)))

end Native

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- Signed ordinary Tate sheaves, built from the recorded coefficient line and its dual.
The coefficient presentation c runs through all admissible stages, including finite
rings (the zero ring as well), integral coefficients and the algebraic closure.
Source: latest blueprint, actual signed Tate sheaves
(blueprint: sk-def-sf-weil-complexes). -/
def tateLine (T : Scheme.{u}) : ℤ →
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (c.obj ell) T)
  | .ofNat n => c.line ell T n
  | .negSucc n => (ihom (c.line ell T (n + 1))).obj (𝟙_ _)

/-- The actual Tate sheaf placed in degree zero.
Source: latest blueprint, Tate sheaves in degree zero (blueprint: sk-def-sf-weil-complexes). -/
def derivedTateLine (T : Scheme.{u}) (r : ℤ) : c.derived ell T :=
  (DerivedCategory.singleFunctor _ 0).obj (tateLine ell c T r)

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil
