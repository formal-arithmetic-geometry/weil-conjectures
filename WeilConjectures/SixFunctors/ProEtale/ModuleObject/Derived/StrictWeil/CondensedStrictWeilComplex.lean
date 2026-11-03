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
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFiniteLines

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

/-- The strict Weil category on any model over the stated global finite field.
The admissibility witness is the recorded coefficient notion, not a new coefficient type.
Smoothness of a morphism between models adds no datum to this category.
Source: latest blueprint, definition and first context paragraph
(blueprint: sk-def-sf-weil-complexes). -/
abbrev modelComplex (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (_hΛ : IsAdmissibleCoefficient Λ) (T₀ : Over (Spec (.of D.k₀))) :=
  Complex Λ (modelFrobenius D T₀)

/-- The faithful forgetful functor of strict pairs.
Source: latest blueprint, pair category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev forget {T : Scheme.{u}} (g : T ≅ T) :=
  CategoryTheory.Endofunctor.IsoAlgebra.forget (smallAction Λ g)

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

/-- The ordinary coefficient unit with its coefficient-unit Weil structure.
Source: latest blueprint, phi_Lambda and the point example
(blueprint: sk-def-sf-weil-complexes). -/
def unitWeilModule {T : Scheme.{u}} (g : T ≅ T) : WeilModule Λ g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (𝟙_ _)
    (Functor.Monoidal.εIso (upperStar Λ g.hom)).symm

/-- The ambient dual is the recorded relative derived internal Hom into the coefficient unit.
Source: latest blueprint, contragredient paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev dual {T : Scheme.{u}} (K : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :=
  (ihom K).obj (𝟙_ _)

/-- The three typed arrows of the contragredient datum, with inverse in the first Hom slot.
The first arrow is the evaluation-transpose comparison for the monoidal equivalence.
Source: latest blueprint, displayed contragredient composite
(blueprint: sk-def-sf-weil-complexes). -/
def dualDatum {T : Scheme.{u}} (g : T ≅ T)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
    (phi : (action Λ g).obj K ≅ K) : (action Λ g).obj (dual Λ K) ≅ dual Λ K :=
  Functor.Monoidal.ihomObjIso (action Λ g) K (𝟙_ _) ≪≫
    (ihom ((action Λ g).obj K)).mapIso (Functor.Monoidal.εIso (action Λ g)).symm ≪≫
      (MonoidalClosed.internalHom.mapIso phi.symm.op).app (𝟙_ _)

/-- Restrict a dual datum only with its stated domain condition.
Source: latest blueprint, dual-domain qualification (blueprint: sk-def-sf-weil-complexes). -/
def dualComplex {T : Scheme.{u}} (g : T ≅ T) (K : Complex Λ g)
    (hK : (constantModelBoundedConstructible Λ T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L) (dual Λ K.carrier.obj)) : Complex Λ g :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk ⟨dual Λ K.carrier.obj, hK⟩
    (ObjectProperty.isoMk _ (dualDatum Λ g K.carrier.obj
      ((ObjectProperty.ι _).mapIso K.str)))

/-- The tensorator is included in the tensor of two ambient Weil data.
Source: latest blueprint, twisted-dual composite (blueprint: sk-def-sf-weil-complexes). -/
def tensorDatum {T : Scheme.{u}} (g : T ≅ T)
    {K L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))}
    (phi : (action Λ g).obj K ≅ K) (psi : (action Λ g).obj L ≅ L) :
    (action Λ g).obj (K ⊗ L) ≅ K ⊗ L :=
  (Functor.Monoidal.μIso (action Λ g) K L).symm ≪≫ tensorIso phi psi

/-- The existing normalized root coordinates. Their integral component is uniquely
fixed by every root projection; scalar and power components are fixed by the record's
normalization equations. No root frame or arbitrary unnormalized map is selected.
Source: latest blueprint, roots, limits and scalar extensions
(blueprint: sk-def-sf-weil-complexes). -/
def tateCoordinates {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] : LinePullCoordinates ell c g.hom :=
  Classical.choice (linePullCoordinates_nonempty ell c g.hom)

/-- Positive Tate powers use the specified scalar extension and tensorator maps.
The coordinates record includes their equality to those canonical constructions.
Source: latest blueprint, tensor and scalar-extension Tate constructions
(blueprint: sk-def-sf-weil-complexes). -/
def positiveTatePull {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (n : ℕ) :=
  (tateCoordinates ell c g).power n

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

/-- Root-normalized Frobenius on signed ordinary Tate sheaves. The negative case is
contragredient, using the canonical closed comparison, the unit and the inverse
positive Tate isomorphism in the contravariant slot.
Source: latest blueprint, tau_r (blueprint: sk-def-sf-weil-complexes). -/
def tatePull {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] :
    (r : ℤ) → (upperStar (c.obj ell) g.hom).obj (tateLine ell c T r) ≅
      tateLine ell c T r
  | .ofNat n => positiveTatePull ell c g n
  | .negSucc n =>
      Functor.Monoidal.ihomObjIso (upperStar (c.obj ell) g.hom)
          (c.line ell T (n + 1)) (𝟙_ _) ≪≫
        (ihom ((upperStar (c.obj ell) g.hom).obj (c.line ell T (n + 1)))).mapIso
          (Functor.Monoidal.εIso (upperStar (c.obj ell) g.hom)).symm ≪≫
        (MonoidalClosed.internalHom.mapIso (positiveTatePull ell c g (n + 1)).symm.op).app
          (𝟙_ _)

/-- Multiplication by q is invertible on the coefficient unit in every admissible stage.
Source: latest blueprint, q inverse in Z_ell units (blueprint: sk-def-sf-weil-complexes).
Proof: ell differs from p and q is a power of p, so q is an ell-adic unit.
Its inverse passes through each specified integral coefficient map, including a finite
quotient and the zero ring, and gives a two-sided inverse to scalar multiplication. -/
theorem cardinal_scalar_isIso (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (T : Scheme.{u}) :
    IsIso (D.q • 𝟙 (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (c.obj ell) T)))) := by
  sorry

/-- The actual Tate sheaf placed in degree zero.
Source: latest blueprint, Tate sheaves in degree zero (blueprint: sk-def-sf-weil-complexes). -/
def derivedTateLine (T : Scheme.{u}) (r : ℤ) : c.derived ell T :=
  (DerivedCategory.singleFunctor _ 0).obj (tateLine ell c T r)

/-- The termwise root-normalized Tate structure in the ambient derived category.
At r=0 it is the canonical coefficient-unit isomorphism.
Source: latest blueprint, tau_r and varphi_Lambda (blueprint: sk-def-sf-weil-complexes). -/
def tateDatum {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (r : ℤ) :
    (action (c.obj ell) g).obj (derivedTateLine ell c T r) ≅ derivedTateLine ell c T r :=
  ((upperStar (c.obj ell) g.hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (tatePull ell c g r)

/-- The typed twisted-dual datum contains the inverse tensorator before the two structures.
Source: latest blueprint, final displayed composite (blueprint: sk-def-sf-weil-complexes). -/
def twistedDualDatum {T : Scheme.{u}} (g : T ≅ T)
    [∀ x : T, Invertible (ell : T.residueField x)] (K : c.derived ell T)
    (phi : (action (c.obj ell) g).obj K ≅ K) (r : ℤ) :
    (action (c.obj ell) g).obj (dual (c.obj ell) K ⊗ derivedTateLine ell c T r) ≅
      dual (c.obj ell) K ⊗ derivedTateLine ell c T r :=
  tensorDatum (c.obj ell) g (dualDatum (c.obj ell) g K phi) (tateDatum ell c g r)

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeil
