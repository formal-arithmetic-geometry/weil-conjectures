/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFreeTensorLinear
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Strict Weil complexes with actual condensed coefficients

Source: latest blueprint, part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
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

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Geometric Frobenius on any model, without a finite-type restriction.
Source: latest blueprint, semilinear automorphism paragraph
(blueprint: sk-def-sf-weil-complexes). -/
def modelFrobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) :
    Aut (pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) :=
  letI := Fintype.ofFinite D.k₀
  { hom := D.galoisMap T₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
    inv := D.galoisMap T₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
    hom_inv_id := (D.galoisMap_inverse T₀.hom _).1
    inv_hom_id := (D.galoisMap_inverse T₀.hom _).2 }

/-- The exact module inverse image, applied termwise and localized.
Source: latest blueprint, P_T paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev action {T : Scheme.{u}} (g : T ≅ T) :=
  (upperStar Λ g.hom).mapDerivedCategory

/-- An automorphism reindexes stratifications and preserves and reflects each Tor interval.
Source: latest blueprint, P_T paragraph (blueprint: sk-def-sf-weil-complexes).
Proof: inverse image along g and its inverse are exact inverse monoidal equivalences.
They transport covering families, finite scalar local models and locally closed strata.
Exactness commutes with homology, so bounded constructibility is preserved and reflected.
The tensorator identifies tensoring a pulled-back complex with a test module with the
pullback of the tensor with the inverse-pulled-back test module. Exactness preserves the
same vanishing interval; apply the inverse equivalence for the converse. -/
theorem action_preserves {T : Scheme.{u}} (g : T ≅ T)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
    (constantModelBoundedConstructible Λ T ((action Λ g).obj K) ↔
      constantModelBoundedConstructible Λ T K) ∧
    (∀ a b : ℤ, DerivedCategory.torAmplitudeIn _ a b ((action Λ g).obj K) ↔
      DerivedCategory.torAmplitudeIn _ a b K) := by
  sorry

/-- The restriction of exact Frobenius inverse image to Dctf.
Source: latest blueprint, P_T paragraph (blueprint: sk-def-sf-weil-complexes).
Proof: use action_preserves on bounded constructibility and on the single finite
Tor interval witnessing finite Tor amplitude. -/
theorem action_mem {T : Scheme.{u}} (g : T ≅ T)
    (K : ConstantModelConstructibleFiniteTor Λ T) :
    (constantModelBoundedConstructible Λ T ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L) ((action Λ g).obj K.obj) := by
  sorry

/-- Frobenius pullback as an endofunctor of the actual Dctf full subcategory.
Source: latest blueprint, P_T paragraph (blueprint: sk-def-sf-weil-complexes). -/
def smallAction {T : Scheme.{u}} (g : T ≅ T) :
    ConstantModelConstructibleFiniteTor Λ T ⥤ ConstantModelConstructibleFiniteTor Λ T :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ action Λ g) (action_mem Λ g)

/-- Strict pairs, with exactly the recorded commuting morphisms, identities and composition.
No smooth map is data of a pair. The admissible coefficient stages are all specializations
of this construction for a commutative condensed ring.
Source: latest blueprint, strict-pair paragraphs (blueprint: sk-def-sf-weil-complexes). -/
abbrev Complex {T : Scheme.{u}} (g : T ≅ T) :=
  CategoryTheory.Endofunctor.IsoAlgebra (smallAction Λ g)

/-- The faithful forgetful functor of strict pairs.
Source: latest blueprint, pair category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev forget {T : Scheme.{u}} (g : T ≅ T) :=
  CategoryTheory.Endofunctor.IsoAlgebra.forget (smallAction Λ g)

/-- Native Weil modules are the abelian fixed pairs before deriving.
Source: latest blueprint, native category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev WeilModule {T : Scheme.{u}} (g : T ≅ T) :=
  WeilConjectures.condensedWeilModules Λ g.hom

section Native

open CategoryTheory.Endofunctor.IsoAlgebra

variable {T : Scheme.{u}} (g : T ≅ T)

/-- Bounded native derived Weil modules with constructible underlying cohomology.
Source: latest blueprint, native category paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev Native :=
  WeilConjectures.condensedWeilComplex Λ g.hom

/-- The canonical ambient comparison localizes the termwise structure, without a choice.
Source: latest blueprint, K maps to (For K, theta_K)
(blueprint: sk-def-sf-weil-complexes). -/
def ambientComparison : DerivedCategory (WeilModule Λ g) ⥤
    CategoryTheory.Endofunctor.IsoAlgebra (action Λ g) :=
  { obj K := CategoryTheory.Endofunctor.IsoAlgebra.mk
      ((WeilConjectures.condensedWeilModuleForget Λ g.hom).mapDerivedCategory.obj K)
      ((WeilConjectures.condensedWeilDerivedStructure Λ g.hom).app K)
    map f := ObjectProperty.homMk
      { f := (WeilConjectures.condensedWeilModuleForget Λ g.hom).mapDerivedCategory.map f
        h := (WeilConjectures.condensedWeilDerivedStructure Λ g.hom).hom.naturality f } }

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
  ObjectProperty.lift _ ((WeilConjectures.condensedWeilComplexProperty Λ g.hom).ι ⋙
      (CategoryTheory.Endofunctor.IsoAlgebra.forget (upperStar Λ g.hom)).mapDerivedCategory)
    (fun K ↦ by simpa [ambientComparison] using native_mem Λ g ell hΛ K)

/-- The comparison sends K to (For K, theta_K), using the localized termwise isomorphism.
Source: latest blueprint, displayed native-to-strict comparison
(blueprint: sk-def-sf-weil-complexes). -/
def nativeComparison (ell : ℕ) [Fact ell.Prime] [IsNoetherian T]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    Native Λ g ⥤ Complex Λ g :=
  { obj K := CategoryTheory.Endofunctor.IsoAlgebra.mk
      ((nativeForget Λ g ell hΛ).obj K)
      (ObjectProperty.isoMk _
        ((WeilConjectures.condensedWeilDerivedStructure Λ g.hom).app K.obj))
    map f := ObjectProperty.homMk
      { f := (nativeForget Λ g ell hΛ).map f
        h := ObjectProperty.hom_ext _
          ((WeilConjectures.condensedWeilDerivedStructure Λ g.hom).hom.naturality f.hom) } }

end Native

/-- The ambient dual is the recorded relative derived internal Hom into the coefficient unit.
Source: latest blueprint, contragredient paragraph (blueprint: sk-def-sf-weil-complexes). -/
abbrev dual {T : Scheme.{u}} (K : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :=
  (ihom K).obj (𝟙_ _)

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
