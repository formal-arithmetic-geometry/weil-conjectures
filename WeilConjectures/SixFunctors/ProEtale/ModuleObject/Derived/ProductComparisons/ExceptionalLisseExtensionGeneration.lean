/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalHomComparisonNaturality
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalHomCovariantShift
public import WeilConjectures.CategoryTheory.DerivedCategory.ExternalHomTensorInterchangeShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import Mathlib.CategoryTheory.CommSq
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeTriangulated
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension

/-!
# Native locally closed lisse generators

Source: exceptional external Künneth, General coefficients, and
`det-sf-flat-model-generation` clause (3).
(blueprint: lem-trf-native-lisse-extension-generation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
open CompactificationReindexing

/-- The existing scalar-perfect locally closed generators, restricted to ctf, together
with zero objects. Adjoining zero includes the empty generating-family convention.
Source: exceptional external Künneth, General coefficients, bounded perfect lisse
models (blueprint: lem-trf-native-lisse-extension-generation). -/
def lisseExtensionGenerator {k : Type u} [Field k] (Λ : ScalarSixRing.{u})
    (X : SepFinType k) :
    ObjectProperty (ConstantModelConstructibleFiniteTor Λ.X X.obj.left) := fun K ↦
  sfbPerfectScalarGenerator Λ X.obj K.obj ∨ IsZero K

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard upperStarFromPoint CondensedRing.upperStar
  CategoryTheory.Sheaf.monoidalCategory

set_option synthInstance.maxHeartbeats 200000 in
-- The native derived-category instances require a larger synthesis budget.
set_option maxHeartbeats 3200000 in
-- Elaborating the native derived-category endpoint functors requires a larger budget.
attribute [-instance] CategoryTheory.Sheaf.monoidalCategory in
/-- Native scalar-perfect generation restricts to the full ctf category.
Source: exceptional external Künneth proof, General coefficients, final thick closure
(blueprint: lem-trf-native-lisse-extension-generation).

Proof: Let B be the native generator property in the ctf subcategory and let Q be
its thick envelope. The ambient essential image of Q is triangulated because the
inclusion is fully faithful and exact. It is retract closed: lift an ambient retract
using thickness of ctf, then use retract closure of Q. Every scalar-perfect generator
is ctf by finite-Tor stability of locally closed extension, and is in this image by
the seed inclusion. Native finite scalar generation writes K as a retract of a finite
extension of shifted scalar-perfect generators. Thus K lies in the ambient image of
Q. Lift its witnessing isomorphism through the full inclusion to conclude Q K.
-/
theorem native_lisseExtension_thickGeneration
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A]
    (hA : ∃ n : ℕ, ((ell ^ n : ℕ) : A) = 0)
    [∀ X : SepFinType k,
      (ctfPredicate (CommMon.mk (Profinite.continuousMapRingObj A)) X).IsTriangulated]
    (X : SepFinType k)
    (K : ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj A) X.obj.left) :
    (lisseExtensionGenerator (CommMon.mk (Profinite.continuousMapRingObj A)) X).triangEnvelope
      K := by
  let Λ : ScalarSixRing.{u} := CommMon.mk (Profinite.continuousMapRingObj A)
  have htors : ∃ n : ℕ, ∀ x : A, ell ^ n • x = 0 := by
    obtain ⟨n, hn⟩ := hA
    exact ⟨n, fun x ↦ by rw [nsmul_eq_mul, hn, zero_mul]⟩
  have hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X :=
    Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, htors, ⟨Iso.refl _⟩⟩
  let T := ctfPredicate Λ X
  have : T.IsTriangulated := inferInstanceAs ((ctfPredicate Λ X).IsTriangulated)
  let B := lisseExtensionGenerator Λ X
  have : B.Nonempty := ⟨0, Or.inr (isZero_zero _)⟩
  let Q := B.triangEnvelope
  obtain ⟨_, hbc⟩ := sfbAdmissibleConstructibleThickness ell Λ hΛ k X.obj
  have : (constantModelBoundedConstructible Λ.X X.obj.left).IsStableUnderRetracts := hbc
  have htor := constantModelConstructibleFiniteTor_wellDefined Λ.X X.obj.left
  have : (_root_.DerivedCategory.finiteTorAmplitude
      (ModuleRingedComparison.internalModules Λ.X X.obj.left)).IsStableUnderRetracts :=
    htor.2.2.2.2.2.2.2.2
  have : T.IsStableUnderRetracts := ⟨fun r h ↦
    ⟨(constantModelBoundedConstructible Λ.X X.obj.left).prop_of_retract r h.1,
      (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_retract r h.2⟩⟩
  have : Q.IsTriangulated := inferInstance
  let R := Q.map T.ι
  have : R.IsTriangulated := inferInstance
  have : R.IsStableUnderRetracts := by
    constructor
    rintro M N r ⟨N', hN', ⟨e⟩⟩
    let r₀ := r.trans (Retract.ofIso e.symm)
    let M' : T.FullSubcategory := ⟨M, T.prop_of_retract r₀ N'.property⟩
    let r' : Retract M' N' :=
      { i := ⟨r₀.i⟩, r := ⟨r₀.r⟩, retract := ObjectProperty.hom_ext T r₀.retract }
    exact ⟨M', Q.prop_of_retract r' hN', ⟨Iso.refl _⟩⟩
  have hgen : sfbPerfectScalarGenerator Λ X.obj ≤ R := by
    rintro M hM
    obtain ⟨S, a, ha, P, hP, ⟨e⟩⟩ := hM
    have hctf : T M := T.prop_of_iso e.symm
      (sfbPerfectLocallyClosedExtension ell Λ hΛ k X.obj S a ha P hP)
    let M' : T.FullSubcategory := ⟨M, hctf⟩
    exact ⟨M', B.le_triangEnvelope M'
      (Or.inl ⟨S, a, ha, P, hP, ⟨e⟩⟩), ⟨Iso.refl _⟩⟩
  obtain ⟨n, hn⟩ := sfbFiniteScalarGeneration (Λ := Λ) A
    (Iso.refl (Mon.mk (Profinite.continuousMapRingObj A))) X.obj K
  have hclosed : (((sfbPerfectScalarGenerator Λ X.obj).shiftClosure ℤ).extensionProductIter n
      ).retractClosure ≤ R := by
    apply (ObjectProperty.retractClosure_le_iff _ R).mpr
    apply ObjectProperty.extensionProductIter_le_of_isTriangulatedClosed₂
    exact (ObjectProperty.shiftClosure_le_iff _ R).mpr hgen
  obtain ⟨K', hK', ⟨e⟩⟩ := hclosed K.obj hn
  exact Q.prop_of_iso (T.isoMk e) hK'

end AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
