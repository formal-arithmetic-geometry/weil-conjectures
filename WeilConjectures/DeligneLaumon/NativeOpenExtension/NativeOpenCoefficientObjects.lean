/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement

/-!
# Native open coefficient objects

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-integral-adjunction/
sk-prop-sp-integral-adjunction-direct-image.proof.md,
det-sp-integral-direct-image-tower clause (2)
(blueprint: def-dla1-native-open-coefficient-objects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures
namespace NativeOpenExtension

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Owner aliases for the completed integral coefficient objects used below.
Source: sk-def-pe-derived-completion; the underlying constructions are
`DerivedNakayama.integerRingSheaf` and `DerivedNakayama.integerRing`.
(blueprint: def-dla1-native-open-coefficient-objects). -/
abbrev integerRingSheaf := DerivedNakayama.integerRingSheaf l E

/-- The underlying native condensed integral ring used by the inclusion.
Source: sk-def-pe-derived-completion
(blueprint: def-dla1-native-open-coefficient-objects). -/
abbrev integerRing := DerivedNakayama.integerRing l E

/-- The spectral topology used by the native field coefficients.
Source: coefficient convention of clause (2)
(blueprint: def-dla1-native-open-coefficient-objects). -/
abbrev fieldTopology : TopologicalSpace E :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  inferInstance

/-- The continuous field sheaf, in the same coefficient presentation as O_E.
Source: coefficient convention of clause (2)
(blueprint: def-dla1-native-open-coefficient-objects). -/
abbrev fieldRingSheaf : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingSheaf E

/-- The native condensed field ring; its multiplication is the published pointwise one.
Source: coefficient convention of clause (2)
(blueprint: def-dla1-native-open-coefficient-objects). -/
abbrev fieldRing : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (fieldRingSheaf l E)

/-- Continuous postcomposition with the actual inclusion O_E into E.
Source: clause (2), integral-to-rational scalar map
(blueprint: def-dla1-native-open-coefficient-objects). -/
def inclusionSheaf : integerRingSheaf l E ⟶ fieldRingSheaf l E :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ⟨{ app := fun _ ↦ RingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         (((Padic.coefficientExtensionIntegers l E).subtype.compLeftContinuous _
           continuous_subtype_val).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The actual native condensed-ring map O_E to E.
Source: clause (2), integral-to-rational scalar map
(blueprint: def-dla1-native-open-coefficient-objects). -/
abbrev inclusion : integerRing l E ⟶ fieldRing l E :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (inclusionSheaf l E)

/-- Finite field coefficient changes use continuous postcomposition, without a lattice choice.
Source: clause (2), E to E' scalar map
(blueprint: def-dla1-native-open-coefficient-objects). -/
def fieldMapSheaf (E' : Type u) [Field E'] [Algebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E'] (f : E →ₐ[ℚ_[l]] E')
    (hf : @Continuous E E' (fieldTopology l E) (fieldTopology l E') f) :
    fieldRingSheaf l E ⟶ fieldRingSheaf l E' :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  letI := (Padic.coefficientExtensionAbsoluteValue l E').toNormedField
  ⟨{ app := fun _ ↦ RingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         ((f.toRingHom.compLeftContinuous _ hf).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

end NativeOpenExtension

end WeilConjectures
