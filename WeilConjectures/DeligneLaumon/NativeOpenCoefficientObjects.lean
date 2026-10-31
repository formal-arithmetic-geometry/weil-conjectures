/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealizationSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement

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

/-- Commutativity of the native field ring, with the spectral topology.
Source: coefficient convention of clause (2)
(blueprint: def-dla1-native-open-coefficient-objects). -/
instance fieldRing_comm : IsCommMonObj (fieldRing l E) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj E

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

/-- The same inclusion in the native O_E presentation used by the strict reduction data.
The coefficient identification is the existing finite-projection-normalized point comparison.
Source: clause (2), integral-to-rational scalar map
(blueprint: def-dla1-native-open-coefficient-objects). -/
abbrev nativeInclusion : spIntegralCondensed l E ⟶ fieldRing l E :=
  (IntegralConstantModel.pointComparison l E).inv.hom ≫ inclusion l E

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

/-- The actual condensed map of finite field coefficients.
Source: clause (2), E to E' scalar map
(blueprint: def-dla1-native-open-coefficient-objects). -/
abbrev fieldMap (E' : Type u) [Field E'] [Algebra ℚ_[l] E']
    [FiniteDimensional ℚ_[l] E'] (f : E →ₐ[ℚ_[l]] E')
    (hf : @Continuous E E' (fieldTopology l E) (fieldTopology l E') f) :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (fieldMapSheaf l E E' f hf)

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

/-- Localize the coefficient-linear projection-formula comparison for restriction of scalars.
Source: clause (2), balanced scalar normalization
(blueprint: def-dla1-native-open-coefficient-objects). -/
def restrictionOpenIso :
    D(CondensedRing.openImmersionLowerShriek Λ' j) ⋙ D(Mod.comap (coefficientMap a T)) ≅
      D(Mod.comap (coefficientMap a U)) ⋙ D(CondensedRing.openImmersionLowerShriek Λ j) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (CondensedRing.comapOpenImmersionLowerShriekIso a j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The balanced scalar map is constructed from the scalar unit and the coefficient-linear
open projection formula. Its generator formula is 1 tensor j_!m to j_!(1 tensor m).
Source: clause (2), balanced scalar normalization
(blueprint: def-dla1-native-open-coefficient-objects). -/
def balancedMap (K : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a T)).homEquiv _ _).symm
    (D(CondensedRing.openImmersionLowerShriek Λ j).map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U)).unit.app K) ≫
      (restrictionOpenIso a j).inv.app
        (L(Mod.extendScalars (coefficientMap a U)).obj K))

/-- The scalar/pullback arrow, transposed from the fixed restriction comparison.
Source: clause (2), compatibility with the open counit
(blueprint: def-dla1-native-open-coefficient-objects). -/
def pullScalarMap :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a T))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
    (CondensedRing.derivedComapUpperStarIso a j)

/-- The substantive scalar normalization and the square for the actual open counits.
Source: clause (2), scalar maps and counits
(blueprint: def-dla1-native-open-coefficient-objects). -/
def ScalarCompatibility : Prop :=
  (∀ K, balancedMap a j K = (CondensedRing.derivedOpenImmersionShriekIso a j).hom.app K) ∧
  ∀ N,
    (CondensedRing.derivedOpenImmersionShriekIso a j).hom.app
        (D(CondensedRing.upperStar Λ j).obj N) ≫
      D(CondensedRing.openImmersionLowerShriek Λ' j).map ((pullScalarMap a j).app N) ≫
      (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j).counit.app
        (L(Mod.extendScalars (coefficientMap a T)).obj N) =
    L(Mod.extendScalars (coefficientMap a T)).map
      ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).counit.app N)

/-- Native finite evaluation of a field complex: restrict its O_E action, then derive the
actual positive quotient extension of scalars. Source: clause (2), rational finite evaluations
(blueprint: def-dla1-native-open-coefficient-objects). -/
abbrev rationalEvaluation (X : Scheme.{u}) (n : ℕ) :=
  D(Mod.comap (coefficientMap (inclusion l E) X)) ⋙ AdicCompletion.derivedReduction l E X n

end NativeOpenExtension

end WeilConjectures
