/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarTensorData
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import all WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import all WeilConjectures.Algebra.Homology.ScalarInternalHomAdjunction

/-! # Native presentations of the open scalar tensor models

Source: Stacks Project, Tags 07A4, 07A6 and 0FPT.
(blueprint: lem-sp-native-open-scalar-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- The closed structures and representative comparisons agree with the native
K-flat derived tensor. The scalar adjunctions remain normalized as in `Models`.
Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-sp-native-open-scalar-models). -/
def NativeModels (m : Models.{u}) : Prop :=
  ∀ (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}),
    ((m T).closed R).monoidal =
      RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2} (Scheme.ProEt.topology T) R ∧
    ∀ (P Q : CochainComplex (proEtaleRingModules T R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
      HEq ((m T).model R |>.iso (Scheme.ProEt.topology T) R ((m T).closed R) P Q hP hQ)
        (RingedDerivedNative.tensorIso.{u + 1, u, u + 1, u + 2}
          (Scheme.ProEt.topology T) R P Q (Or.inl hP))

/-- The representative constraints of each selected closed tensor structure.
Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-sp-native-open-scalar-models). -/
def CoherentModels (m : Models.{u}) : Prop :=
  ∀ (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}),
    ∃ β : @SymmetricCategory (DerivedCategory (proEtaleRingModules T R)) _
      ((m T).closed R).monoidal,
      Nonempty (RingedDerivedTensorCoherence.{u + 1, u, u + 1, u + 2}
        (Scheme.ProEt.topology T) R ((m T).closed R) ((m T).model R) β)

/-- Native closed structures can be selected simultaneously with normalized scalar pairs.
Source: Stacks Project, Tags 07A4, 07A6 and 0FPT
(blueprint: lem-sp-native-open-scalar-models).

Proof: for each scheme and ring sheaf, use the proved native closed-monoidal
construction, retaining its equality of monoidal structures and its heterogeneous
comparison equation on every K-flat pair. Independently choose the normalized
scalar-derived adjunction for every ring-sheaf map. These data are precisely a
`Models` family, and the two equations retained by the first construction prove
`NativeModels`. Retaining the symmetric structure and its representative coherence
also gives `CoherentModels`. All choices are made from proved constructions. -/
theorem native_models : ∃ m : Models.{u}, NativeModels m ∧ CoherentModels m := by
  let h (T : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :=
    ringedDerived_closed_symmetric_monoidal_native.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology T) R
  let m : Models.{u} := fun T ↦ {
    closed := fun R ↦ (h T R).choose
    model := fun R ↦ (h T R).choose_spec.2.choose
    scalar := fun a ↦ (scalarDerivedPair_exists a).some }
  refine ⟨m, ⟨fun T R ↦ ⟨(h T R).choose_spec.1, ?_⟩, ?_⟩⟩
  · exact (h T R).choose_spec.2.choose_spec.choose_spec.choose_spec.2
  · intro T R
    exact ⟨(h T R).choose_spec.2.choose_spec.choose,
      ⟨(h T R).choose_spec.2.choose_spec.choose_spec.choose⟩⟩

/-- The restricted flat-term model retains the native K-flat tensor comparison.
Source: Stacks Project, Tag 07A4
(blueprint: lem-sp-native-open-scalar-models).

Proof: the restricted model is obtained by whiskering the same comparison along
the inclusion of flat-term representatives into all K-flat representatives.
Consequently its component is definitionally the comparison recorded in `NativeModels`. -/
theorem native_tensorModel_comparison (m : Models.{u}) (hm : NativeModels m)
    (A : Type u) [CommRing A] (T : Scheme.{u})
    (P Q : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hp : proEtaleFlatRepresentatives T (proEtaleConstantRing T A) P)
    (hq : proEtaleFlatRepresentatives T (proEtaleConstantRing T A) Q) :
    HEq ((tensorModel m A T).representative.app (⟨P, hp⟩, ⟨Q, hq⟩))
      (RingedDerivedNative.tensorIso.{u + 1, u, u + 1, u + 2}
        (Scheme.ProEt.topology T) (proEtaleConstantRing T A) P Q
        (Or.inl ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hp.1))) := by
  exact (hm T (proEtaleConstantRing T A)).2 P Q
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hp.1)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).mpr hq.1)

end AlgebraicGeometry.ProEtale.OpenScalarTensor
