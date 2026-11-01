/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Six operations for pulled-back condensed coefficients

Source: latest blueprint, sec-six-functors-basics/sk-prop-qlbar-two-colimit/
det-def-sf-operations.md, ambient typing (i)--(vi), and sk-def-cd,
finite cohomological dimension convention
(blueprint: det-def-sf-operations).

The ambient operations are reused: `upperStar Λ f |>.leftDerivedFunctor`,
`lowerStar Λ f |>.rightDerivedFunctor`, `derivedTensor Λ X`, `derivedHom Λ X`,
`openImmersionLowerShriek Λ j`, and `rightDerivedLowerShriekOfCompactification Λ c`.
Their adjunctions are `derivedUpperStarLowerStarAdjunction` and
`derivedTensorHomAdjunction`. All use the ordinary uncompleted module derived category
with coefficient ring `condensedRingObj Λ X = p_X^* Λ`.

The new exceptional inverse image is literally the restriction of the localizing
right adjoint to the finite-Tor constructible full subcategories. At non-finite
coefficients `integral_ctf_equals_bc` identifies these with bounded constructible
objects; `nativeConstructibleExceptionalInverseImage` is the existing bounded
constructible presentation. Finite etale comparison is a separate theorem.

An optional ambient exceptional functor is a right adjoint to the same ambient
compactification functor. The stronger finite-level datum remains the existing
`Scheme.SfAmbientExceptionalRightAdjointDatum`, including FullCD and coherent
refinement comparisons. No such datum is an argument of the definitions below.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The localizing adjunction and the membership proofs needed for its restriction.
The left functor is the specified compactification composite, not freely chosen data.
The right functor is determined up to the unique adjunction-compatible isomorphism.
Source: det-def-sf-operations (vi), sk-thm-existence (2)--(4)
(blueprint: det-def-sf-operations). -/
structure SixOperationsLocalizingAdjunction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  /-- Membership in the localizing target for the ambient compact-support functor. -/
  lower_mem : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
    ((rightDerivedLowerShriekOfCompactification Λ c).obj K)
  /-- Inclusion of the finite-Tor constructible source into its localizing closure. -/
  source_mem : (constantModelBoundedConstructible Λ X ⊓
    DerivedCategory.finiteTorAmplitude _) ≤ localizingClosureProEtale Λ X
  /-- Inclusion of the finite-Tor constructible target into its localizing closure. -/
  target_mem : (constantModelBoundedConstructible Λ Y ⊓
    DerivedCategory.finiteTorAmplitude _) ≤ localizingClosureProEtale Λ Y
  /-- The localizing exceptional inverse image. -/
  right : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
    (localizingClosureProEtale Λ X).FullSubcategory
  /-- Its defining natural Hom bijections. -/
  adjunction : localizingLowerShriek Λ c lower_mem ⊣ right
  /-- Preservation of finite-Tor constructible objects by compact support. -/
  lower_ctf : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
    (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _) K.obj →
    (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _)
      ((localizingLowerShriek Λ c lower_mem).obj K).obj
  /-- Preservation of finite-Tor constructible objects by the right adjoint. -/
  right_ctf : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
    (constantModelBoundedConstructible Λ Y ⊓ DerivedCategory.finiteTorAmplitude _) K.obj →
    (constantModelBoundedConstructible Λ X ⊓ DerivedCategory.finiteTorAmplitude _)
      (right.obj K).obj

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hcd : BaseFieldFiniteCD ℓ k)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)

/-- Select the adjunction supplied by sk-thm-existence for the chosen compactification.
Only membership proofs and a right adjoint characterized by its adjunction are selected.
Source: det-def-sf-operations (vi), sk-thm-existence (2)--(4)
(blueprint: det-def-sf-operations). -/
def sixOperationsLocalizingAdjunction :
    SixOperationsLocalizingAdjunction Λ (compactificationOverField f) :=
  Classical.choice (by
    obtain ⟨hX, hY, hSX, hSY, h, sX, sY, H⟩ :=
      exceptionalInverseImage_exists Λ ℓ k hcd f hΛ
    let := hX
    let := hY
    let := sX
    let := sY
    obtain ⟨_, _, _, _, hF, _, ⟨G, s, hG⟩, _⟩ := H
    obtain ⟨_, ⟨adj⟩, hpres⟩ := hG
    exact ⟨⟨h, hSX, hSY, G, adj, hF, hpres⟩⟩)

/-- Compact support on Dctf, obtained by full-subcategory restriction of the chosen
ambient compactification functor. Source: det-def-sf-operations (iv), (vi)
(blueprint: det-def-sf-operations). -/
def ctfLowerShriek :
    ConstantModelConstructibleFiniteTor Λ X.left ⥤ ConstantModelConstructibleFiniteTor Λ Y.left :=
  (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _).lift
    ((constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _).ι ⋙
      rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f))
    (fun K ↦ (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).lower_ctf
      ⟨K.obj, (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).source_mem K.obj K.property⟩
      K.property)

/-- The exceptional inverse image on Dctf is the restriction of the localizing right
adjoint. No ambient exceptional right adjoint or finite-level comparison is assumed.
Source: det-def-sf-operations (vi) (blueprint: det-def-sf-operations). -/
def ctfExceptionalInverseImage :
    ConstantModelConstructibleFiniteTor Λ Y.left ⥤ ConstantModelConstructibleFiniteTor Λ X.left :=
  (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _).lift
    (ObjectProperty.ιOfLE (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).target_mem ⋙
      (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).right ⋙
      (localizingClosureProEtale Λ X.left).ι)
    (fun K ↦ (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).right_ctf
      ⟨K.obj, (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).target_mem K.obj K.property⟩
      K.property)

/-- The restricted adjunction, retaining the localizing Hom bijections.
Source: det-def-sf-operations (vi), restriction paragraph
(blueprint: det-def-sf-operations). -/
def ctfExceptionalAdjunction :
    ctfLowerShriek Λ ℓ k hcd f hΛ ⊣ ctfExceptionalInverseImage Λ ℓ k hcd f hΛ :=
  (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).adjunction.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE
      (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).source_mem)
    (ObjectProperty.fullyFaithfulιOfLE
      (sixOperationsLocalizingAdjunction Λ ℓ k hcd f hΛ).target_mem)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _))

end AlgebraicGeometry.ProEtale.CondensedRing
