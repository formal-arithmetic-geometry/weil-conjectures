/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact

/-!
# Signed shifts of condensed derived tensor and internal Hom

Source: latest blueprint, sec-six-functors/sk-thm-sf-tensor-hom,
lem-sf-tensor-hom.proof.md,
Step 2: compatibility with shifts of the tensor--internal-Hom ingredients
(blueprint: lem-sf-condensed-derived-tensor-shifts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v h

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated.Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The shift laws for the specified tensor and closed adjunction, including the signed
source mate on the triangulated opposite. The tensor shift structure is supplied by the
canonical signed total-complex localization, not chosen by this predicate.
Source: latest blueprint, lem-sf-tensor-hom.proof.md, Step 2
(blueprint: lem-sf-condensed-derived-tensor-shifts). -/
def SignedClosedShiftLaws (D : Type v) [Category.{h} D] [Preadditive D]
    [HasShift D ℤ] [MonoidalCategory D] [MonoidalClosed D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int] : Prop :=
  (∀ K : D, ∃ s : (CategoryTheory.ihom K).CommShift ℤ,
    s = (CategoryTheory.ihom.adjunction K).rightAdjointCommShift ℤ ∧
    ∀ r : ℤ,
      Adjunction.CommShift.CompatibilityUnit (CategoryTheory.ihom.adjunction K)
        ((tensorLeft K).commShiftIso r) (s.commShiftIso r) ∧
      Adjunction.CommShift.CompatibilityCounit (CategoryTheory.ihom.adjunction K)
        ((tensorLeft K).commShiftIso r) (s.commShiftIso r)) ∧
  (∀ M : D, ∃ s : (MonoidalClosed.internalHom.flip.obj M).CommShift ℤ,
    ∀ (n : ℤ) (X : Dᵒᵖ),
      (s.commShiftIso n).hom.app X = siteHomSignedSourceComponent M n X)

namespace CondensedRing

/-- The signed total-complex tensor shifts and the closed-adjunction Hom shifts on
unbounded condensed module categories, and on ordinary finite constant coefficients.
The predicate specifies the unique unit/counit-compatible target-Hom shifts and the
quadratic-sign source mate; its `CommShift` witnesses include naturality, zero and addition.

Source: latest blueprint, sec-six-functors/sk-thm-sf-tensor-hom,
lem-sf-tensor-hom.proof.md, Step 2.

Proof: unfold `SignedClosedShiftLaws`. The published derived monoidal construction already
provides the canonical signed integer bifunctor shift. For each fixed tensor parameter,
`Adjunction.rightAdjointCommShift` supplies the target-Hom shift, and
`RightAdjointCommShift.compatibilityUnit_iso` together with
`compatibilityCounit_of_compatibilityUnit` supplies the required unit and counit equations.
The existing `nativeDerivedHom_signed_exact` theorem supplies the coherent quadratic-sign
source-Hom shift with exactly the displayed components. Apply the same argument to the
condensed module-object category and to every finite constant coefficient module-sheaf
category; no boundedness or Tor-amplitude hypothesis is needed.
(blueprint: lem-sf-condensed-derived-tensor-shifts). -/
theorem condensedDerivedTensorShiftStructure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (W : Scheme.{u}) :
    SignedClosedShiftLaws (DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj Λ W))) ∧
    (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}),
      SignedClosedShiftLaws
        (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))) := by
  constructor
  · let D := DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (condensedRingObj Λ W))
    change SignedClosedShiftLaws D
    rw [SignedClosedShiftLaws]
    constructor
    · intro K
      refine ⟨(CategoryTheory.ihom.adjunction K).rightAdjointCommShift ℤ, rfl, ?_⟩
      intro r
      refine ⟨?_, ?_⟩
      · exact CategoryTheory.Adjunction.RightAdjointCommShift.compatibilityUnit_iso
          (CategoryTheory.ihom.adjunction K) r
      · exact CategoryTheory.Adjunction.CommShift.compatibilityCounit_of_compatibilityUnit
          _ _ _ (CategoryTheory.Adjunction.RightAdjointCommShift.compatibilityUnit_iso
            (CategoryTheory.ihom.adjunction K) r)
    · intro M
      obtain ⟨s, _, hcomp⟩ :=
        nativeDerivedHom_signed_exact
          (C := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
            (condensedRingObj Λ W)) M
      refine ⟨s, ?_⟩
      intro n X
      simpa only [siteHomSignedSourceComponent] using hcomp X.unop n
  · intro A _ _ X
    rw [SignedClosedShiftLaws]
    constructor
    · intro K
      refine ⟨(CategoryTheory.ihom.adjunction K).rightAdjointCommShift ℤ, rfl, ?_⟩
      intro r
      refine ⟨?_, ?_⟩
      · exact CategoryTheory.Adjunction.RightAdjointCommShift.compatibilityUnit_iso
          (CategoryTheory.ihom.adjunction K) r
      · exact CategoryTheory.Adjunction.CommShift.compatibilityCounit_of_compatibilityUnit
          _ _ _ (CategoryTheory.Adjunction.RightAdjointCommShift.compatibilityUnit_iso
            (CategoryTheory.ihom.adjunction K) r)
    · intro M
      obtain ⟨s, _, hcomp⟩ :=
        nativeDerivedHom_signed_exact (C := Sheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} A)) M
      refine ⟨s, ?_⟩
      intro n Y
      simpa only [siteHomSignedSourceComponent] using hcomp Y.unop n

end CondensedRing
end AlgebraicGeometry.ProEtale
