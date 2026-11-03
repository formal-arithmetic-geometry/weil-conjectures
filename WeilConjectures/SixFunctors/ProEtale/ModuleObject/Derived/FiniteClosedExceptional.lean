/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement

/-!
# Finite-coefficient closed exceptional inverse image over an arbitrary field

Source: blueprint
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/det-prop-a1.proof.md,
Step 1, the Brown exceptional operation; det-def-sf-operations (vi);
coord/brief-stage2.md, general-field smooth-purity ruling of 2026-11-01
(blueprint: def-pur-finite-closed-exceptional).

This extends the domain of the recorded Brown construction for closed immersions.
It uses exactly its localizing adjunction structure and its chosen compactification.
It agrees by adjunction uniqueness with ctfExceptionalInverseImage wherever the latter
is already defined. In particular it is not defined to be the transported etale functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A]
  [DiscreteTopology A] [IsTopologicalRing A]
  (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsClosedImmersion f.left] (hA : ∃ e : ℕ, (l ^ e : A) = 0)

include l hA in
/-- The Brown localizing adjunction exists for a closed immersion at finite coefficients
without a finite-CD hypothesis on the ground field.
Source: det-prop-a1, Step 1, and the general-field smooth-purity ruling
(blueprint: def-pur-finite-closed-exceptional).

Proof: use the normalized section-action encoding for the discrete finite ring. On
bounded-below etale-origin objects the exact site comparison identifies the actual
chosen compact-support word with the ordinary etale word. Closed direct image is exact,
preserves coproducts and constructible finite-Tor objects, and its ordinary support right
adjoint exists by the closed-support adjunction. Pass to the localizing closures generated
by Dctf, using the same compact-support comparison. This gives the localizing right
adjoint and its natural Hom bijections. Finite constructibility and Tor preservation are
local on the target and follow from the finite etale closed-support calculation; no
bound on the cohomological dimension of the base field is used. Transport these
membership proofs and the adjunction back through the normalized encoding. -/
theorem finiteClosedLocalizingAdjunction_exists :
    Nonempty (SixOperationsLocalizingAdjunction (coefficient A) (compactificationOverField f)) := by
  sorry

/-- The recorded compact-support functor restricted by its finite closed-case proofs.
Source: det-def-sf-operations (iv),(vi) (blueprint: def-pur-finite-closed-exceptional). -/
def finiteClosedCtfLowerShriek :
    ConstantModelConstructibleFiniteTor (coefficient A) X.left ⥤
      ConstantModelConstructibleFiniteTor (coefficient A) Y.left :=
  (constantModelBoundedConstructible (coefficient A) Y.left ⊓
      DerivedCategory.finiteTorAmplitude _).lift
    ((constantModelBoundedConstructible (coefficient A) X.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι ⋙
      rightDerivedLowerShriekOfCompactification (coefficient A) (compactificationOverField f))
    (fun K ↦ (finiteClosedLocalizingAdjunction A l k f hA).lower_ctf
      ⟨K.obj, (finiteClosedLocalizingAdjunction A l k f hA).source_mem K.obj K.property⟩ K.property)

/-- The finite closed exceptional inverse image is literally a restriction of the Brown
right adjoint on the same localizing closures as the recorded operation.
Source: det-def-sf-operations (vi), closed case of det-prop-a1 Step 1
(blueprint: def-pur-finite-closed-exceptional). -/
def finiteClosedCtfExceptionalInverseImage :
    ConstantModelConstructibleFiniteTor (coefficient A) Y.left ⥤
      ConstantModelConstructibleFiniteTor (coefficient A) X.left :=
  (constantModelBoundedConstructible (coefficient A) X.left ⊓
      DerivedCategory.finiteTorAmplitude _).lift
    (ObjectProperty.ιOfLE (finiteClosedLocalizingAdjunction A l k f hA).target_mem ⋙
      (finiteClosedLocalizingAdjunction A l k f hA).right ⋙
      (localizingClosureProEtale (coefficient A) X.left).ι)
    (fun K ↦ (finiteClosedLocalizingAdjunction A l k f hA).right_ctf
      ⟨K.obj, (finiteClosedLocalizingAdjunction A l k f hA).target_mem K.obj K.property⟩ K.property)

/-- The restricted Brown adjunction retains the actual localizing unit and counit.
Source: det-def-sf-operations (vi) (blueprint: def-pur-finite-closed-exceptional). -/
def finiteClosedCtfAdjunction :
    finiteClosedCtfLowerShriek A l k f hA ⊣
      finiteClosedCtfExceptionalInverseImage A l k f hA :=
  (finiteClosedLocalizingAdjunction A l k f hA).adjunction.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulιOfLE
      (finiteClosedLocalizingAdjunction A l k f hA).source_mem)
    (ObjectProperty.fullyFaithfulιOfLE
      (finiteClosedLocalizingAdjunction A l k f hA).target_mem)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _))

/-- Canonical identification with the recorded ctf exceptional functor on its domain.
This is the unique adjunction-compatible comparison, so it preserves units and counits.
Source: det-prop-a1 Step 1 (blueprint: def-pur-finite-closed-exceptional). -/
def finiteClosedCtfExceptionalIso (hcd : BaseFieldFiniteCD l k)
    (hΛ : IsLocalizingAdmissibleCoefficient l (coefficient A)) :
    ctfExceptionalInverseImage (coefficient A) l k hcd f hΛ ≅
      finiteClosedCtfExceptionalInverseImage A l k f hA :=
  (ctfExceptionalAdjunction (coefficient A) l k hcd f hΛ).rightAdjointUniq
    (finiteClosedCtfAdjunction A l k f hA)

end AlgebraicGeometry.ProEtale.CondensedRing
