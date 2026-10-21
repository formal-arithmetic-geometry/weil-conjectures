/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding

/-! # Finite discrete coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The two compactification composites agree under normalized coefficient encoding.
Source: blueprint coefficient-identification proof, steps 11--12; Stacks Tags 015F and 03EK.
(blueprint: lem-sf-finite-discrete-encoding-compactification).

Proof: on every site object both direct images evaluate the same module on the fibre
product. The coefficient-sections identity identifies the scalar actions, giving the
underived direct-image comparison. The same identity gives the pullback comparison.
For an open immersion the two extensions by zero are left adjoint to the identified
restriction functor; uniqueness of left adjoints gives their natural comparison.
The encodings are exact equivalences and are right adjoint to their exact inverses,
so they preserve K-injective complexes. Compute the right derived direct images on
corresponding K-injective resolutions and descend the termwise comparison. Extension
by zero is exact, so its termwise comparison already computes its derived functor.
Compose the two comparisons, using the given open and proper factors of the very same
compactification. This proves the displayed natural isomorphism without changing or
choosing a compactification. -/
theorem encoding_compactification [Finite A] [DiscreteTopology A]
    (E : ∀ T : Scheme.{u}, Encoding A T)
    (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f) :
    Nonempty (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
        (E Y).fixedDerived.functor ≅
      (E X).fixedDerived.functor ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c) := by sorry

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
