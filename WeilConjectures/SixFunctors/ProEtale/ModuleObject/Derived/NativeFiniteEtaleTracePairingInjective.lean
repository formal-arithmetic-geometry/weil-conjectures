/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleSheetTrace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtalePushforwardFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleTracePairingLocal

/-! # Injectivity of the native finite-etale trace pairing -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction

/-- The normalized native trace pairing is injective.
Source: finite splitting charts and the finite product comparison.
(blueprint: new-det-sp-native-finite-etale-trace-pairing-injective).
Proof. On a splitting chart direct image is the product of sheet restrictions.
The trace pairing is its row of sheet maps. Compose with each product inclusion
to recover that sheet map, so equal pairings give equal restrictions to every
sheet. The product comparison and chart Hom descent then identify the direct
images of the original maps. Finite-etale direct image is faithful, because
sections extend by zero along the clopen diagonal, so the original maps coincide.
Empty products and the zero coefficient ring satisfy the same argument. -/
theorem nativeFiniteEtaleSheetPairing_injective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Function.Injective (fun f : M ⟶ (upperStar Λ p).obj P ↦
      (lowerStar Λ p).map f ≫ nativeFiniteEtaleSheetTrace Λ p P) := by
  classical
  intro f g h
  have : (lowerStar Λ p).Faithful := nativeFiniteEtale_lowerStar_faithful Λ p
  apply (lowerStar Λ p).map_injective
  apply nativeFiniteEtaleChart_hom_ext Λ p
  intro c
  have he (j : Fin c.degree) :
      (upperStar Λ (c.sheet j)).map f = (upperStar Λ (c.sheet j)).map g := by
    calc
      _ = nativeFiniteEtaleLocalTranspose Λ p c M P
          ((lowerStar Λ p).map f ≫ nativeFiniteEtaleSheetTrace Λ p P) j :=
        (nativeFiniteEtaleLocalTranspose_pairing Λ p c M P f j).symm
      _ = nativeFiniteEtaleLocalTranspose Λ p c M P
          ((lowerStar Λ p).map g ≫ nativeFiniteEtaleSheetTrace Λ p P) j :=
        congrArg (fun z ↦ nativeFiniteEtaleLocalTranspose Λ p c M P z j) h
      _ = _ := nativeFiniteEtaleLocalTranspose_pairing Λ p c M P g j
  let q' := Pi.lift (nativeFiniteEtaleSheetProjection Λ p c ((upperStar Λ p).obj P))
  have : IsIso q' := nativeFiniteEtaleSheetProjection_product_isIso Λ p c ((upperStar Λ p).obj P)
  apply (cancel_mono q').mp
  apply Pi.hom_ext
  intro j
  simp only [q', Category.assoc, Pi.lift_π]
  rw [nativeFiniteEtaleSheetProjection_naturality, nativeFiniteEtaleSheetProjection_naturality, he]

end AlgebraicGeometry.ProEtale.CondensedRing
