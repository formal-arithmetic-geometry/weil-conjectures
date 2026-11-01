/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleSheetTrace
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleLocalTransposeGluing

/-! # Surjectivity of the native finite-etale trace pairing -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Every arrow out of finite-etale direct image is a trace transpose.
Source: finite sheet sums in smooth trace clause (3), and finite biproduct descent.
(blueprint: new-det-sp-native-finite-etale-trace-pairing-surjective).

Proof in words. On a finite splitting chart identify direct image of M with the
finite product of its sheet restrictions by the canonical counit product map.
Compose a supplied arrow h with each product inclusion and with the inverse
pullback-composition comparison. These are maps from the restrictions of M to
those of p*P on the sheets. On two charts refine by the open-and-closed
intersections of their sheets. The canonical product comparisons restrict to the
same projection maps, so the maps agree on that refinement. Module Hom descent
therefore glues them to f : M -> p*P. The chart formula for the descended trace
identifies p*(f) followed by trace with the row of these components, which is h
by the finite-biproduct identity. Hom descent gives the equality globally.
For zero sheets this is the unique map from the zero module, so neither
surjectivity of p nor nontriviality of the coefficient ring is required. -/
theorem nativeFiniteEtaleSheetPairing_surjective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p]
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Function.Surjective (fun f : M ⟶ (upperStar Λ p).obj P ↦
      (lowerStar Λ p).map f ≫ nativeFiniteEtaleSheetTrace Λ p P) := by
  intro h
  obtain ⟨f, hf⟩ := nativeFiniteEtaleLocalTranspose_glue Λ p M P h
  refine ⟨f, ?_⟩
  apply nativeFiniteEtaleChart_hom_ext Λ p
  intro c
  rw [nativeFiniteEtaleTracePairing_chart Λ p c M P f]
  simp_rw [hf c]
  exact nativeFiniteEtaleLocalTranspose_reconstruct Λ p c M P h

end AlgebraicGeometry.ProEtale.CondensedRing
