/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Sheaf.AlgebraicGeometry.InternalExtensionInverseImage
import Sheaf.AlgebraicGeometry.InternalExtensionFinitePresentation
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!
# Subfield scalar extension preserves local presentations after raw scheme pullback

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
  sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-subfield-constructible.proof.md,
  second sentence (blueprint: lem-sfb-subfield-extension-local-presentation).

This statement records tensoring a local finite presentation along a finite coefficient
extension after arbitrary raw pro-etale pullback.  The proof follows the four proof steps
in the node: use the internal inverse-image comparison for `f` and for each member of a
witnessing cover, tensor the finite presentation, and retain the same cover.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

universe u

set_option autoImplicit false

namespace AlgebraicGeometry.ProEtale

/--
Subfield scalar extension preserves local finite presentations after arbitrary raw pullback.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
  sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-subfield-constructible.proof.md,
  second sentence (blueprint: lem-sfb-subfield-extension-local-presentation).

Proof (deferred to stage 3).  First apply `lem-sfb-internal-extension-inverse-image` to
`f`, the commutative coefficient rings `E_X` and `F_X`, and their inclusion, obtaining the
comparison of the raw pullback of the scalar extension with extension over the raw
pullback rings.  For every member of a cover witnessing the hypothesis, apply the same
comparison to that member and transport the first comparison along its module functor.
Apply `lem-sfb-internal-extension-finite-presentation` to tensor the finite presentation
on each member; its finite ranks are unchanged and no flatness is assumed.  The resulting
cokernel presentations show that each member of the original cover witnesses the
conclusion, so every witnessing cover is retained.
-/
theorem subfieldExtension_localPresentation
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (hEF : E ≤ F)
    {X Z : Scheme.{u}} (f : Z ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))
    (hM : IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj X ℓ E))
      ((Functor.mapMod (upperStar Ab.{u + 1} f)
        (padicSubfieldRingObj X ℓ E)).obj M)) :
    IsLocallyFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj X ℓ F))
      ((Functor.mapMod (upperStar Ab.{u + 1} f)
        (padicSubfieldRingObj X ℓ F)).obj
        ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hEF)).obj M)) ∧
      ∀ (𝒰 : Scheme.Cover Scheme.proetalePrecoverage Z),
        (∀ i : 𝒰.I₀,
          Mod.IsFinitelyPresented
            ((upperStar Ab.{u + 1} (𝒰.f i)).obj
              ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj X ℓ E)))
            (((Functor.mapMod (upperStar Ab.{u + 1} (𝒰.f i))
              ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj X ℓ E))).obj
              ((Functor.mapMod (upperStar Ab.{u + 1} f)
                (padicSubfieldRingObj X ℓ E)).obj M)))) →
        ∀ i : 𝒰.I₀,
          Mod.IsFinitelyPresented
            ((upperStar Ab.{u + 1} (𝒰.f i)).obj
              ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj X ℓ F)))
            (((Functor.mapMod (upperStar Ab.{u + 1} (𝒰.f i))
              ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj X ℓ F))).obj
              ((Functor.mapMod (upperStar Ab.{u + 1} f)
                (padicSubfieldRingObj X ℓ F)).obj
                ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hEF)).obj M)))) := by
  sorry

end AlgebraicGeometry.ProEtale
