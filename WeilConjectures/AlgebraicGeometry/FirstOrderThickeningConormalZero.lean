/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.AffineConormalSections

/-!
# A first order thickening with zero conormal is an isomorphism

## References

* [Stacks Project, Tag 04FE](https://stacks.math.columbia.edu/tag/04FE)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A square-zero closed immersion is an isomorphism if its conormal module vanishes.
This does not require any universal lifting property. (Stacks, Tags 04FE and 01R3.) -/
theorem firstOrderThickening_isIso_of_conormal_isZero {X X' : Scheme.{u}}
    (i : X ⟶ X') (hi : IsFirstOrderThickening i)
    (hC : IsZero ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) :
    IsIso i := by
  have : IsClosedImmersion i := hi.1
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply Scheme.IdealSheafData.ext
  funext U
  let I := i.ker.ideal U
  obtain ⟨e, _⟩ := (Scheme.Modules.affine_conormal_sections i).2 U
    Γ(X', U.1) (RingEquiv.refl _) I (by simp [I, Scheme.Hom.ker_apply])
  have hsec : ∀ z : Γ((Scheme.Modules.tensorPullback i).obj i.ker.toModules,
      i ⁻¹ᵁ U.1), z = 0 := by
    intro z
    have heq := congrArg (fun φ ↦ φ.app (i ⁻¹ᵁ U.1) z) (hC.eq_of_src (𝟙 _) 0)
    simpa using heq
  have : Subsingleton Γ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules), U.1) :=
    ⟨fun x y ↦ (hsec x).trans (hsec y).symm⟩
  have hI : Subsingleton I.Cotangent := e.toEquiv.subsingleton
  have hsq : I ^ 2 = ⊥ := congrArg (fun J : X'.IdealSheafData ↦ J.ideal U) hi.2
  have hidem := (Ideal.cotangent_subsingleton_iff I).mp hI
  change I = ⊥
  exact hidem.symm.trans (by simpa [pow_two] using hsq)

end AlgebraicGeometry
