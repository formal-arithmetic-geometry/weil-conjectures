/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The preimage of an affine open under an affine morphism is a fibre product

For an affine morphism `f : X ⟶ Y` and an affine open `U` of `Y`, the affine scheme
`Spec Γ(X, f ⁻¹ᵁ U)` is the fibre product `Spec Γ(Y, U) ×[Y] X`.

## Main declarations

* `AlgebraicGeometry.IsAffineOpen.SpecMap_app_fromSpec`: the square built from `f.app U` and the
  two canonical morphisms `fromSpec` commutes.
* `AlgebraicGeometry.IsAffineOpen.isPullback_SpecMap_app_fromSpec`: that square is cartesian.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsAffineOpen

variable {X Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U) (f : X ⟶ Y) [IsAffineHom f]

/-- The square expressing `f ⁻¹ᵁ U` as the preimage of `U`, in terms of `Spec` of the affine
opens:

```
    Spec Γ(X, f ⁻¹ᵁ U) --(hU.preimage f).fromSpec--> X
            |                                       |
    Spec.map (f.app U)                              f
            |                                       |
            v                                       v
      Spec Γ(Y, U) ------------hU.fromSpec--------> Y
```
-/
@[reassoc]
lemma SpecMap_app_fromSpec :
    Spec.map (f.app U) ≫ hU.fromSpec = (hU.preimage f).fromSpec ≫ f := by
  rw [Scheme.Hom.app_eq_appLE]
  exact SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl

/-- **The affine open `f ⁻¹ᵁ U` is the fibre product of `U` and `X` over `Y`**, in terms of `Spec`
of the affine opens: the commuting square

```
    Spec Γ(X, f ⁻¹ᵁ U) --(hU.preimage f).fromSpec--> X
          ⌜ |                                        |
    Spec.map (f.app U)                               f
            |                                        |
            v                                        v
      Spec Γ(Y, U) ------------hU.fromSpec---------> Y
```

of `AlgebraicGeometry.IsAffineOpen.SpecMap_app_fromSpec` is cartesian. -/
lemma isPullback_SpecMap_app_fromSpec :
    IsPullback (Spec.map (f.app U)) (hU.preimage f).fromSpec hU.fromSpec f := by
  have h₁ : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := isPullback_morphismRestrict f U
  have h₂ : IsPullback (Spec.map (f.app U)) (hU.preimage f).isoSpec.inv hU.isoSpec.inv
      (f ∣_ U) := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, isoSpec_inv_ι, morphismRestrict_ι,
      ← Category.assoc, isoSpec_inv_ι, ← hU.SpecMap_app_fromSpec f]
  exact h₂.paste_vert h₁

end AlgebraicGeometry.IsAffineOpen
