/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Properness of morphisms of schemes over a base

Cancellation for properness, packaged for the category `Over S` of schemes over a base scheme
`S`: a morphism of `S`-schemes with proper source and separated target is proper. Together with
the global sections of a proper integral scheme over an algebraically closed field, which
Mathlib's `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` gives outright.

## Main results

- `AlgebraicGeometry.isProper_left`: a morphism `f : X ⟶ Y` in `Over S` with `X` proper over `S`
  and `Y` separated over `S` is proper.
- `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_appTop` (blueprint `lem:cube-global-sections`): for
  `X` proper and integral over an algebraically closed field `K`, the structure map
  `K ⟶ Γ(X, 𝒪_X)` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism `f : X ⟶ Y` of schemes over `S` with `X` proper over `S` and `Y` separated over
`S` is proper.

```
             f.left
    X.left ─────────→ Y.left
         ╲           ╱
   X.hom  ╲         ╱  Y.hom
           ↘       ↙
               S
```
-/
instance (priority := low) isProper_left {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsProper X.hom] [IsSeparated Y.hom] : IsProper f.left := by
  have : IsProper (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  exact IsProper.of_comp _ Y.hom

/-- **The global sections of a proper integral scheme over an algebraically closed field.**

For `X` proper and integral over an algebraically closed field `K`, the structure morphism
induces an isomorphism `K ≅ Γ(X, 𝒪_X)`. This is `lem:cube-global-sections` of the blueprint.

Mathlib's `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed` makes `Γ(X, 𝒪_X)` an
integral extension of `K`, and it is a domain because `X` is integral; over an algebraically
closed `K` an integral domain extension is trivial. -/
theorem isIso_ΓSpecIso_inv_comp_appTop {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π] :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
  apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed π

end AlgebraicGeometry
