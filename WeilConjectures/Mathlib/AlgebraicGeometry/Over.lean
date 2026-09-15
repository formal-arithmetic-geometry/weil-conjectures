/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# The structure map on global sections of a scheme over a base ring

If `X` is a scheme over `Spec R`, the structure morphism `X ↘ Spec R` induces a ring
homomorphism `R → Γ(X, 𝒪_X)`. Mathlib records this only as an `R`-algebra structure on
`Γ(X, ⊤)` for `X` *affine* over `Spec R`; here we record the underlying ring homomorphism,
which needs no affineness hypothesis.

## Main definitions

- `AlgebraicGeometry.Scheme.overRingHom`: the ring homomorphism `R → Γ(X, 𝒪_X)`.
- `AlgebraicGeometry.Scheme.module_sectionsTop`: the `R`-module structure on `Γ(X, 𝒪_X)` obtained
  by restricting scalars along it.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The ring homomorphism `R → Γ(X, 𝒪_X)` induced by the structure morphism of a scheme over
`Spec R`. -/
noncomputable def overRingHom : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop).hom

lemma overRingHom_apply (r : R) :
    overRingHom R X r = (X ↘ Spec (.of R)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) :=
  rfl

/-- The global functions of a scheme over `Spec R` form an `R`-module, by restriction of scalars
along the structure map `R → Γ(X, 𝒪_X)`. -/
noncomputable instance module_sectionsTop : Module R Γ(X, ⊤) :=
  Module.compHom _ (overRingHom R X)

lemma smul_sectionsTop_def (r : R) (t : Γ(X, ⊤)) : r • t = overRingHom R X r * t := rfl

section

variable {X} {Y : Scheme.{u}} [Y.Over (Spec (.of R))] (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- The structure maps `R → Γ(-, 𝒪)` of two schemes over `Spec R` are compatible with a
morphism over `Spec R` between them. -/
lemma appTop_overRingHom (r : R) :
    f.appTop.hom (overRingHom R Y r) = overRingHom R X r := by
  have h : (X ↘ Spec (.of R)).appTop = (Y ↘ Spec (.of R)).appTop ≫ f.appTop := by
    rw [← Scheme.Hom.comp_appTop, comp_over]
  rw [overRingHom_apply, overRingHom_apply, h]
  rfl

end

end AlgebraicGeometry.Scheme
