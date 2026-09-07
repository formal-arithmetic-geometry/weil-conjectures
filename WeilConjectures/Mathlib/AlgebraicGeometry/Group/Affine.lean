/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Global sections of an affine scheme over an unbundled base ring

Mathlib equips the global sections of a scheme `X` affine over `Spec S` with an `S`-algebra
structure, for a *bundled* base ring `S : CommRingCat`. Instance search cannot use that instance
when the goal mentions an unbundled ring `R : Type u`, because it would have to invert the
forgetful coercion `CommRingCat → Type u`. This file restates it for `R : Type u`, and records
that the structure morphism of `X` is `Spec` of the structure map `R → Γ(X, ⊤)`.

## Main results

- `AlgebraicGeometry.algebraPresheafObj`: the `R`-algebra structure on `Γ(X, ⊤)`.
- `AlgebraicGeometry.isoSpec_hom_comp_specMap_algebraMap`: `X ⟶ Spec R` is
  `Spec (R → Γ(X, ⊤))` read through `X ≅ Spec Γ(X, ⊤)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- Mathlib's `S`-algebra structure on `Γ(X, ⊤)`, for `X` affine over `Spec S` and `S` a bundled
commutative ring, packaged as a `def` with `S` an explicit argument. This exists only to make
`AlgebraicGeometry.algebraPresheafObj` definitionally equal to it. -/
@[instance_reducible]
noncomputable def algebraPresheafObjOfBundled (S : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec S)] [IsAffine X] : Algebra S Γ(X, ⊤) :=
  inferInstance

/-- The global sections of a scheme `X` affine over `Spec R` form an `R`-algebra. -/
noncomputable instance (priority := low) algebraPresheafObj [X.Over (Spec (.of R))] [IsAffine X] :
    Algebra R Γ(X, ⊤) :=
  algebraPresheafObjOfBundled (.of R) X

variable (R X) in
/-- The structure morphism of a scheme `X` affine over `Spec R` is `Spec` of the structure map
`R → Γ(X, ⊤)`, read through the canonical isomorphism `X ≅ Spec Γ(X, ⊤)`. -/
@[reassoc]
lemma specMap_algebraMap_presheafObj [X.Over (Spec (.of R))] [IsAffine X] :
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) = X.isoSpec.inv ≫ X ↘ Spec (.of R) := by
  rw [algebraMap_presheafObj (R := CommRingCat.of R)]
  simp

variable (R X) in
/-- Variant of `AlgebraicGeometry.specMap_algebraMap_presheafObj` cancelling the isomorphism
`X ≅ Spec Γ(X, ⊤)`. -/
@[reassoc]
lemma isoSpec_hom_comp_specMap_algebraMap [X.Over (Spec (.of R))] [IsAffine X] :
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) = X ↘ Spec (.of R) := by
  rw [specMap_algebraMap_presheafObj, Iso.hom_inv_id_assoc]

end AlgebraicGeometry
