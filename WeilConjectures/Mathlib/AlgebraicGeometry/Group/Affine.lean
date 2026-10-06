/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Naturality of `Spec.mapMulEquiv`

Precomposing the morphism of affine schemes `Spec T ⟶ Spec S` given by an algebra homomorphism
`S → T` with `Spec U ⟶ Spec T`, for an algebra homomorphism `T → U`, corresponds to composing the
algebra homomorphisms.

Every morphism from a scheme `X` over `Spec k` to an affine scheme over `Spec k` factors through
the canonical morphism `X ⟶ Spec Γ(X, ⊤)` (`AlgebraicGeometry.Scheme.exists_toSpecΓOver_comp`),
so that points with values in `X` are determined by points with values in the `k`-algebra
`Γ(X, ⊤)`.
-/

@[expose] public section

universe u

open CategoryTheory WithConv

namespace AlgebraicGeometry

variable {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U] [Bialgebra R S]
  [Algebra R T] [Algebra R U]

/-- The square
```
Spec U ──Spec φ──▶ Spec T
     ╲                │
      ╲               │ Spec ψ
       ╲              ▼
        ╲──Spec (φ ∘ ψ)──▶ Spec S
```
over `Spec R` commutes. -/
theorem Spec.map_asOver_comp_mapMulEquiv (φ : T →ₐ[R] U) (ψ : WithConv (S →ₐ[R] T)) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (.of R)) ≫ Spec.mapMulEquiv ψ =
      Spec.mapMulEquiv (toConv (φ.comp ψ.ofConv)) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

section GlobalSections

variable {k : Type u} [CommRing k] (X : Over (Spec (.of k)))

/-- The `k`-algebra structure on the global sections `Γ(X, ⊤)` of a scheme `X` over `Spec k`. -/
noncomputable abbrev Scheme.algebraΓOfOver : Algebra k Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom.toAlgebra

attribute [local instance] Scheme.algebraΓOfOver

theorem Scheme.toSpecΓ_comp_over :
    X.left.toSpecΓ ≫ (Spec Γ(X.left, ⊤) ↘ Spec (.of k)) = X.hom := by
  change _ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- The canonical morphism `X ⟶ Spec Γ(X, ⊤)` of schemes over `Spec k`. -/
noncomputable def Scheme.toSpecΓOver :
    letI := Scheme.algebraΓOfOver X
    X ⟶ (Spec (.of Γ(X.left, ⊤))).asOver (Spec (.of k)) :=
  Over.homMk X.left.toSpecΓ (Scheme.toSpecΓ_comp_over X)

variable {X} in
/-- Every morphism from `X` to an affine scheme over `Spec k` factors through
`X ⟶ Spec Γ(X, ⊤)`. -/
theorem Scheme.exists_toSpecΓOver_comp {Y : Over (Spec (.of k))} [IsAffine Y.left] (a : X ⟶ Y) :
    ∃ a' : (Spec (.of Γ(X.left, ⊤))).asOver (Spec (.of k)) ⟶ Y,
      Scheme.toSpecΓOver X ≫ a' = a := by
  have ha : a.left ≫ Y.hom = X.hom := Over.w a
  refine ⟨Over.homMk (Spec.map a.left.appTop ≫ inv Y.left.toSpecΓ) ?_, ?_⟩
  · change (Spec.map a.left.appTop ≫ inv Y.left.toSpecΓ : Spec Γ(X.left, ⊤) ⟶ Y.left) ≫ Y.hom =
      Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)
    have hY : inv Y.left.toSpecΓ ≫ Y.hom =
        Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ Y.hom.appTop) := by
      rw [IsIso.inv_comp_eq, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
        ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
    rw [Category.assoc, hY, ← Spec.map_comp, ← ha, Scheme.Hom.comp_appTop, Category.assoc]
  · ext1
    change X.left.toSpecΓ ≫ _ ≫ _ = _
    rw [← Scheme.toSpecΓ_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]

end GlobalSections

end AlgebraicGeometry
