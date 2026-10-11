/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# The geometric point over a point of a scheme

For a point `y` of a scheme `Y`, `Scheme.fromSpecResidueField` is the canonical morphism
`Spec κ(y) ⟶ Y`. This file names its composite with `Spec κ(y)‾ ⟶ Spec κ(y)`, where `κ(y)‾` is
the algebraic closure of `κ(y)`.

We also record that whether a residue field extension is étale, that is finite separable, is
insensitive to composing with a morphism inducing isomorphisms of residue fields, such as an open
immersion, and two facts on morphisms from spectra of fields: precomposition with
`Spec L ⟶ Spec K` for a field extension `K ⟶ L` is injective
(`AlgebraicGeometry.Scheme.SpecMap_comp_injective`), and two field-valued points with the same
image have a common field extension
(`AlgebraicGeometry.Scheme.exists_SpecMap_comp_eq_of_apply_eq`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The geometric point `Spec κ(y)‾ ⟶ Y` over a point `y` of a scheme `Y`, where `κ(y)‾` is the
algebraic closure of the residue field `κ(y)`. It is the composite

```
  Spec κ(y)‾ ──▶ Spec κ(y) ── fromSpecResidueField y ──▶ Y
```
-/
noncomputable def fromSpecAlgebraicClosureResidueField (Y : Scheme.{u}) (y : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure _))) ≫
    Y.fromSpecResidueField y

/-- If `g` induces an isomorphism of residue fields at `x`, then `κ(x)` is étale over the residue
field of its image under `g ≫ h` if and only if `κ(g x)` is. -/
lemma Hom.etale_residueFieldMap_comp_iff_left {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (x : X) [IsIso (g.residueFieldMap x)] :
    ((g ≫ h).residueFieldMap x).hom.Etale ↔ (h.residueFieldMap (g x)).hom.Etale := by
  rw [residueFieldMap_comp]
  exact RingHom.Etale.respectsIso.cancel_right_isIso _ _

/-- If `h` induces an isomorphism of residue fields at `g x`, then `κ(x)` is étale over the
residue field of its image under `g ≫ h` if and only if it is étale over `κ(g x)`. -/
lemma Hom.etale_residueFieldMap_comp_iff_right {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (x : X) [IsIso (h.residueFieldMap (g x))] :
    ((g ≫ h).residueFieldMap x).hom.Etale ↔ (g.residueFieldMap x).hom.Etale := by
  rw [residueFieldMap_comp]
  exact RingHom.Etale.respectsIso.cancel_left_isIso (h.residueFieldMap (g x))
    (g.residueFieldMap x)

lemma Hom.etale_residueFieldMap_congr {X Y : Scheme.{u}} {g h : X ⟶ Y} (e : g = h) (x : X) :
    (g.residueFieldMap x).hom.Etale ↔ (h.residueFieldMap x).hom.Etale := by
  subst e
  rfl

/-- A morphism `p : Spec K ⟶ X` from the spectrum of a field factors through `Spec κ(x)` for its
image point `x`, through a field embedding `κ(x) ⟶ K`. -/
lemma exists_eq_spec_map_comp_fromSpecResidueField {K : Type u} [Field K] {X : Scheme.{u}}
    (p : Spec (.of K) ⟶ X) (x : X) (hx : p.base (IsLocalRing.closedPoint K) = x) :
    ∃ ι : X.residueField x ⟶ .of K, p = Spec.map ι ≫ X.fromSpecResidueField x := by
  subst hx
  exact ⟨_, ((SpecToEquivOfField K X).left_inv p).symm⟩


section FieldPoints

open IsLocalRing

/-- The morphism `Spec L ⟶ Spec K` induced by a field extension maps the point to the point. -/
lemma SpecMap_apply_closedPoint {K L : Type u} [Field K] [Field L]
    (α : CommRingCat.of K ⟶ CommRingCat.of L) :
    Spec.map α (closedPoint L) = closedPoint K :=
  Subsingleton.elim _ _

/-- Precomposition with `Spec L ⟶ Spec K` for a field extension `K ⟶ L` is injective on
morphisms `Spec K ⟶ X`. -/
lemma SpecMap_comp_injective {X : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    (α : CommRingCat.of K ⟶ CommRingCat.of L) {g₁ g₂ : Spec (.of K) ⟶ X}
    (h : Spec.map α ≫ g₁ = Spec.map α ≫ g₂) : g₁ = g₂ := by
  have hx : g₁ (closedPoint K) = g₂ (closedPoint K) := by
    have := congr($h (closedPoint L))
    simpa only [Scheme.Hom.comp_apply, SpecMap_apply_closedPoint] using this
  obtain ⟨c₁, hc₁⟩ := exists_eq_spec_map_comp_fromSpecResidueField g₁ _ rfl
  obtain ⟨c₂, hc₂⟩ := exists_eq_spec_map_comp_fromSpecResidueField g₂ _ rfl
  rw [← X.residueFieldCongr_fromSpecResidueField hx, ← Category.assoc, ← Spec.map_comp] at hc₂
  rw [hc₁, hc₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective ((cancel_mono _).1 h)
  have : c₁ = (X.residueFieldCongr hx).hom ≫ c₂ := by
    ext a
    exact α.hom.injective congr(($h').hom a)
  rw [hc₁, hc₂, this]


/-- Two field-valued points of `S` with the same image have a common field extension. -/
lemma exists_SpecMap_comp_eq_of_apply_eq {S : Scheme.{u}} {K L : Type u} [Field K] [Field L]
    (σ : Spec (.of K) ⟶ S) (τ : Spec (.of L) ⟶ S)
    (h : σ (closedPoint K) = τ (closedPoint L)) :
    ∃ (Ω : Type u) (_ : Field Ω) (α : CommRingCat.of K ⟶ CommRingCat.of Ω)
      (β : CommRingCat.of L ⟶ CommRingCat.of Ω), Spec.map α ≫ σ = Spec.map β ≫ τ := by
  obtain ⟨a, ha⟩ := exists_eq_spec_map_comp_fromSpecResidueField σ _ rfl
  obtain ⟨b, hb⟩ := exists_eq_spec_map_comp_fromSpecResidueField τ _ rfl
  rw [← S.residueFieldCongr_fromSpecResidueField h, ← Category.assoc,
    ← Spec.map_comp] at hb
  let F := S.residueField (σ (closedPoint K))
  let b' := (S.residueFieldCongr h).hom ≫ b
  let : Algebra F K := a.hom.toAlgebra
  let : Algebra F L := b'.hom.toAlgebra
  have : Nontrivial (TensorProduct F K L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F K L
      a.hom.injective b'.hom.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct F K L)
  let := Ideal.Quotient.field m
  refine ⟨TensorProduct F K L ⧸ m, inferInstance,
    CommRingCat.ofHom ((Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom),
    CommRingCat.ofHom ((Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight (R := F) (A := K)).toRingHom), ?_⟩
  refine (congrArg (Spec.map _ ≫ ·) ha).trans (Eq.trans ?_ (congrArg (Spec.map _ ≫ ·) hb).symm)
  dsimp only
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext x
  change Ideal.Quotient.mk m (algebraMap F K x ⊗ₜ[F] (1 : L)) =
    Ideal.Quotient.mk m ((1 : K) ⊗ₜ[F] algebraMap F L x)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end FieldPoints

end AlgebraicGeometry.Scheme
