/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Fibre products of affine schemes over the terminal scheme

`Mathlib.AlgebraicGeometry.Pullbacks` computes the fibre product of `Spec A` and `Spec B` over
`Spec R` as `Spec (A ⊗[R] B)`. Since `Spec (ULift ℤ)` is a terminal scheme, this also computes
the fibre product over the terminal scheme `⊤_ Scheme`, which is the shape in which products of
schemes appear in practice.

## Main declarations

* `AlgebraicGeometry.isPullback_terminalFrom_spec`: the square with projections
  `Spec (A ⊗[ULift ℤ] B) ⟶ Spec A` and `Spec (A ⊗[ULift ℤ] B) ⟶ Spec B` over `⊤_ Scheme` is
  cartesian.
* `AlgebraicGeometry.pullbackTerminalSpecIso`: the induced isomorphism
  `pullback (terminal.from (Spec A)) (terminal.from (Spec B)) ≅ Spec (A ⊗[ULift ℤ] B)`.

Note that `IsAffine (pullback (terminal.from X) (terminal.from Y))` for affine `X` and `Y` is
already an instance in Mathlib, since `⊤_ Scheme` is affine.

## Implementation notes

The `ULift ℤ`-algebra structure on a commutative ring `A : Type u` is `ULift.algebra'`, which is a
def rather than an instance; it is enabled as a local instance in this file.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct CommRingCat

namespace AlgebraicGeometry

attribute [local instance] ULift.algebra'

variable (A B : Type u) [CommRing A] [CommRing B]

/-- `Spec (A ⊗[ULift ℤ] B)`, with the two maps induced by `a ↦ a ⊗ₜ 1` and `b ↦ 1 ⊗ₜ b`, is the
fibre product of `Spec A` and `Spec B` over the terminal scheme. -/
theorem isPullback_terminalFrom_spec :
    IsPullback (Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ULift.{u} ℤ) (A := A) (B := B))))
      (Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
        (A := A) (B := B)).toRingHom))
      (terminal.from (Spec (.of A))) (terminal.from (Spec (.of B))) := by
  have h : IsPullback (Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := ULift.{u} ℤ) (A := A) (B := B))))
      (Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
        (A := A) (B := B)).toRingHom))
      (Spec.map (ofHom (algebraMap (ULift.{u} ℤ) A)))
      (Spec.map (ofHom (algebraMap (ULift.{u} ℤ) B))) := ?_
  · exact h.of_isTerminal specULiftZIsTerminal terminalIsTerminal
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso (ULift.{u} ℤ) A B).symm
    (pullbackSpecIso_inv_fst ..) (pullbackSpecIso_inv_snd ..)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  simp [Algebra.TensorProduct.algebraMap_def]

/-- The fibre product of `Spec A` and `Spec B` over the terminal scheme is
`Spec (A ⊗[ULift ℤ] B)`. -/
noncomputable def pullbackTerminalSpecIso :
    pullback (terminal.from (Spec (.of A))) (terminal.from (Spec (.of B))) ≅
      Spec (.of (A ⊗[ULift.{u} ℤ] B)) :=
  (isPullback_terminalFrom_spec A B).isoPullback.symm

/-- The composition of the inverse of `pullbackTerminalSpecIso A B` with the first projection is
`Spec.map` of the ring morphism `a ↦ a ⊗ₜ 1`. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_inv_fst :
    (pullbackTerminalSpecIso A B).inv ≫ pullback.fst _ _ =
      Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ULift.{u} ℤ))) :=
  (isPullback_terminalFrom_spec A B).isoPullback_hom_fst

/-- The composition of the inverse of `pullbackTerminalSpecIso A B` with the second projection is
`Spec.map` of the ring morphism `b ↦ 1 ⊗ₜ b`. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_inv_snd :
    (pullbackTerminalSpecIso A B).inv ≫ pullback.snd _ _ =
      Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
        (A := A) (B := B)).toRingHom) :=
  (isPullback_terminalFrom_spec A B).isoPullback_hom_snd

/-- The composition of `pullbackTerminalSpecIso A B` with `Spec.map` of the ring morphism
`a ↦ a ⊗ₜ 1` is the first projection. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_hom_fst :
    (pullbackTerminalSpecIso A B).hom ≫
        Spec.map (ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ULift.{u} ℤ))) =
      pullback.fst _ _ := by
  rw [← pullbackTerminalSpecIso_inv_fst, Iso.hom_inv_id_assoc]

/-- The composition of `pullbackTerminalSpecIso A B` with `Spec.map` of the ring morphism
`b ↦ 1 ⊗ₜ b` is the second projection. -/
@[reassoc (attr := simp)]
lemma pullbackTerminalSpecIso_hom_snd :
    (pullbackTerminalSpecIso A B).hom ≫
        Spec.map (ofHom (Algebra.TensorProduct.includeRight (R := ULift.{u} ℤ)
          (A := A) (B := B)).toRingHom) = pullback.snd _ _ := by
  rw [← pullbackTerminalSpecIso_inv_snd, Iso.hom_inv_id_assoc]

end AlgebraicGeometry
