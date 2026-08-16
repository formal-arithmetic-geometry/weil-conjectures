/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib

/-!

# Geometric Frobenius on the geometric fiber of a scheme over a finite field

For a finite field `k` with algebraic closure `k̄`, this file sets up the finite-field
geometry underlying Weil structures:

- the *geometric Frobenius* of an algebraic extension of `k`, the inverse of the
  arithmetic Frobenius `x ↦ x ^ #k` (`FiniteField.frobeniusAlgEquivOfAlgebraic`);
- the induced automorphism `σ` of `Spec k̄` over `Spec k`;
- for a scheme `X₀` over `k` with structure morphism `f : X₀ ⟶ Spec k`, the geometric
  fiber `X := X₀ ×_{Spec k} Spec k̄` with its two projections `p_X : X ⟶ X₀` and
  `a_X : X ⟶ Spec k̄`;
- the geometric Frobenius `g_X := 𝟙 X₀ × σ : X ≅ X` of the geometric fiber.

The morphism `g_X` commutes with the projection to the model, `g_X ≫ p_X = p_X`, and is
*semilinear* over `k̄`: it does not commute with the structure morphism `a_X` but
satisfies `g_X ≫ a_X = a_X ≫ σ`, and the resulting Frobenius square

```
X  -- g_X -->  X
|              |
a_X            a_X
v              v
s  --  σ  -->  s
```

is Cartesian (`AlgebraicGeometry.Scheme.Hom.isPullback_geometricFrobenius`). This square
is the input for the compact-support base change isomorphisms which transport Weil
structures through `Rf_!` later on.

## Main definitions

- `FiniteField.geometricFrobenius`: the geometric Frobenius, the inverse of the
  arithmetic Frobenius `FiniteField.frobeniusAlgEquivOfAlgebraic`.
- `AlgebraicGeometry.specAlgebraicClosure`: the morphism `Spec k̄ ⟶ Spec k`.
- `AlgebraicGeometry.specGeometricFrobenius`: the automorphism `σ` of `Spec k̄` induced
  by the geometric Frobenius.
- `AlgebraicGeometry.Scheme.Hom.geometricFiber`: the geometric fiber
  `X = X₀ ×_{Spec k} Spec k̄` of a scheme over `k`.
- `AlgebraicGeometry.Scheme.Hom.geometricFrobenius`: the geometric Frobenius
  `g_X = 𝟙 X₀ × σ` on the geometric fiber.
- `AlgebraicGeometry.Scheme.Hom.isPullback_geometricFrobenius`: the Frobenius square is
  Cartesian.
- `AlgebraicGeometry.Scheme.Hom.geometricFiberMap`: the geometric base change
  `h̄ : X ⟶ Y` of a morphism `h : X₀ ⟶ Y₀` over `k`.
- `AlgebraicGeometry.Scheme.Hom.isPullback_geometricFrobenius_geometricFiberMap`: the
  geometric base change intertwines the geometric Frobenii, `g_Y ∘ h̄ = h̄ ∘ g_X`, and
  the resulting Frobenius square is Cartesian.

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace FiniteField

variable (k : Type*) [Field k] [Finite k]
variable (K : Type*) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

/-- The geometric Frobenius of an algebraic extension `K` of a finite field `k`, the
inverse of the arithmetic Frobenius `x ↦ x ^ #k`
(`FiniteField.frobeniusAlgEquivOfAlgebraic`). -/
def geometricFrobenius : K ≃ₐ[k] K :=
  letI : Fintype k := Fintype.ofFinite k
  (frobeniusAlgEquivOfAlgebraic k K).symm

@[simp]
theorem geometricFrobenius_pow_card (x : K) :
    geometricFrobenius k K x ^ Nat.card k = x := by
  letI : Fintype k := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card]
  have h : geometricFrobenius k K x ^ Fintype.card k =
      frobeniusAlgEquivOfAlgebraic k K (geometricFrobenius k K x) := by
    rw [coe_frobeniusAlgEquivOfAlgebraic]
  rw [h]
  exact (frobeniusAlgEquivOfAlgebraic k K).apply_symm_apply x

end FiniteField

namespace AlgebraicGeometry

open FiniteField Scheme

variable (k : Type u) [Field k] [Finite k]

/-- The morphism `Spec k̄ ⟶ Spec k` induced by the inclusion of a finite field `k` into
its algebraic closure. The geometric fiber of a scheme over `k` is the pullback along
this morphism. -/
def specAlgebraicClosure : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- The automorphism `σ` of `Spec k̄` induced by the geometric Frobenius of the
algebraic closure of a finite field `k`. All Frobenius operators of the Weil formalism
are built from this single automorphism. -/
def specGeometricFrobenius :
    Spec (.of (AlgebraicClosure k)) ≅ Spec (.of (AlgebraicClosure k)) where
  hom := Spec.map (CommRingCat.ofHom
    (geometricFrobenius k (AlgebraicClosure k) : AlgebraicClosure k →+* AlgebraicClosure k))
  inv := Spec.map (CommRingCat.ofHom
    ((geometricFrobenius k (AlgebraicClosure k)).symm :
      AlgebraicClosure k →+* AlgebraicClosure k))
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp

/-- The geometric Frobenius on `Spec k̄` is an automorphism over `Spec k`: the geometric
Frobenius of the algebraic closure fixes the finite base field pointwise. -/
@[reassoc (attr := simp)]
theorem specGeometricFrobenius_hom_specAlgebraicClosure :
    (specGeometricFrobenius k).hom ≫ specAlgebraicClosure k = specAlgebraicClosure k := by
  simp only [specGeometricFrobenius, specAlgebraicClosure]
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

namespace Scheme.Hom

variable {k} {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The geometric fiber `X := X₀ ×_{Spec k} Spec k̄` of a scheme `X₀` over a finite
field `k` with structure morphism `f : X₀ ⟶ Spec k`. -/
def geometricFiber : Scheme.{u} :=
  pullback f (specAlgebraicClosure k)

/-- The projection `p_X : X ⟶ X₀` from the geometric fiber to the model over the finite
base field. -/
def geometricFiberProj : f.geometricFiber ⟶ X₀ :=
  pullback.fst f (specAlgebraicClosure k)

/-- The structure morphism `a_X : X ⟶ Spec k̄` of the geometric fiber. -/
def geometricFiberStruct : f.geometricFiber ⟶ Spec (.of (AlgebraicClosure k)) :=
  pullback.snd f (specAlgebraicClosure k)

omit [Finite k] in
@[reassoc]
theorem geometricFiberProj_comp :
    f.geometricFiberProj ≫ f = f.geometricFiberStruct ≫ specAlgebraicClosure k :=
  pullback.condition

/-- The geometric Frobenius `g_X := 𝟙 X₀ × σ` on the geometric fiber
`X = X₀ ×_{Spec k} Spec k̄`, acting through the geometric Frobenius on the coefficients
only. It is an automorphism of `X` semilinear over `k̄`: it commutes with the projection
to the model `X₀` but only commutes with the structure morphism `a_X` up to `σ`, see
`geometricFrobenius_hom_struct`. -/
def geometricFrobenius : f.geometricFiber ≅ f.geometricFiber :=
  asIso (pullback.map f (specAlgebraicClosure k) f (specAlgebraicClosure k)
    (𝟙 X₀) (specGeometricFrobenius k).hom (𝟙 (Spec (.of k)))
    (by simp) (by simp))

/-- The geometric Frobenius of the geometric fiber commutes with the projection to the
model: `p_X ∘ g_X = p_X`. -/
@[reassoc (attr := simp)]
theorem geometricFrobenius_hom_proj :
    f.geometricFrobenius.hom ≫ f.geometricFiberProj = f.geometricFiberProj := by
  simp [geometricFrobenius, geometricFiberProj]

/-- The geometric Frobenius of the geometric fiber is semilinear over `k̄`:
`a_X ∘ g_X = σ ∘ a_X`. -/
@[reassoc (attr := simp)]
theorem geometricFrobenius_hom_struct :
    f.geometricFrobenius.hom ≫ f.geometricFiberStruct =
      f.geometricFiberStruct ≫ (specGeometricFrobenius k).hom := by
  simp [geometricFrobenius, geometricFiberStruct]

/-- The Frobenius square

```
X  -- g_X -->  X
|              |
a_X            a_X
v              v
s  --  σ  -->  s
```

is Cartesian: the geometric Frobenius on the geometric fiber is the base change of the
geometric Frobenius on `Spec k̄`. This is the square whose compact-support base change
isomorphism transports Weil structures through `Rf_!`. -/
theorem isPullback_geometricFrobenius :
    IsPullback f.geometricFrobenius.hom f.geometricFiberStruct f.geometricFiberStruct
      (specGeometricFrobenius k).hom := by
  have h : IsPullback (f.geometricFrobenius.hom ≫ f.geometricFiberProj)
      f.geometricFiberStruct f ((specGeometricFrobenius k).hom ≫ specAlgebraicClosure k) := by
    rw [f.geometricFrobenius_hom_proj, specGeometricFrobenius_hom_specAlgebraicClosure]
    exact IsPullback.of_hasPullback f (specAlgebraicClosure k)
  exact h.of_right f.geometricFrobenius_hom_struct
    (IsPullback.of_hasPullback f (specAlgebraicClosure k))

section GeometricFiberMap

variable {Y₀ : Scheme.{u}} (fY : Y₀ ⟶ Spec (.of k)) (h : X₀ ⟶ Y₀)

/-- The geometric base change `h̄ : X ⟶ Y` of a morphism `h : X₀ ⟶ Y₀` over the finite
base field, between the geometric fibers of `X₀` (with structure morphism `h ≫ fY`) and
of `Y₀`. -/
def geometricFiberMap : (h ≫ fY).geometricFiber ⟶ fY.geometricFiber :=
  pullback.map (h ≫ fY) (specAlgebraicClosure k) fY (specAlgebraicClosure k) h
    (𝟙 _) (𝟙 _) (by simp) (by simp)

omit [Finite k] in
/-- The geometric base change lies over the original morphism: `p_Y ∘ h̄ = h ∘ p_X`. -/
@[reassoc (attr := simp)]
theorem geometricFiberMap_proj :
    fY.geometricFiberMap h ≫ fY.geometricFiberProj = (h ≫ fY).geometricFiberProj ≫ h := by
  simp [geometricFiberMap, geometricFiberProj]

omit [Finite k] in
/-- The geometric base change is a morphism over `Spec k̄`: `a_Y ∘ h̄ = a_X`. -/
@[reassoc (attr := simp)]
theorem geometricFiberMap_struct :
    fY.geometricFiberMap h ≫ fY.geometricFiberStruct = (h ≫ fY).geometricFiberStruct := by
  simp [geometricFiberMap, geometricFiberStruct]

/-- The geometric base change intertwines the geometric Frobenii: `h̄ ∘ g_X = g_Y ∘ h̄`.
Both act through the geometric Frobenius on the coefficients only. -/
@[reassoc]
theorem geometricFrobenius_hom_geometricFiberMap :
    (h ≫ fY).geometricFrobenius.hom ≫ fY.geometricFiberMap h =
      fY.geometricFiberMap h ≫ fY.geometricFrobenius.hom := by
  apply pullback.hom_ext <;> simp [geometricFrobenius, geometricFiberMap]

/-- The Frobenius square

```
X  -- g_X -->  X
|              |
h̄              h̄
v              v
Y  -- g_Y -->  Y
```

of the geometric base change of a morphism over the finite base field is Cartesian: the
horizontal morphisms are isomorphisms. Its compact-support base change isomorphism
transports Weil structures through `Rh̄_!`. -/
theorem isPullback_geometricFrobenius_geometricFiberMap :
    IsPullback (h ≫ fY).geometricFrobenius.hom (fY.geometricFiberMap h)
      (fY.geometricFiberMap h) fY.geometricFrobenius.hom :=
  IsPullback.of_horiz_isIso ⟨fY.geometricFrobenius_hom_geometricFiberMap h⟩

end GeometricFiberMap

end Scheme.Hom

end AlgebraicGeometry

end
