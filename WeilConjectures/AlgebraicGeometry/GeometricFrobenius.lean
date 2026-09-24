/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic

/-!

# The geometric fiber of a scheme over a finite field and its Galois Frobenius

Let `k` be a field with algebraic closure `k̄`. For a scheme `X₀` over `k` with structure
morphism `f : X₀ ⟶ Spec k`, this file constructs the geometric fiber

`X := X₀ ×_{Spec k} Spec k̄`

with its projection `p_X : X ⟶ X₀` to the model over `k` and its structure morphism
`a_X : X ⟶ Spec k̄` over the algebraic closure.

If `k` is finite, the geometric Frobenius `x ↦ x ^ (1 / #k)` of `k̄`
(`FiniteField.geometricFrobenius`) induces an automorphism `σ` of `Spec k̄` over `Spec k`,
and the *geometric Galois Frobenius* of the geometric fiber is the base change

`g_X := 𝟙 X₀ × σ : X ≅ X`.

It commutes with the projection to the model, `g_X ≫ p_X = p_X`, and is *semilinear* over
`k̄`: it does not commute with the structure morphism `a_X` but satisfies
`g_X ≫ a_X = a_X ≫ σ`, and the resulting Frobenius square

```
        g_X
  X ---------> X
  |            |
a_X          a_X
  v            v
Spec k̄ --σ--> Spec k̄
```

is Cartesian (`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius`). This
square is the input for the compact-support base change isomorphisms which transport Weil
structures through `Rf_!` later on.

## Implementation notes

The classical Frobenius dictionary distinguishes several Frobenii. The one constructed
here is the *geometric Galois Frobenius* `𝟙 X₀ × σ`, which acts through the coefficients
only and is not a morphism of `k̄`-schemes. It is not the relative `#k`-power Frobenius
`Fr_{X₀} × 𝟙` of `X` over `k̄`. Since the absolute Frobenius acts as the identity on the
étale topos and `Fr^{abs}_X = (Fr_{X₀} × 𝟙) ∘ (𝟙 X₀ × σ⁻¹)`, the two induce canonically
isomorphic pullback endofunctors `(𝟙 X₀ × σ)^* ≅ (Fr_{X₀} × 𝟙)^*`, so they define
equivalent categories of Weil sheaves; the Galois version is used here because its
Frobenius square is Cartesian, which is what the compact-support base change needs.
Constructing the comparison isomorphism with `(Fr_{X₀} × 𝟙)^*` — needed for the Lefschetz
trace formula, whose intersection-theoretic side requires the `k̄`-linear endomorphism
`Fr_{X₀} × 𝟙` — is left as a TODO.

## Main definitions

- `AlgebraicGeometry.specAlgebraicClosure`: the morphism `Spec k̄ ⟶ Spec k`.
- `AlgebraicGeometry.Scheme.Hom.geometricFiber`: the geometric fiber
  `X = X₀ ×_{Spec k} Spec k̄` of a scheme over `k`, with its projection
  `geometricFiberProj` to the model and its structure morphism
  `geometricFiberToAlgebraicClosure` over `k̄`.
- `AlgebraicGeometry.specGeometricFrobenius`: the automorphism `σ` of `Spec k̄` induced by
  the geometric Frobenius of the algebraic closure of a finite field.
- `AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`: the geometric Galois Frobenius
  `g_X = 𝟙 X₀ × σ` of the geometric fiber.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius`: the Frobenius square
  is Cartesian.

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

open FiniteField Scheme

section AlgebraicClosure

variable (k : Type u) [Field k]

/-- The morphism `Spec k̄ ⟶ Spec k` induced by the inclusion of a field `k` into its
algebraic closure. The geometric fiber of a scheme over `k` is the pullback along this
morphism. -/
def specAlgebraicClosure : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

namespace Scheme.Hom

variable {k} {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The geometric fiber `X := X₀ ×_{Spec k} Spec k̄` of a scheme `X₀` over a field `k`
with structure morphism `f : X₀ ⟶ Spec k`. -/
def geometricFiber : Scheme.{u} :=
  pullback f (specAlgebraicClosure k)

/-- The projection `p_X : X ⟶ X₀` from the geometric fiber to the model over the base
field. -/
def geometricFiberProj : f.geometricFiber ⟶ X₀ :=
  pullback.fst f (specAlgebraicClosure k)

/-- The structure morphism `a_X : X ⟶ Spec k̄` of the geometric fiber over the algebraic
closure. -/
def geometricFiberToAlgebraicClosure :
    f.geometricFiber ⟶ Spec (.of (AlgebraicClosure k)) :=
  pullback.snd f (specAlgebraicClosure k)

/-- The defining square of the geometric fiber commutes:
`p_X ≫ f = a_X ≫ (Spec k̄ ⟶ Spec k)`. -/
@[reassoc]
theorem geometricFiber_condition :
    f.geometricFiberProj ≫ f =
      f.geometricFiberToAlgebraicClosure ≫ specAlgebraicClosure k :=
  pullback.condition

end Scheme.Hom

end AlgebraicClosure

section Frobenius

variable (k : Type u) [Field k] [Finite k]

/-- The automorphism `σ` of `Spec k̄` induced by the geometric Frobenius of the algebraic
closure of a finite field `k`, the image under `Spec` of the ring isomorphism
`FiniteField.geometricFrobenius`. All Frobenius operators of the Weil formalism are built
from this single automorphism. -/
def specGeometricFrobenius :
    Spec (.of (AlgebraicClosure k)) ≅ Spec (.of (AlgebraicClosure k)) :=
  Scheme.Spec.mapIso
    (geometricFrobenius k (AlgebraicClosure k)).toRingEquiv.toCommRingCatIso.op

/-- The underlying morphism of the automorphism `σ` of `Spec k̄` is the image under `Spec`
of the geometric Frobenius. This is not a `simp` lemma: the composites of `σ` are
simplified by `specGeometricFrobenius_hom_comp_specAlgebraicClosure` and by the
`Scheme.Hom.geometricGaloisFrobenius` lemmas instead. -/
theorem specGeometricFrobenius_hom :
    (specGeometricFrobenius k).hom =
      Spec.map (CommRingCat.ofHom
        (geometricFrobenius k (AlgebraicClosure k)).toRingEquiv.toRingHom) :=
  rfl

/-- The geometric Frobenius on `Spec k̄` is an automorphism over `Spec k`: the geometric
Frobenius of the algebraic closure fixes the finite base field pointwise. -/
@[reassoc (attr := simp)]
theorem specGeometricFrobenius_hom_comp_specAlgebraicClosure :
    (specGeometricFrobenius k).hom ≫ specAlgebraicClosure k = specAlgebraicClosure k := by
  simp only [specGeometricFrobenius_hom, specAlgebraicClosure, ← Spec.map_comp]
  congr 1
  ext x
  simp

namespace Scheme.Hom

variable {k} {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- The geometric Galois Frobenius `g_X := 𝟙 X₀ × σ` of the geometric fiber
`X = X₀ ×_{Spec k} Spec k̄` of a scheme over a finite field, acting through the geometric
Frobenius on the coefficients only. It is an automorphism of `X` semilinear over `k̄`: it
commutes with the projection to the model `X₀`
(`geometricGaloisFrobenius_hom_comp_geometricFiberProj`) but commutes with the structure
morphism `a_X` only up to `σ`
(`geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure`). It is not the
relative `#k`-power Frobenius of `X` over `k̄`, see the module implementation notes. -/
def geometricGaloisFrobenius : f.geometricFiber ≅ f.geometricFiber :=
  asIso (pullback.map f (specAlgebraicClosure k) f (specAlgebraicClosure k)
    (𝟙 X₀) (specGeometricFrobenius k).hom (𝟙 (Spec (.of k)))
    (by simp) (by simp))

/-- The geometric Galois Frobenius of the geometric fiber commutes with the projection to
the model: `g_X ≫ p_X = p_X`. -/
@[reassoc (attr := simp)]
theorem geometricGaloisFrobenius_hom_comp_geometricFiberProj :
    f.geometricGaloisFrobenius.hom ≫ f.geometricFiberProj = f.geometricFiberProj := by
  simp [geometricGaloisFrobenius, geometricFiberProj]

/-- The geometric Galois Frobenius of the geometric fiber is semilinear over `k̄`: the
square

```
        g_X
  X ---------> X
  |            |
a_X          a_X
  v            v
Spec k̄ --σ--> Spec k̄
```

commutes, that is `g_X ≫ a_X = a_X ≫ σ`. -/
@[reassoc (attr := simp)]
theorem geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure :
    f.geometricGaloisFrobenius.hom ≫ f.geometricFiberToAlgebraicClosure =
      f.geometricFiberToAlgebraicClosure ≫ (specGeometricFrobenius k).hom := by
  simp [geometricGaloisFrobenius, geometricFiberToAlgebraicClosure]

/-- The Frobenius square

```
        g_X
  X ---------> X
  |            |
a_X          a_X
  v            v
Spec k̄ --σ--> Spec k̄
```

is Cartesian: the geometric Galois Frobenius of the geometric fiber is the base change of
the geometric Frobenius of `Spec k̄`. This is the square whose compact-support base change
isomorphism transports Weil structures through `Rf_!`. -/
theorem isPullback_geometricGaloisFrobenius :
    IsPullback f.geometricGaloisFrobenius.hom f.geometricFiberToAlgebraicClosure
      f.geometricFiberToAlgebraicClosure (specGeometricFrobenius k).hom :=
  have h : IsPullback (f.geometricGaloisFrobenius.hom ≫ f.geometricFiberProj)
      f.geometricFiberToAlgebraicClosure f
      ((specGeometricFrobenius k).hom ≫ specAlgebraicClosure k) := by
    rw [f.geometricGaloisFrobenius_hom_comp_geometricFiberProj,
      specGeometricFrobenius_hom_comp_specAlgebraicClosure]
    exact IsPullback.of_hasPullback f (specAlgebraicClosure k)
  h.of_right f.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure
    (IsPullback.of_hasPullback f (specAlgebraicClosure k))

end Scheme.Hom

end Frobenius

end AlgebraicGeometry

end
