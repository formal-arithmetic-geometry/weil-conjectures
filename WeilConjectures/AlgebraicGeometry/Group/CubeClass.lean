/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackConstant

/-!
# The cube class of a line bundle on a monoid scheme

Let `B` be a scheme, let `G` be a monoid scheme over `B` and let `ℓ` be the class in the Picard
group of `G` of a line bundle `L`. To three `W`-points `f`, `g`, `h` of `G` this file attaches
the class

`Θ(L)(f, g, h) := (f+g+h)^*L ⊗ (f+g)^*L⁻¹ ⊗ (f+h)^*L⁻¹ ⊗ (g+h)^*L⁻¹ ⊗ f^*L ⊗ g^*L ⊗ h^*L`

in the Picard group of `W`, the **cube class** of `ℓ` at `f`, `g`, `h`. Two of its formal
properties are proved here and need nothing beyond the monoid structure of `G`:

* it is natural in the `W`-points, i.e. compatible with pulling `f`, `g`, `h` back along a
  morphism `σ : V ⟶ W` (`AlgebraicGeometry.Scheme.Pic.map_cubeClass`);
* it is trivial as soon as one of the three points is the unit — six of the seven factors
  cancel in pairs and the seventh is a pullback along a constant morphism, hence trivial as
  soon as the Picard group of the base is trivial
  (`AlgebraicGeometry.Scheme.Pic.cubeClass_one_left` and its two companions).

The cube identity is the assertion that the cube class is *always* trivial when `G` is an
abelian variety; that is `thm:cube-abelian` of the blueprint, proved in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.CubeIdentity`. Nothing about abelian
varieties, and nothing about the base being the spectrum of a field, enters the present file.

## Main definitions

- `AlgebraicGeometry.Scheme.Pic.cubeClass`: the cube class of `ℓ` at three `W`-points of `G`.

## Main results

- `AlgebraicGeometry.Scheme.Pic.map_cubeClass`: naturality of the cube class.
- `AlgebraicGeometry.Scheme.Pic.cubeClass_comm_left`,
  `AlgebraicGeometry.Scheme.Pic.cubeClass_comm_right`: the cube class of a *commutative* monoid
  scheme is symmetric in its three points.
- `AlgebraicGeometry.Scheme.Pic.cubeClass_one_left`,
  `AlgebraicGeometry.Scheme.Pic.cubeClass_one_middle`,
  `AlgebraicGeometry.Scheme.Pic.cubeClass_one_right`: the cube class is trivial as soon as one
  of the three points is the unit.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry.Scheme.Pic

variable {B : Scheme.{u}} {G V W : Over B} [MonObj G]

/-- The class in the Picard group of `W` of the **cube bundle**

`(f+g+h)^*L ⊗ (f+g)^*L⁻¹ ⊗ (f+h)^*L⁻¹ ⊗ (g+h)^*L⁻¹ ⊗ f^*L ⊗ g^*L ⊗ h^*L`

attached to the class `ℓ` of a line bundle `L` on a monoid scheme `G` over `B` and to three
`W`-points `f`, `g`, `h` of `G`. The cube identity says that it is trivial when `G` is an
abelian variety, see `AlgebraicGeometry.Scheme.Pic.cubeClass_eq_one`.

Taking `W = G × G × G` and `f`, `g`, `h` the three projections gives the class of the bundle
`Θ(L)` of the blueprint. -/
noncomputable def cubeClass (f g h : W ⟶ G) (ℓ : G.left.Pic) : W.left.Pic :=
  Pic.map (f * g * h).left ℓ * (Pic.map (f * g).left ℓ)⁻¹ * (Pic.map (f * h).left ℓ)⁻¹ *
    (Pic.map (g * h).left ℓ)⁻¹ * Pic.map f.left ℓ * Pic.map g.left ℓ * Pic.map h.left ℓ

/-- **The cube class is natural in the points**: pulling it back along `σ : V ⟶ W` is the cube
class of the three `V`-points obtained by composing with `σ`.

```
              σ                f, g, h
       V ──────────▶ W ──────────────────▶ G
        ╲                                ↗
         ╲───────── σ ≫ f, … ───────────╱
```

Both sides unfold to the same seven pullbacks because pullback of Picard classes is
functorial and because composing with `σ` is a homomorphism of the groups of points
(`CategoryTheory.MonObj.comp_mul`). -/
theorem map_cubeClass (σ : V ⟶ W) (f g h : W ⟶ G) (ℓ : G.left.Pic) :
    Pic.map σ.left (cubeClass f g h ℓ) = cubeClass (σ ≫ f) (σ ≫ g) (σ ≫ h) ℓ := by
  simp only [cubeClass, map_mul, map_inv, ← Pic.map_comp_apply, ← Over.comp_left,
    MonObj.comp_mul]

section Comm

variable [IsCommMonObj G]

/-- **The cube class is symmetric in its first two points**, for a commutative monoid scheme:
exchanging `f` and `g` exchanges the two factors `(f+h)^*L⁻¹` and `(g+h)^*L⁻¹` and the two
factors `f^*L` and `g^*L`, and fixes the remaining three. -/
theorem cubeClass_comm_left (f g h : W ⟶ G) (ℓ : G.left.Pic) :
    cubeClass f g h ℓ = cubeClass g f h ℓ := by
  simp only [cubeClass, mul_comm g f]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- **The cube class is symmetric in its last two points**, for a commutative monoid scheme:
exchanging `g` and `h` exchanges the two factors `(f+g)^*L⁻¹` and `(f+h)^*L⁻¹` and the two
factors `g^*L` and `h^*L`, and fixes the remaining three. -/
theorem cubeClass_comm_right (f g h : W ⟶ G) (ℓ : G.left.Pic) :
    cubeClass f g h ℓ = cubeClass f h g ℓ := by
  simp only [cubeClass, mul_assoc, mul_comm h g]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Comm

variable [Subsingleton B.Pic]

/-- **The cube class is trivial as soon as the first of the three points is the unit.**

With `f = 1` the first factor becomes `(g+h)^*L` and cancels against the fourth, the second
becomes `g^*L` and cancels against the sixth, the third becomes `h^*L` and cancels against the
seventh; what is left is `1^*L`, trivial by
`AlgebraicGeometry.Scheme.Pic.map_one_left`. -/
theorem cubeClass_one_left (g h : W ⟶ G) (ℓ : G.left.Pic) : cubeClass 1 g h ℓ = 1 := by
  simp only [cubeClass, one_mul, Pic.map_one_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

/-- **The cube class is trivial as soon as the second of the three points is the unit**, by
`AlgebraicGeometry.Scheme.Pic.cubeClass_one_left` and the symmetry
`AlgebraicGeometry.Scheme.Pic.cubeClass_comm_left`. -/
theorem cubeClass_one_middle [IsCommMonObj G] (f h : W ⟶ G) (ℓ : G.left.Pic) :
    cubeClass f 1 h ℓ = 1 := by
  rw [cubeClass_comm_left, cubeClass_one_left]

/-- **The cube class is trivial as soon as the third of the three points is the unit**, by
`AlgebraicGeometry.Scheme.Pic.cubeClass_one_middle` and the symmetry
`AlgebraicGeometry.Scheme.Pic.cubeClass_comm_right`. -/
theorem cubeClass_one_right [IsCommMonObj G] (f g : W ⟶ G) (ℓ : G.left.Pic) :
    cubeClass f g 1 ℓ = 1 := by
  rw [cubeClass_comm_right, cubeClass_one_middle]

end AlgebraicGeometry.Scheme.Pic
