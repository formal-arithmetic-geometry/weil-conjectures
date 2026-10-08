/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The theorem of the cube

For an invertible module `L` on an abelian scheme `A` over a base `S` with unit section
`e : S ⟶ A`, the seven pullbacks of `L` and `L⁻¹` along the partial sum maps `A × A × A ⟶ A`
multiply to the pullback `π₃^* (e^* L)` of `L` along the zero map `A × A × A ⟶ S ⟶ A`, by a
canonical isomorphism. As a consequence the pullback of a symmetric invertible module along
multiplication by `n` is its `n²`-th tensor power, up to a power of `π^* (e^* L)`.

The partial sum maps are written using the group structure on `X ⟶ A` coming from
`CategoryTheory.GrpObj.Hom.group`: writing `p₁ = fst _ _ ≫ fst _ _`, `p₂ = fst _ _ ≫ snd _ _`
and `p₃ = snd _ _` for the three projections `(A ⊗ A) ⊗ A ⟶ A`, the partial sum `m_{i₁…i_t}` is
the product `p_{i₁} * ⋯ * p_{i_t}`. Naming the eight vertices of the cube `(ε₁, ε₂, ε₃)` with
`εᵢ ∈ {0, 1}`, the cube relation is the alternating product over the vertices:

```
        (0,1,1) ───────── (1,1,1)
         ╱ │               ╱ │
   (0,1,0) ─┼───────(1,1,0)  │
      │   (0,0,1) ──────│── (1,0,1)
      │  ╱              │  ╱
   (0,0,0) ─────────(1,0,0)
```

the vertex `(ε₁, ε₂, ε₃)` contributing `m_{i : εᵢ = 1}^* L` with sign `(-1)^(ε₁ + ε₂ + ε₃)`. The
vertex `(0, 0, 0)` is the zero map `1 = toUnit _ ≫ η[A]`, that is `e ∘ π₃` for the structure
map `π₃ = toUnit _ : A × A × A ⟶ S`, and its term `π₃^* (e^* L)` is what makes the relation
hold over an arbitrary base.

## Main definitions

- `AlgebraicGeometry.cubeIso`: the theorem of the cube, as the canonical isomorphism
  `C₇(L) ≅ π₃^* (e^* L)`.
- `AlgebraicGeometry.overPullbackNpowIdIso`: `[n]^* N ⊗ π^* (e^* N)^{⊗ n²} ≅ N^{⊗ n²} ⊗ π^* (e^* N)`
  for `N` with a chosen symmetry `[-1]^* N ≅ N`.

## TODO

Both isomorphisms are `sorry`. The eight-term form of the theorem of the cube, the canonical
trivialisation `Θ(L) = C₇(L) ⊗ π₃^* (e^* L)⁻¹ ≅ 𝒪`, follows from `AlgebraicGeometry.cubeIso`
and `AlgebraicGeometry.Scheme.Modules.evaluationIso` once the pullback functors are known to be
monoidal.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme.Modules

variable {S : Scheme.{u}}

/-- Blueprint `sk-prop-av-cube`: The theorem of the cube.

Let `A` be an abelian scheme over a base `S` with unit section `e : S ⟶ A`, and let `L` be an
invertible `𝒪_A`-module. For `1 ≤ i₁ < ⋯ < i_t ≤ 3` let `m_{i₁…i_t} : A × A × A ⟶ A` be the
partial sum map `(x₁, x₂, x₃) ↦ x_{i₁} + ⋯ + x_{i_t}`, and let `π₃ : A × A × A ⟶ S` be the
structure map, so that `e ∘ π₃` is the zero map. The seven-term invertible module

`C₇(L) = m₁₂₃^* L ⊗ m₁₂^* L⁻¹ ⊗ m₁₃^* L⁻¹ ⊗ m₂₃^* L⁻¹ ⊗ m₁^* L ⊗ m₂^* L ⊗ m₃^* L`

is canonically isomorphic to `π₃^* (e^* L)`:

`c_L : C₇(L) ≅ π₃^* (e^* L)`.

Over a field, or whenever `e^* L` is trivial, the right-hand side is `𝒪` and this is the
blueprint statement `m₁₂₃^* L ⊗ m₁^* L ⊗ m₂^* L ⊗ m₃^* L ≅ m₁₂^* L ⊗ m₁₃^* L ⊗ m₂₃^* L`; over a
general base the term `π₃^* (e^* L)` cannot be dropped: for `L = π^* M` with `M` invertible on
`S` all seven partial-sum pullbacks of `L` are `π₃^* M`, so `C₇(L) = π₃^* M`, which is trivial
only if `M` is.

The isomorphism is canonical, natural under isomorphisms of `L` and compatible with arbitrary
base change: on each coordinate face `xᵢ = 0` the factors of `C₇(L)` cancel against
`π₃^* (e^* L)` by evaluation (on `x₃ = 0` one has `m₁₂₃ = m₁₂`, `m₁₃ = m₁`, `m₂₃ = m₂` and
`m₃ = e ∘ π₃`), and `c_L` is the unique isomorphism restricting to these cancellations. Two
such isomorphisms differ by a global unit of `A × A × A`, which comes from `S` since
`π₃_* 𝒪 = 𝒪_S`, and the face normalisation forces it to be `1`. No trivialisation of
`e^* L` is chosen: the form of the statement with `𝒪` in place of `π₃^* (e^* L)` would require
a rigidification `e^* L ≅ 𝒪_S`, which need not exist and whose choice changes the isomorphism
by a unit of `S`. The present formulation is obtained from the rigidified theorem of the cube
applied to `L ⊗ π^* (e^* L)⁻¹`, which is canonically rigidified by evaluation; see Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, Proposition 3.2.3.1, and Conrad's
notes on abelian varieties, Theorem 3.1.6. -/
noncomputable def cubeIso (A : Over S) [GrpObj A] [IsAbelianScheme A]
    (L : A.left.Modules) [L.IsInvertible] :
    (overPullback ((fst (A ⊗ A) A ≫ fst A A) * (fst (A ⊗ A) A ≫ snd A A) * snd (A ⊗ A) A) L ⊗
      overPullback ((fst (A ⊗ A) A ≫ fst A A) * (fst (A ⊗ A) A ≫ snd A A)) (L⁻¹) ⊗
      overPullback ((fst (A ⊗ A) A ≫ fst A A) * snd (A ⊗ A) A) (L⁻¹) ⊗
      overPullback ((fst (A ⊗ A) A ≫ snd A A) * snd (A ⊗ A) A) (L⁻¹) ⊗
      overPullback (fst (A ⊗ A) A ≫ fst A A) L ⊗
      overPullback (fst (A ⊗ A) A ≫ snd A A) L ⊗
      overPullback (snd (A ⊗ A) A) L) ≅
    overPullback (toUnit ((A ⊗ A) ⊗ A)) (overPullback η[A] L) :=
  sorry

/-- Blueprint `sk-prop-av-mult-n-pullback`: Pullback of symmetric modules under multiplication
by `n`.

Let `A` be an abelian scheme over a base `S` with unit section `e : S ⟶ A` and structure map
`π : A ⟶ S`, and let `N` be an invertible `𝒪_A`-module which is *symmetric*, with a chosen
symmetry `[-1]^* N ≅ N`. Then for every `n`

`[n]^* N ⊗ π^* (e^* N)^{⊗ n²} ≅ N^{⊗ n²} ⊗ π^* (e^* N)`,

that is, `[n]^* N ≅ N^{⊗ n²} ⊗ π^* (e^* N)^{⊗ (1 - n²)}`. Over a field, or whenever `e^* N` is
trivial, this is the blueprint statement `[n]^* N ≅ N^{⊗ n²}`; over a general base the
correction term is forced, as `N = π^* M` with `M` invertible on `S` shows (then `[n]^* N = N`).

The isomorphism is canonical given the symmetry: the theorem of the cube
`AlgebraicGeometry.cubeIso` gives by induction on `n` the canonical isomorphism
`[n]^* N ≅ N^{⊗ (n² + n)/2} ⊗ [-1]^* N^{⊗ (n² - n)/2} ⊗ π^* (e^* N)^{⊗ (1 - n²)}`, into which
the chosen symmetry is substituted. -/
noncomputable def overPullbackNpowIdIso (A : Over S) [GrpObj A] [IsAbelianScheme A]
    (N : A.left.Modules) [N.IsInvertible] (e : overPullback ι[A] N ≅ N) (n : ℕ) :
    (overPullback (𝟙 A ^ n) N ⊗
        (overPullback (toUnit A) (overPullback η[A] N)).tensorPow (n ^ 2)) ≅
      (N.tensorPow (n ^ 2) ⊗ overPullback (toUnit A) (overPullback η[A] N)) :=
  sorry

end AlgebraicGeometry
