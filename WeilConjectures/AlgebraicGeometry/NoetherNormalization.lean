/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Generic relative Noether normalization

Noether normalization says that a finitely generated algebra over a field is finite over a
polynomial subalgebra. This file states the relative, generic form of that statement for schemes: a
dominant affine morphism `f : X ⟶ Y` of finite type between integral schemes whose generic fibre
has dimension `r` becomes, after shrinking `Y` to a dense open `V` and replacing `X` by `f ⁻¹ᵁ V`, a
finite surjective morphism to the `r`-fold relative affine line over `V` followed by the projection
to `V`.

Recording the target as `AlgebraicGeometry.iteratedAffineLine V r` rather than as the relative
affine space `𝔸(ULift (Fin r); V)` is what makes the statement usable in the Deligne–Laumon
reduction: the projection is then literally a composition of `r` affine-line projections, each of
which can be fed to the relative affine-line bound one at a time, as the blueprint node requires.

## Implementation notes

The blueprint derives this statement from a purely ring-theoretic one, `lem-zl-spread-normalization`
("spreading affine normalization to a principal open"): for a domain `A` and a finitely generated
`A`-algebra `B` there are `0 ≠ s ∈ A`, `d ≥ 0` and coordinates `t ∈ (B_s)^d` making `A_s[t] → B_s`
finite. That lemma generalises `Mathlib/RingTheory/NoetherNormalization.lean`, is independent of the
Weil conjectures, and belongs in the mirror tree `WeilConjectures/Mathlib/RingTheory/`; it is a
separate blueprint node and is not stated here.

## Main statements

- `AlgebraicGeometry.exists_dense_isFinite_toIteratedAffineLine`: the generic relative Noether
  normalization.

## References

- [Stacks, Tag 07NA](https://stacks.math.columbia.edu/tag/07NA): for an injective finite-type ring
  map out of a domain `R`, a factorization `R → R[y₁, …, y_d] → S' → S` with `S'` finite over the
  polynomial ring and `S'_f ≅ S_f` for some nonzero `f ∈ R`. This is the ring-theoretic statement
  the lemma below globalises.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Let `f : X ⟶ Y` be a dominant affine morphism of finite type between integral schemes whose
generic fibre has dimension `r`. Then there is a dense open `V ⊆ Y` over which `f` factors as a
finite surjective morphism `ν` to the `r`-fold relative affine line over `V` followed by its
projection to `V`:

```
f ⁻¹ᵁ V ----- ν -----> iteratedAffineLine V r
      \                        |
       \                       | iteratedAffineLineProj V r
    f ∣_ V                     |
         \                     v
          `----------------->  V
```

(blueprint: `sk-l-dl-general-normalization`). -/
@[stacks 07NA]
theorem exists_dense_isFinite_toIteratedAffineLine {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]
    [IsIntegral Y] [IsAffineHom f] [LocallyOfFiniteType f] [IsDominant f] (r : ℕ)
    (hr : topologicalKrullDim (f.fiber (genericPoint Y)) = r) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧
      ∃ ν : (f ⁻¹ᵁ V).toScheme ⟶ iteratedAffineLine V.toScheme r,
        IsFinite ν ∧ Surjective ν ∧ ν ≫ iteratedAffineLineProj V.toScheme r = f ∣_ V :=
  sorry

end AlgebraicGeometry
