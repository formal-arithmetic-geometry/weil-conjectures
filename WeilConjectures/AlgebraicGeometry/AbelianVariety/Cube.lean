/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube

/-!
# The theorem of the cube

For an invertible module `L` on an abelian variety `A` the seven pullbacks of `L` along the
partial sum maps `A × A × A ⟶ A` satisfy the cube relation, and as a consequence the pullback of
a symmetric invertible module along multiplication by `n` is its `n²`-th tensor power.

The partial sum maps are written using the group structure on `X ⟶ A` coming from
`CategoryTheory.GrpObj.Hom.group`: writing `p₁ = fst _ _ ≫ fst _ _`, `p₂ = fst _ _ ≫ snd _ _`
and `p₃ = snd _ _` for the three projections `(A ⊗ A) ⊗ A ⟶ A`, the partial sum `m_{i₁…i_t}` is
the product `p_{i₁} * ⋯ * p_{i_t}`. Naming the eight vertices of the cube `(ε₁, ε₂, ε₃)` with
`εᵢ ∈ {0, 1}`, the relation below is the alternating product over the vertices:

```
        (0,1,1) ───────── (1,1,1)
         ╱ │               ╱ │
   (0,1,0) ─┼───────(1,1,0)  │
      │   (0,0,1) ──────│── (1,0,1)
      │  ╱              │  ╱
   (0,0,0) ─────────(1,0,0)
```

the vertex `(ε₁, ε₂, ε₃)` contributing `m_{i : εᵢ = 1}^* L` with sign `(-1)^(ε₁ + ε₂ + ε₃)`.

## Main statements

- `AlgebraicGeometry.nonempty_iso_cube`: the theorem of the cube.
- `AlgebraicGeometry.nonempty_iso_overPullback_npow_id`: `[n]^* N ≅ N^{⊗ n²}` for symmetric `N`.

## TODO

Both statements throw the isomorphism away by asserting only `Nonempty`. The mathematical
content is the isomorphism itself, so once they can be proved they should become `def`s
returning the isomorphism, with the `Nonempty` form derived.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme.Modules

variable {K : Type u} [Field K]

/-- Blueprint `sk-prop-av-cube`: The theorem of the cube.

Let `A` be an abelian variety over a field `K` and let `L` be an invertible `𝒪_A`-module. For
`1 ≤ i₁ < ⋯ < i_t ≤ 3` let `m_{i₁…i_t} : A × A × A ⟶ A` be the partial sum map
`(x₁, x₂, x₃) ↦ x_{i₁} + ⋯ + x_{i_t}`. Then
`m₁₂₃^* L ⊗ m₁^* L ⊗ m₂^* L ⊗ m₃^* L ≅ m₁₂^* L ⊗ m₁₃^* L ⊗ m₂₃^* L`.

This is also blueprint `thm-sc-theorem-of-cube`. The proof applies the general theorem of the
cube `AlgebraicGeometry.nonempty_iso_of_nonempty_iso_overPullback_slices` with `X = Y = Z = A`
and the unit as rational point: on each of the slices `{e} × A × A`, `A × {e} × A` and
`A × A × {e}` both sides restrict to `n₁₂^* L ⊗ n₁^* L ⊗ n₂^* L`, since `e^* L` is trivial. -/
theorem nonempty_iso_cube (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (L : A.left.Modules) [L.IsInvertible] :
    Nonempty
      (Scheme.Modules.tensorObj
          (overPullback ((fst (A ⊗ A) A ≫ fst A A) * (fst (A ⊗ A) A ≫ snd A A) *
            snd (A ⊗ A) A) L)
          (Scheme.Modules.tensorObj (overPullback (fst (A ⊗ A) A ≫ fst A A) L)
            (Scheme.Modules.tensorObj (overPullback (fst (A ⊗ A) A ≫ snd A A) L)
              (overPullback (snd (A ⊗ A) A) L))) ≅
        Scheme.Modules.tensorObj
          (overPullback ((fst (A ⊗ A) A ≫ fst A A) * (fst (A ⊗ A) A ≫ snd A A)) L)
          (Scheme.Modules.tensorObj
            (overPullback ((fst (A ⊗ A) A ≫ fst A A) * snd (A ⊗ A) A) L)
            (overPullback ((fst (A ⊗ A) A ≫ snd A A) * snd (A ⊗ A) A) L))) := by
  -- Compare isomorphism classes in the commutative monoid `Skeleton`, where pullback is
  -- multiplicative and the pullback of `L` along the constant map `1` is trivial.
  have hcomp {B C : Over (Spec (.of K))} (s : B ⟶ C) (g : C ⟶ A) :
      toSkeleton (overPullback s (overPullback g L)) = toSkeleton (overPullback (s ≫ g) L) :=
    toSkeleton_eq_toSkeleton_iff.2 ⟨(pullbackComp s.left g.left).app L⟩
  have htensor {B C : Over (Spec (.of K))} (s : B ⟶ C) (M N : C.left.Modules) :
      toSkeleton (overPullback s (M ⊗ N)) =
        toSkeleton (overPullback s M) * toSkeleton (overPullback s N) := by
    rw [← Skeleton.toSkeleton_tensorObj]
    exact toSkeleton_eq_toSkeleton_iff.2 (nonempty_pullback_tensorObj_iso _ _ _)
  have hone (B : Over (Spec (.of K))) :
      toSkeleton (overPullback (toUnit B ≫ η[A]) L) = 1 := by
    rw [← hcomp, Skeleton.one_eq]
    obtain ⟨e⟩ := IsInvertible.nonempty_iso_unit (X := Spec (.of K))
      (IsLocalRing.closedPoint K) (overPullback η[A] L)
    exact toSkeleton_eq_toSkeleton_iff.2 ⟨(pullback _).mapIso e ≪≫ pullbackObjUnitIso _⟩
  have hunit_mul {B : Over (Spec (.of K))} (f : B ⟶ A) : (toUnit B ≫ η[A]) * f = f :=
    one_mul f
  have mul_hunit {B : Over (Spec (.of K))} (f : B ⟶ A) : f * (toUnit B ≫ η[A]) = f := mul_one f
  refine nonempty_iso_of_nonempty_iso_overPullback_slices A A A η[A] η[A] η[A] _ _ ?_ ?_ ?_ <;>
    refine toSkeleton_eq_toSkeleton_iff.1 ?_ <;>
    simp only [htensor, hcomp, comp_mul, lift_fst_assoc, lift_fst, lift_snd, Category.id_comp,
      hunit_mul, mul_hunit, hone]
  · rw [_root_.one_mul]; ac_rfl
  · rw [_root_.one_mul]; ac_rfl
  · rw [_root_.mul_one]

/-- Blueprint `sk-prop-av-mult-n-pullback`: Pullback of symmetric modules under multiplication
by `n`.

Let `A` be an abelian variety over `K` and let `N` be an invertible `𝒪_A`-module which is
*symmetric*, that is `[-1]^* N ≅ N`. Then `[n]^* N ≅ N^{⊗ n²}` for every `n`. -/
theorem nonempty_iso_overPullback_npow_id (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (N : A.left.Modules) [N.IsInvertible]
    (hsymm : Nonempty (overPullback ι[A] N ≅ N)) (n : ℕ) :
    Nonempty (overPullback (𝟙 A ^ n) N ≅ N.tensorPow (n ^ 2)) :=
  sorry

end AlgebraicGeometry
