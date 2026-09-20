/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
public import WeilConjectures.AlgebraicGeometry.Group.CubeClass
public import WeilConjectures.AlgebraicGeometry.Modules.Symmetric
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.Basic
public import WeilConjectures.Mathlib.Algebra.Group.ForwardDiff
public import WeilConjectures.Mathlib.Algebra.Ring.Int.Parity

/-!
# The cube identity on an abelian variety, and the pullback formula `[n]^*L ≅ L^(n²)`

Let `A` be an abelian variety over a field `K` and let `L` be a line bundle on `A`. The theorem
of the cube, applied with `X = Y = Z = A` and `x₀ = y₀ = z₀ = e`, says that the line bundle

`Θ(L) := m₁₂₃^*L ⊗ m₁₂^*L⁻¹ ⊗ m₁₃^*L⁻¹ ⊗ m₂₃^*L⁻¹ ⊗ p₁^*L ⊗ p₂^*L ⊗ p₃^*L`

on `A × A × A` is trivial, where `p₁, p₂, p₃` are the three projections and `m_S` is the sum of
the coordinates indexed by `S`. Equivalently, and this is the form everything below is stated
in, for every `K`-scheme `S` and all `f, g, h ∈ A(S)`,

`(f+g+h)^*L ⊗ (f+g)^*L⁻¹ ⊗ (f+h)^*L⁻¹ ⊗ (g+h)^*L⁻¹ ⊗ f^*L ⊗ g^*L ⊗ h^*L ≅ 𝒪_S`.

This is `thm:cube-abelian` of the blueprint (`27_theorem_of_the_cube.tex`). Taking
`S = A` and `f = [n]`, `g = [1]`, `h = [-1]` gives the recursion

`[n+1]^*L ⊗ [n-1]^*L ≅ ([n]^*L)^⊗2 ⊗ L ⊗ [-1]^*L`   (`cor:cube-mulby-recursion`),

and a two-directional induction over `ℤ` from the two base cases `n = 0, 1` turns the
recursion into the closed formula

`[n]^*L ≅ L^⊗((n²+n)/2) ⊗ ([-1]^*L)^⊗((n²-n)/2)`   (`thm:cube-mulby-pullback`),

which for a *symmetric* line bundle, one with `[-1]^*L ≅ L`, reads `[n]^*L ≅ L^⊗(n²)`. That
last formula is what the degree computation for the isogeny `[n]` rests on.

## Main statements

- `AlgebraicGeometry.Scheme.Pic.cubeClass_eq_one` (blueprint: `thm:cube-abelian`) — the cube
  identity, in the Picard group and in the `S`-points form. The corresponding statement on
  sheaves is
  `AlgebraicGeometry.IsAbelianVariety.nonempty_pullback_tensor_iso_tensor_pullback`, and the
  statement on `A × A × A` itself, which the `S`-points form is pulled back from, is
  `AlgebraicGeometry.Scheme.Pic.cubeClass_proj_eq_one`.
- `AlgebraicGeometry.Scheme.Pic.map_zpow_add_one_mul_map_zpow_sub_one` (blueprint:
  `cor:cube-mulby-recursion`) — the recursion for `[n]^*L`.
- `AlgebraicGeometry.Scheme.Pic.map_zpow_left_eq_zpow_mul_zpow` (blueprint:
  `thm:cube-mulby-pullback`) — the pullback formula for `[n]^*L`, for `n : ℤ`.
  `AlgebraicGeometry.Scheme.Pic.map_zpow_left_eq_zpow_of_map_neg_one` is its symmetric form
  `[n]^*L ≅ L^⊗(n²)`, for a class fixed by `[-1]`, with
  `AlgebraicGeometry.Scheme.Pic.map_zpow_left_eq_zpow_of_isSymmetric` the version for a
  symmetric line bundle; that specialises to the `ℕ`-indexed
  `AlgebraicGeometry.IsAbelianVariety.mulBy` as
  `AlgebraicGeometry.Scheme.Pic.map_mulBy_left_eq_pow_of_isSymmetric` and, on sheaves, as
  `AlgebraicGeometry.IsAbelianVariety.nonempty_pullback_mulBy_iso_tensorPow`.

## Implementation notes

* **The Künneth hypothesis is carried, not discharged.** Every statement below whose proof goes
  through the theorem of the cube takes the hypothesis `hkunneth`, the predicate
  `AlgebraicGeometry.Scheme.IsCubeKunneth` instantiated at `X = Y = Z = A` and `x₀ = y₀ = e`,
  and passes it straight on, exactly as
  `WeilConjectures.AlgebraicGeometry.TheoremOfCube.Basic` carries it. Discharging it is the
  work of a separate issue, after which it can be stripped from all of these signatures at once.
* **Everything is stated in the Picard group.** The seven-fold cancellation that the proof of
  the cube identity comes down to is a computation in the abelian group `Pic`, not a coherence
  argument about seven tensor isomorphisms, so the Picard group is what the statements are
  phrased in: `AlgebraicGeometry.Scheme.Pic.cubeClass` is the class of `Θ(L)`, and triviality
  is `cubeClass … = 1`. The two sheaf-level forms are corollaries, obtained through
  `AlgebraicGeometry.Scheme.Pic.mk_eq_mk_iff`, and they are the only declarations here in the
  `AlgebraicGeometry.IsAbelianVariety` namespace.
* The sheaf-level form of the cube identity,
  `AlgebraicGeometry.IsAbelianVariety.nonempty_pullback_tensor_iso_tensor_pullback`, is stated
  with the three inverses moved to the other side of the isomorphism,
  `(f+g+h)^*L ⊗ f^*L ⊗ g^*L ⊗ h^*L ≅ (f+g)^*L ⊗ (f+h)^*L ⊗ (g+h)^*L`,
  which is equivalent to the triviality of `Θ(L)` and avoids naming tensor inverses.
* Nothing that is not about abelian varieties is stated here. The cube class itself, its
  naturality, its symmetry and its triviality when one of the three points is the unit are
  statements about an arbitrary monoid scheme and live in
  `WeilConjectures.AlgebraicGeometry.Group.CubeClass`; the identification of the three slices
  of a triple product with cartesian lifts is in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks`; the theorem of the cube in the Picard
  group is in `WeilConjectures.AlgebraicGeometry.TheoremOfCube.Basic`; and the two-directional
  induction over `ℤ` is `eq_one_of_add_one_mul_sub_one_eq_sq` of
  `WeilConjectures.Mathlib.Algebra.Group.ForwardDiff`.
* The triple product `A × A × A` is `(G ⊗ G) ⊗ G` in the cartesian monoidal category
  `Over (Spec K)`, whose underlying scheme is *definitionally* the iterated fibre product
  `(A ×_K A) ×_K A` that the theorem of the cube is stated about. That is what lets the group
  law of `A`, which lives in `Over (Spec K)`, meet the theorem of the cube, which lives in
  `Scheme`.
* Everything here is `sorryAx`-tainted through the theorem of the cube, which rests on the
  project's deferred seesaw and formal-functions statements. This is why nothing in this area
  carries `\leanok`.

## References

* D. Mumford, *Abelian Varieties*, §6.
* J. S. Milne, *Abelian Varieties*, I, §5.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry

open Scheme

section Cube

variable {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] [IsAbelianVariety G]

variable (hkunneth : ∀ (t : G.left) (n : ℕ), Scheme.IsCubeKunneth G.hom G.hom G.hom
  η[G].left (MonObj.one_left_comp_hom G) η[G].left (MonObj.one_left_comp_hom G) t n)

include hkunneth

namespace Scheme.Pic

/-! ### The cube identity -/

/-- **The cube identity on an abelian variety, at the universal point** (blueprint:
`thm:cube-abelian`): the bundle

`Θ(L) = m₁₂₃^*L ⊗ m₁₂^*L⁻¹ ⊗ m₁₃^*L⁻¹ ⊗ m₂₃^*L⁻¹ ⊗ p₁^*L ⊗ p₂^*L ⊗ p₃^*L`

on `A × A × A` is trivial.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. It is carried by every statement below in the same way, and this is not repeated. -/
theorem cubeClass_proj_eq_one (ℓ : G.left.Pic) :
    cubeClass (fst (G ⊗ G) G ≫ fst G G) (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ = 1 := by
  -- this is the theorem of the cube applied with `X = Y = Z = A` and `x₀ = y₀ = z₀ = e`: an
  -- abelian variety is a proper geometrically integral variety over `K`, in particular a
  -- connected reduced `K`-scheme of finite type, and `e` is a `K`-rational point
  refine eq_one_of_map_sliceInclusion_eq_one G.hom G.hom G.hom
    η[G].left (MonObj.one_left_comp_hom G) η[G].left (MonObj.one_left_comp_hom G) hkunneth
    η[G].left (MonObj.one_left_comp_hom G) _ ?_ ?_ ?_
  -- what has to be checked is that `Θ(L)` restricts trivially to the three coordinate slices,
  -- and on each of them one of the three points becomes the identity, which makes three of the
  -- seven factors cancel against three others and leaves a pullback along a constant morphism
  · -- the slice `A × A × {e}`: the third point becomes the identity
    rw [sliceInclusionFst_eq_lift]
    refine (map_cubeClass (lift (𝟙 (G ⊗ G)) (toUnit (G ⊗ G) ≫ η[G]))
      (fst (G ⊗ G) G ≫ fst G G) (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ).trans ?_
    simpa only [← Category.assoc, lift_fst, lift_snd, Category.id_comp,
      ← CategoryTheory.Hom.one_def] using cubeClass_one_right (fst G G) (snd G G) ℓ
  · -- the slice `A × {e} × A`: the second point becomes the identity
    rw [pullbackMapSliceInclusionFst_eq_lift]
    refine (map_cubeClass (lift (lift (fst G G) (toUnit (G ⊗ G) ≫ η[G])) (snd G G))
      (fst (G ⊗ G) G ≫ fst G G) (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ).trans ?_
    simpa only [← Category.assoc, lift_fst, lift_snd, ← CategoryTheory.Hom.one_def] using
      cubeClass_one_middle (fst G G) (snd G G) ℓ
  · -- the slice `{e} × A × A`: the first point becomes the identity
    rw [pullbackMapSliceInclusionSnd_eq_lift]
    refine (map_cubeClass (lift (lift (toUnit (G ⊗ G) ≫ η[G]) (fst G G)) (snd G G))
      (fst (G ⊗ G) G ≫ fst G G) (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ).trans ?_
    simpa only [← Category.assoc, lift_fst, lift_snd, ← CategoryTheory.Hom.one_def] using
      cubeClass_one_left (fst G G) (snd G G) ℓ

/-- **The cube identity on an abelian variety** (blueprint: `thm:cube-abelian`), in the form of
`S`-points: for every `K`-scheme `S` and all `f, g, h ∈ A(S)`, the line bundle

`(f+g+h)^*L ⊗ (f+g)^*L⁻¹ ⊗ (f+h)^*L⁻¹ ⊗ (g+h)^*L⁻¹ ⊗ f^*L ⊗ g^*L ⊗ h^*L`

on `S` is trivial. It is the pullback of `Θ(L)` along `(f, g, h) : S ⟶ A × A × A`, so this is
`AlgebraicGeometry.Scheme.Pic.cubeClass_proj_eq_one` pulled back. -/
theorem cubeClass_eq_one {W : Over (Spec (.of K))} (f g h : W ⟶ G) (ℓ : G.left.Pic) :
    cubeClass f g h ℓ = 1 := by
  have h₁ := map_cubeClass (lift (lift f g) h) (fst (G ⊗ G) G ≫ fst G G)
    (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ
  rw [cubeClass_proj_eq_one G hkunneth, map_one] at h₁
  simpa only [← Category.assoc, lift_fst, lift_snd] using h₁.symm

/-! ### The recursion and the pullback formula -/

/-- **The recursion for `[n]^*L`** (blueprint: `cor:cube-mulby-recursion`): for every `n : ℤ`,

`[n+1]^*L ⊗ [n-1]^*L ≅ ([n]^*L)^⊗2 ⊗ L ⊗ [-1]^*L`,

read in the Picard group of `A`. -/
theorem map_zpow_add_one_mul_map_zpow_sub_one (ℓ : G.left.Pic) (n : ℤ) :
    Pic.map (GrpObj.zpow G (n + 1)).left ℓ * Pic.map (GrpObj.zpow G (n - 1)).left ℓ =
      Pic.map (GrpObj.zpow G n).left ℓ ^ 2 * ℓ * Pic.map (GrpObj.zpow G (-1)).left ℓ := by
  have hmul : ∀ m k : ℤ, GrpObj.zpow G m * GrpObj.zpow G k = GrpObj.zpow G (m + k) := by
    intro m k
    rw [CategoryTheory.Hom.mul_def, ← GrpObj.zpow_add]
  -- the `S`-points form of the cube identity, taken at `S = A` with `f = [n]`, `g = [1] = 𝟙`
  -- and `h = [-1]`, so that `f + g = [n+1]`, `f + h = [n-1]`, `g + h = [0]` and `f + g + h = [n]`
  have key := cubeClass_eq_one G hkunneth (GrpObj.zpow G n) (GrpObj.zpow G 1)
    (GrpObj.zpow G (-1)) ℓ
  simp only [cubeClass, hmul] at key
  -- the factor `[0]^*L` is trivial because `[0]` is the constant morphism at `e`, and `[1] = 𝟙`
  rw [show n + 1 + (-1 : ℤ) = n by ring, show n + (-1 : ℤ) = n - 1 by ring,
    show (1 : ℤ) + (-1 : ℤ) = 0 by norm_num, GrpObj.zpow_zero, ← CategoryTheory.Hom.one_def,
    map_one_left, GrpObj.zpow_one, Over.id_left, Pic.map_id, MonoidHom.id_apply] at key
  apply Additive.ofMul.injective
  replace key := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at key
  simp only [ofMul_mul, ofMul_pow]
  linear_combination (norm := abel) -key

/-- **The pullback of a line bundle along `[n]`** (blueprint: `thm:cube-mulby-pullback`): for
every `n : ℤ`, writing `N := [-1]^*L`,

`[n]^*L ≅ L^⊗((n²+n)/2) ⊗ N^⊗((n²-n)/2)`,

read in the Picard group of `A`. The two exponents `n(n+1)/2` and `n(n-1)/2` are integers, and
in fact non-negative ones, for every `n : ℤ`. -/
theorem map_zpow_left_eq_zpow_mul_zpow (ℓ : G.left.Pic) (n : ℤ) :
    Pic.map (GrpObj.zpow G n).left ℓ =
      ℓ ^ (n * (n + 1) / 2) * Pic.map (GrpObj.zpow G (-1)).left ℓ ^ (n * (n - 1) / 2) := by
  set ν := Pic.map (GrpObj.zpow G (-1)).left ℓ with hν
  -- both sides solve the second-order recursion `u (m+1) * u (m-1) = u m ^ 2 * (ℓ * ν)` and
  -- agree at `0` and at `1`, so their quotient is trivial by
  -- `eq_one_of_add_one_mul_sub_one_eq_sq`
  have key : (fun m : ℤ ↦ Pic.map (GrpObj.zpow G m).left ℓ /
      (ℓ ^ (m * (m + 1) / 2) * ν ^ (m * (m - 1) / 2))) = 1 := by
    refine eq_one_of_add_one_mul_sub_one_eq_sq (fun m ↦ ?_) ?_ ?_
    · have hF := map_zpow_add_one_mul_map_zpow_sub_one G hkunneth ℓ m
      rw [← hν, mul_assoc] at hF
      -- the exponents satisfy the same recursion, their second differences being constant
      -- equal to `1`
      have hE : ℓ ^ ((m + 1) * (m + 1 + 1) / 2) * ν ^ ((m + 1) * (m + 1 - 1) / 2) *
          (ℓ ^ ((m - 1) * (m - 1 + 1) / 2) * ν ^ ((m - 1) * (m - 1 - 1) / 2)) =
            (ℓ ^ (m * (m + 1) / 2) * ν ^ (m * (m - 1) / 2)) ^ 2 * (ℓ * ν) := by
        rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add, Int.mul_add_one_ediv_two_add,
          Int.mul_sub_one_ediv_two_add, zpow_add, zpow_add, zpow_add, zpow_add, zpow_one,
          zpow_one]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_pow]
        abel
      apply Additive.ofMul.injective
      replace hF := congrArg Additive.ofMul hF
      replace hE := congrArg Additive.ofMul hE
      simp only [ofMul_mul, ofMul_pow] at hF hE
      simp only [ofMul_mul, ofMul_div, ofMul_pow]
      linear_combination (norm := abel) hF - hE
    · -- `[0]` is the constant morphism at `e`, and both exponents vanish at `0`
      rw [div_eq_one, GrpObj.zpow_zero, ← CategoryTheory.Hom.one_def, map_one_left]
      norm_num
    · -- `[1] = 𝟙`, and the two exponents at `1` are `1` and `0`
      rw [div_eq_one, GrpObj.zpow_one, Over.id_left, Pic.map_id, MonoidHom.id_apply]
      norm_num
  simpa only [Pi.one_apply, div_eq_one] using congrFun key n

/-- **The pullback of a line bundle fixed by `[-1]` along `[n]`** (blueprint:
`thm:cube-mulby-pullback`): if `[-1]^*ℓ = ℓ` in the Picard group of `A`, then
`[n]^*ℓ = ℓ^(n²)` for every `n : ℤ`.

This is the case `N = L` of `AlgebraicGeometry.Scheme.Pic.map_zpow_left_eq_zpow_mul_zpow`, the
two exponents adding up to `n(n+1)/2 + n(n-1)/2 = n²`. -/
theorem map_zpow_left_eq_zpow_of_map_neg_one (ℓ : G.left.Pic)
    (hℓ : Pic.map (GrpObj.zpow G (-1)).left ℓ = ℓ) (n : ℤ) :
    Pic.map (GrpObj.zpow G n).left ℓ = ℓ ^ (n ^ 2) := by
  rw [map_zpow_left_eq_zpow_mul_zpow G hkunneth ℓ n, hℓ, ← zpow_add,
    Int.mul_add_one_ediv_two_add_mul_sub_one_ediv_two]

/-- **The pullback of a symmetric line bundle along `[n]`**: if `[-1]^*L ≅ L`, then
`[n]^*L ≅ L^⊗(n²)` for every `n : ℤ`, read in the Picard group of `A`.

This is `AlgebraicGeometry.Scheme.Pic.map_zpow_left_eq_zpow_of_map_neg_one` for the class of a
symmetric line bundle, symmetry being exactly the hypothesis `[-1]^*ℓ = ℓ` read on sheaves. -/
theorem map_zpow_left_eq_zpow_of_isSymmetric {L : G.left.Modules} (hL : L.Invertible)
    (hsymm : L.IsSymmetric G) (n : ℤ) :
    Pic.map (GrpObj.zpow G n).left (Pic.mk L hL) = Pic.mk L hL ^ (n ^ 2) :=
  map_zpow_left_eq_zpow_of_map_neg_one G hkunneth _
    (by rw [GrpObj.zpow_neg_one, Pic.map_mk, Pic.mk_eq_mk_iff]; exact hsymm) n

/-- **The pullback of a symmetric line bundle along `[n]` for `n : ℕ`**: if `[-1]^*L ≅ L`, then
`[n]^*L ≅ L^⊗(n²)`, read in the Picard group of `A`.

This is `AlgebraicGeometry.Scheme.Pic.map_zpow_left_eq_zpow_of_isSymmetric` specialised along
`CategoryTheory.GrpObj.zpow_natCast` to the `ℕ`-indexed multiplication-by-`n` endomorphism
`AlgebraicGeometry.IsAbelianVariety.mulBy`, which is what the theory of the isogeny `[n]` is
stated in terms of. -/
theorem map_mulBy_left_eq_pow_of_isSymmetric {L : G.left.Modules} (hL : L.Invertible)
    (hsymm : L.IsSymmetric G) (n : ℕ) :
    Pic.map (IsAbelianVariety.mulBy G n).left (Pic.mk L hL) = Pic.mk L hL ^ (n ^ 2) := by
  rw [show IsAbelianVariety.mulBy G n = GrpObj.zpow G (n : ℤ) from (GrpObj.zpow_natCast G n).symm,
    map_zpow_left_eq_zpow_of_isSymmetric G hkunneth hL hsymm,
    show ((n : ℤ) ^ 2) = ((n ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

end Scheme.Pic

/-! ### The sheaf-level corollaries -/

namespace IsAbelianVariety

/-- **The cube identity on an abelian variety**, on sheaves (blueprint: `thm:cube-abelian`).

For every `K`-scheme `S` and all `f, g, h ∈ A(S)`,

`(f+g+h)^*L ⊗ f^*L ⊗ g^*L ⊗ h^*L ≅ (f+g)^*L ⊗ (f+h)^*L ⊗ (g+h)^*L`.

This is the triviality of the cube bundle `Θ(L)` of
`AlgebraicGeometry.Scheme.Pic.cubeClass_eq_one`, with the three inverses moved to the other
side of the isomorphism so that no tensor inverse has to be named. -/
theorem nonempty_pullback_tensor_iso_tensor_pullback {W : Over (Spec (.of K))}
    (f g h : W ⟶ G) {L : G.left.Modules} (hL : L.Invertible) :
    Nonempty ((Modules.pullback (f * g * h).left).obj L ⊗ (Modules.pullback f.left).obj L ⊗
        (Modules.pullback g.left).obj L ⊗ (Modules.pullback h.left).obj L ≅
      (Modules.pullback (f * g).left).obj L ⊗ (Modules.pullback (f * h).left).obj L ⊗
        (Modules.pullback (g * h).left).obj L) := by
  have hfgh : ((Modules.pullback (f * g * h).left).obj L).Invertible := hL.pullback _
  have hf : ((Modules.pullback f.left).obj L).Invertible := hL.pullback _
  have hg : ((Modules.pullback g.left).obj L).Invertible := hL.pullback _
  have hh : ((Modules.pullback h.left).obj L).Invertible := hL.pullback _
  have hfg : ((Modules.pullback (f * g).left).obj L).Invertible := hL.pullback _
  have hfh : ((Modules.pullback (f * h).left).obj L).Invertible := hL.pullback _
  have hgh : ((Modules.pullback (g * h).left).obj L).Invertible := hL.pullback _
  -- read the two sides in the Picard group, as products of the seven classes
  rw [← Pic.mk_eq_mk_iff (hM := hfgh.tensorObj (hf.tensorObj (hg.tensorObj hh)))
      (hN := hfg.tensorObj (hfh.tensorObj hgh)),
    Pic.mk_tensorObj (hM := hfgh) (hN := hf.tensorObj (hg.tensorObj hh)),
    Pic.mk_tensorObj (hM := hf) (hN := hg.tensorObj hh),
    Pic.mk_tensorObj (hM := hg) (hN := hh),
    Pic.mk_tensorObj (hM := hfg) (hN := hfh.tensorObj hgh),
    Pic.mk_tensorObj (hM := hfh) (hN := hgh)]
  -- the cube class is trivial, which is the same identity with the three inverses on the left
  have key := Pic.cubeClass_eq_one G hkunneth f g h (Pic.mk L hL)
  simp only [Pic.cubeClass, Pic.map_mk] at key
  apply Additive.ofMul.injective
  replace key := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at key
  simp only [ofMul_mul]
  linear_combination (norm := abel) key

/-- **The pullback of a symmetric line bundle along `[n]`, on sheaves**: if `[-1]^*L ≅ L`, then
`[n]^*L ≅ L^⊗(n²)` for every `n : ℕ`.

This is the form the degree computation for the isogeny `[n]` uses: for a symmetric ample line
bundle `L`, which exists on every abelian variety, it identifies `[n]^*L` with the `n²`-th
tensor power of `L`. -/
theorem nonempty_pullback_mulBy_iso_tensorPow {L : G.left.Modules} (hL : L.Invertible)
    (hsymm : L.IsSymmetric G) (n : ℕ) :
    Nonempty ((Modules.pullback (mulBy G n).left).obj L ≅ L ^⊗ (n ^ 2)) := by
  rw [← Pic.mk_eq_mk_iff (hM := hL.pullback _) (hN := hL.tensorPow (n ^ 2)),
    ← Pic.map_mk (mulBy G n).left hL, Pic.mk_tensorPow (hM := hL), zpow_natCast,
    Pic.map_mulBy_left_eq_pow_of_isSymmetric G hkunneth hL hsymm]

end IsAbelianVariety

end Cube

end AlgebraicGeometry
