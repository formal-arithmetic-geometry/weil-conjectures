/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PicardField
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackConstant
public import WeilConjectures.AlgebraicGeometry.Modules.Symmetric

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

and a two-directional induction over `ℤ` from the three base cases `n = 0, 1, -1` turns the
recursion into the closed formula

`[n]^*L ≅ L^⊗((n²+n)/2) ⊗ ([-1]^*L)^⊗((n²-n)/2)`   (`thm:cube-mulby-pullback`),

which for a *symmetric* line bundle, one with `[-1]^*L ≅ L`, reads `[n]^*L ≅ L^⊗(n²)`. That
last formula is what the degree computation for the isogeny `[n]` rests on.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.cubeClass_eq_one` (blueprint: `thm:cube-abelian`) — the
  cube identity, in the Picard group and in the `S`-points form. The corresponding statement on
  sheaves is `AlgebraicGeometry.IsAbelianVariety.nonempty_cube_iso`, and the statement on
  `A × A × A` itself, which the `S`-points form is pulled back from, is
  `AlgebraicGeometry.IsAbelianVariety.cubeClass_proj_eq_one`.
- `AlgebraicGeometry.IsAbelianVariety.map_zpow_add_one_mul_map_zpow_sub_one` (blueprint:
  `cor:cube-mulby-recursion`) — the recursion for `[n]^*L`.
- `AlgebraicGeometry.IsAbelianVariety.map_zpow` (blueprint: `thm:cube-mulby-pullback`) — the
  pullback formula for `[n]^*L`, for `n : ℤ`, and
  `AlgebraicGeometry.IsAbelianVariety.map_zpow_of_isSymmetric` — its symmetric form
  `[n]^*L ≅ L^⊗(n²)`, which specialises to the `ℕ`-indexed
  `AlgebraicGeometry.IsAbelianVariety.mulBy` as
  `AlgebraicGeometry.IsAbelianVariety.map_mulBy_of_isSymmetric` and, on sheaves, as
  `AlgebraicGeometry.IsAbelianVariety.nonempty_pullback_mulBy_iso_tensorPow`.

Also proved, as the bridge to the theorem of the cube:

- `AlgebraicGeometry.Scheme.Pic.eq_one_of_map_sliceInclusion_eq_one` — the theorem of the cube
  read in the Picard group rather than on sheaves.

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
  phrased in: `AlgebraicGeometry.IsAbelianVariety.cubeClass` is the class of `Θ(L)`, and
  triviality is `cubeClass … = 1`. The sheaf-level forms are corollaries, obtained through
  `AlgebraicGeometry.Scheme.Pic.mk_eq_mk_iff`.
* The sheaf-level form of the cube identity,
  `AlgebraicGeometry.IsAbelianVariety.nonempty_cube_iso`, is stated with the three inverses
  moved to the other side of the isomorphism,
  `(f+g+h)^*L ⊗ f^*L ⊗ g^*L ⊗ h^*L ≅ (f+g)^*L ⊗ (f+h)^*L ⊗ (g+h)^*L`,
  which is equivalent to the triviality of `Θ(L)` and avoids naming tensor inverses.
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

/-! ### The theorem of the cube in the Picard group -/

namespace Scheme.Pic

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}}

/-- **The theorem of the cube, read in the Picard group** (blueprint: `thm:cube-cube`).

This is the theorem of the cube,
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_structureModules_of_map_sliceInclusion_eq_one`,
with "trivial" spelled as "of trivial class in the Picard group" throughout; the two spellings
are exchanged by `AlgebraicGeometry.Scheme.Pic.mk_eq_one_iff`, and every class in the Picard
group is the class of a line bundle by `AlgebraicGeometry.Scheme.Pic.exists_mk`.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
`WeilConjectures.AlgebraicGeometry.TheoremOfCube.Basic`. -/
theorem eq_one_of_map_sliceInclusion_eq_one
    (πX : X ⟶ Spec (.of K)) [IsProper πX] [GeometricallyIntegral πX]
    (πY : Y ⟶ Spec (.of K)) [IsProper πY] [GeometricallyIntegral πY]
    (πZ : Z ⟶ Spec (.of K)) [LocallyOfFiniteType πZ] [QuasiCompact πZ]
    [IsReduced Z] [ConnectedSpace Z]
    (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _)
    (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _)
    (z₀ : Spec (.of K) ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 _)
    (hkunneth : ∀ (t : Z) (n : ℕ), IsCubeKunneth πX πY πZ x₀ hx₀ y₀ hy₀ t n)
    (x : (Limits.pullback (Limits.pullback.fst πX πY ≫ πX) πZ).Pic)
    (hz : Pic.map (sliceInclusionFst (Limits.pullback.fst πX πY ≫ πX) πZ z₀ hz₀) x = 1)
    (hX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) x = 1)
    (hY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) x = 1) :
    x = 1 := by
  obtain ⟨L, hL, rfl⟩ := Pic.exists_mk x
  rw [Pic.mk_eq_one_iff, ← Modules.nonempty_iso_structureModules_iff]
  exact Modules.nonempty_iso_structureModules_of_map_sliceInclusion_eq_one
    πX πY πZ x₀ hx₀ y₀ hy₀ hkunneth z₀ hz₀ hL hz hX hY

end Scheme.Pic

namespace IsAbelianVariety

/-! ### The cube class -/

section CubeClass

variable {K : Type u} [Field K] {G : Over (Spec (.of K))} [GrpObj G]
  {V W : Over (Spec (.of K))}

variable (G) in
/-- The identity `e ∈ G(K)` of a group scheme over `K`, read as a morphism of schemes, is a
section of the structure morphism, i.e. a `K`-rational point. -/
@[reassoc]
theorem one_left_comp_hom : η[G].left ≫ G.hom = 𝟙 (Spec (.of K)) :=
  Over.w η[G]

/-- The class in the Picard group of `S` of the **cube bundle**

`(f+g+h)^*L ⊗ (f+g)^*L⁻¹ ⊗ (f+h)^*L⁻¹ ⊗ (g+h)^*L⁻¹ ⊗ f^*L ⊗ g^*L ⊗ h^*L`

attached to the class `ℓ` of a line bundle `L` on a group scheme `G` over `K` and to three
`S`-points `f`, `g`, `h` of `G`. The cube identity says that it is trivial when `G` is an
abelian variety, see `AlgebraicGeometry.IsAbelianVariety.cubeClass_eq_one`.

Taking `S = G × G × G` and `f`, `g`, `h` the three projections gives the class of the bundle
`Θ(L)` of the blueprint. -/
noncomputable def cubeClass (f g h : W ⟶ G) (ℓ : G.left.Pic) : W.left.Pic :=
  Pic.map (f * g * h).left ℓ * (Pic.map (f * g).left ℓ)⁻¹ * (Pic.map (f * h).left ℓ)⁻¹ *
    (Pic.map (g * h).left ℓ)⁻¹ * Pic.map f.left ℓ * Pic.map g.left ℓ * Pic.map h.left ℓ

/-- **The cube class is natural in the `S`-points**: pulling it back along `σ : T ⟶ S` is the
cube class of the three `T`-points obtained by composing with `σ`. -/
theorem map_cubeClass (σ : V ⟶ W) (f g h : W ⟶ G) (ℓ : G.left.Pic) :
    Pic.map σ.left (cubeClass f g h ℓ) = cubeClass (σ ≫ f) (σ ≫ g) (σ ≫ h) ℓ := by
  simp only [cubeClass, map_mul, map_inv, ← Pic.map_comp_apply, ← Over.comp_left,
    MonObj.comp_mul]

/-- The class of `L` pulled back along the constant morphism at the identity is trivial. -/
theorem map_one_left (ℓ : G.left.Pic) : Pic.map (1 : W ⟶ G).left ℓ = 1 := by
  rw [show ((1 : W ⟶ G)).left = W.hom ≫ η[G].left by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left], Pic.map_comp_apply_eq_one]

/-- **The cube class is trivial as soon as the first of the three points is the identity.** -/
theorem cubeClass_one_left (g h : W ⟶ G) (ℓ : G.left.Pic) : cubeClass 1 g h ℓ = 1 := by
  simp only [cubeClass, one_mul, map_one_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

/-- **The cube class is trivial as soon as the second of the three points is the identity.** -/
theorem cubeClass_one_middle (f h : W ⟶ G) (ℓ : G.left.Pic) : cubeClass f 1 h ℓ = 1 := by
  simp only [cubeClass, one_mul, mul_one, map_one_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

/-- **The cube class is trivial as soon as the third of the three points is the identity.** -/
theorem cubeClass_one_right (f g : W ⟶ G) (ℓ : G.left.Pic) : cubeClass f g 1 ℓ = 1 := by
  simp only [cubeClass, mul_one, map_one_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

end CubeClass

/-! ### The cube identity -/

section Cube

variable {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G]

/-- The slice `A × A × {e}` of the triple product, as a morphism of `K`-schemes: it is the
morphism `lift (𝟙 (A × A)) e` of `Over (Spec K)`. -/
theorem sliceInclusionFst_eq_lift :
    sliceInclusionFst (Limits.pullback.fst G.hom G.hom ≫ G.hom) G.hom η[G].left
        (one_left_comp_hom G) =
      (lift (𝟙 (G ⊗ G)) (toUnit (G ⊗ G) ≫ η[G]) : G ⊗ G ⟶ (G ⊗ G) ⊗ G).left := by
  refine Limits.pullback.hom_ext ?_ ?_ <;>
    simp [sliceInclusionFst, Over.lift_left, Over.comp_left, Over.toUnit_left]

/-- The slice `A × {e} × A` of the triple product, as a morphism of `K`-schemes. -/
theorem pullbackMapSliceInclusionFst_eq_lift :
    pullbackMapSliceInclusionFst G.hom G.hom G.hom η[G].left (one_left_comp_hom G) =
      (lift (lift (fst G G) (toUnit (G ⊗ G) ≫ η[G])) (snd G G) :
        G ⊗ G ⟶ (G ⊗ G) ⊗ G).left := by
  refine Limits.pullback.hom_ext (Limits.pullback.hom_ext ?_ ?_) ?_ <;>
    simp [pullbackMapSliceInclusionFst, sliceInclusionFst, Over.lift_left, Over.comp_left,
      Over.toUnit_left]

/-- The slice `{e} × A × A` of the triple product, as a morphism of `K`-schemes. -/
theorem pullbackMapSliceInclusionSnd_eq_lift :
    pullbackMapSliceInclusionSnd G.hom G.hom G.hom η[G].left (one_left_comp_hom G) =
      (lift (lift (toUnit (G ⊗ G) ≫ η[G]) (fst G G)) (snd G G) :
        G ⊗ G ⟶ (G ⊗ G) ⊗ G).left := by
  refine Limits.pullback.hom_ext (Limits.pullback.hom_ext ?_ ?_) ?_ <;>
    simp [pullbackMapSliceInclusionSnd, sliceInclusionSnd, Over.lift_left, Over.comp_left,
      Over.toUnit_left]

variable [IsAbelianVariety G]

variable (hkunneth : ∀ (t : G.left) (n : ℕ), Scheme.IsCubeKunneth G.hom G.hom G.hom
  η[G].left (one_left_comp_hom G) η[G].left (one_left_comp_hom G) t n)

include hkunneth

/-- **The cube identity on an abelian variety, at the universal point** (blueprint:
`thm:cube-abelian`): the bundle

`Θ(L) = m₁₂₃^*L ⊗ m₁₂^*L⁻¹ ⊗ m₁₃^*L⁻¹ ⊗ m₂₃^*L⁻¹ ⊗ p₁^*L ⊗ p₂^*L ⊗ p₃^*L`

on `A × A × A` is trivial.

This is the theorem of the cube applied with `X = Y = Z = A` and `x₀ = y₀ = z₀ = e`: an abelian
variety is a proper geometrically integral variety over `K`, in particular a connected reduced
`K`-scheme of finite type, and `e` is a `K`-rational point. What has to be checked is that
`Θ(L)` restricts trivially to the three coordinate slices, and on each slice one of the three
points becomes the identity, which makes three of the seven factors cancel against three others
and leaves the pullback of `L` along the constant morphism at `e`, trivial by
`AlgebraicGeometry.Scheme.Pic.map_comp_eq_one`.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem cubeClass_proj_eq_one (ℓ : G.left.Pic) :
    cubeClass (fst (G ⊗ G) G ≫ fst G G) (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ = 1 := by
  refine Scheme.Pic.eq_one_of_map_sliceInclusion_eq_one G.hom G.hom G.hom
    η[G].left (one_left_comp_hom G) η[G].left (one_left_comp_hom G)
    η[G].left (one_left_comp_hom G) hkunneth _ ?_ ?_ ?_
  · rw [sliceInclusionFst_eq_lift]
    refine (map_cubeClass (lift (𝟙 (G ⊗ G)) (toUnit (G ⊗ G) ≫ η[G]))
      (fst (G ⊗ G) G ≫ fst G G) (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ).trans ?_
    simpa only [← Category.assoc, lift_fst, lift_snd, Category.id_comp, ← Hom.one_def] using
      cubeClass_one_right (fst G G) (snd G G) ℓ
  · rw [pullbackMapSliceInclusionFst_eq_lift]
    refine (map_cubeClass (lift (lift (fst G G) (toUnit (G ⊗ G) ≫ η[G])) (snd G G))
      (fst (G ⊗ G) G ≫ fst G G) (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ).trans ?_
    simpa only [← Category.assoc, lift_fst, lift_snd, ← Hom.one_def] using
      cubeClass_one_middle (fst G G) (snd G G) ℓ
  · rw [pullbackMapSliceInclusionSnd_eq_lift]
    refine (map_cubeClass (lift (lift (toUnit (G ⊗ G) ≫ η[G]) (fst G G)) (snd G G))
      (fst (G ⊗ G) G ≫ fst G G) (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ).trans ?_
    simpa only [← Category.assoc, lift_fst, lift_snd, ← Hom.one_def] using
      cubeClass_one_left (fst G G) (snd G G) ℓ

/-- **The cube identity on an abelian variety** (blueprint: `thm:cube-abelian`), in the form of
`S`-points: for every `K`-scheme `S` and all `f, g, h ∈ A(S)`, the line bundle

`(f+g+h)^*L ⊗ (f+g)^*L⁻¹ ⊗ (f+h)^*L⁻¹ ⊗ (g+h)^*L⁻¹ ⊗ f^*L ⊗ g^*L ⊗ h^*L`

on `S` is trivial. It is the pullback of `Θ(L)` along `(f, g, h) : S ⟶ A × A × A`, so this is
`AlgebraicGeometry.IsAbelianVariety.cubeClass_proj_eq_one` pulled back.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem cubeClass_eq_one {W : Over (Spec (.of K))} (f g h : W ⟶ G) (ℓ : G.left.Pic) :
    cubeClass f g h ℓ = 1 := by
  have h₁ := map_cubeClass (lift (lift f g) h) (fst (G ⊗ G) G ≫ fst G G)
    (fst (G ⊗ G) G ≫ snd G G) (snd (G ⊗ G) G) ℓ
  rw [cubeClass_proj_eq_one G hkunneth, map_one] at h₁
  simpa only [← Category.assoc, lift_fst, lift_snd] using h₁.symm

/-- **The cube identity on an abelian variety**, on sheaves (blueprint: `thm:cube-abelian`).

For every `K`-scheme `S` and all `f, g, h ∈ A(S)`,

`(f+g+h)^*L ⊗ f^*L ⊗ g^*L ⊗ h^*L ≅ (f+g)^*L ⊗ (f+h)^*L ⊗ (g+h)^*L`.

This is the triviality of the cube bundle `Θ(L)` of
`AlgebraicGeometry.IsAbelianVariety.cubeClass_eq_one`, with the three inverses moved to the
other side of the isomorphism so that no tensor inverse has to be named. -/
theorem nonempty_cube_iso {W : Over (Spec (.of K))} (f g h : W ⟶ G) {L : G.left.Modules}
    (hL : L.Invertible) :
    Nonempty ((Modules.pullback (f * g * h).left).obj L ⊗ (Modules.pullback f.left).obj L ⊗
        (Modules.pullback g.left).obj L ⊗ (Modules.pullback h.left).obj L ≅
      (Modules.pullback (f * g).left).obj L ⊗ (Modules.pullback (f * h).left).obj L ⊗
        (Modules.pullback (g * h).left).obj L) := by
  have hA : ((Modules.pullback (f * g * h).left).obj L).Invertible := hL.pullback _
  have hB : ((Modules.pullback f.left).obj L).Invertible := hL.pullback _
  have hC : ((Modules.pullback g.left).obj L).Invertible := hL.pullback _
  have hD : ((Modules.pullback h.left).obj L).Invertible := hL.pullback _
  have hE : ((Modules.pullback (f * g).left).obj L).Invertible := hL.pullback _
  have hF : ((Modules.pullback (f * h).left).obj L).Invertible := hL.pullback _
  have hG : ((Modules.pullback (g * h).left).obj L).Invertible := hL.pullback _
  rw [← Pic.mk_eq_mk_iff (hM := hA.tensorObj (hB.tensorObj (hC.tensorObj hD)))
      (hN := hE.tensorObj (hF.tensorObj hG)),
    Pic.mk_tensorObj (hM := hA) (hN := hB.tensorObj (hC.tensorObj hD)),
    Pic.mk_tensorObj (hM := hB) (hN := hC.tensorObj hD),
    Pic.mk_tensorObj (hM := hC) (hN := hD),
    Pic.mk_tensorObj (hM := hE) (hN := hF.tensorObj hG),
    Pic.mk_tensorObj (hM := hF) (hN := hG)]
  have key := cubeClass_eq_one G hkunneth f g h (Pic.mk L hL)
  rw [cubeClass] at key
  simp only [Pic.map_mk] at key
  apply Additive.ofMul.injective
  replace key := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at key
  simp only [ofMul_mul]
  linear_combination (norm := abel) key

/-! ### The recursion and the pullback formula -/

/-- **The recursion for `[n]^*L`** (blueprint: `cor:cube-mulby-recursion`): for every `n : ℤ`,

`[n+1]^*L ⊗ [n-1]^*L ≅ ([n]^*L)^⊗2 ⊗ L ⊗ [-1]^*L`,

read in the Picard group of `A`.

This is the `S`-points form of the cube identity,
`AlgebraicGeometry.IsAbelianVariety.cubeClass_eq_one`, taken at `S = A` with `f = [n]`,
`g = [1] = 𝟙` and `h = [-1]`, so that `f+g = [n+1]`, `f+h = [n-1]`, `g+h = [0]` and
`f+g+h = [n]`; the factor `[0]^*L` is trivial because `[0]` is the constant morphism at `e`.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem map_zpow_add_one_mul_map_zpow_sub_one (ℓ : G.left.Pic) (n : ℤ) :
    Pic.map (GrpObj.zpow G (n + 1)).left ℓ * Pic.map (GrpObj.zpow G (n - 1)).left ℓ =
      Pic.map (GrpObj.zpow G n).left ℓ ^ 2 * ℓ * Pic.map (GrpObj.zpow G (-1)).left ℓ := by
  have hmul : ∀ m k : ℤ, GrpObj.zpow G m * GrpObj.zpow G k = GrpObj.zpow G (m + k) := by
    intro m k
    rw [Hom.mul_def, ← GrpObj.zpow_add]
  have key := cubeClass_eq_one G hkunneth (GrpObj.zpow G n) (GrpObj.zpow G 1)
    (GrpObj.zpow G (-1)) ℓ
  rw [cubeClass] at key
  simp only [hmul] at key
  rw [show n + 1 + (-1 : ℤ) = n by ring, show n + (-1 : ℤ) = n - 1 by ring,
    show (1 : ℤ) + (-1 : ℤ) = 0 by norm_num, GrpObj.zpow_zero, ← Hom.one_def, map_one_left,
    GrpObj.zpow_one, Over.id_left, Pic.map_id, MonoidHom.id_apply] at key
  apply Additive.ofMul.injective
  replace key := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at key
  simp only [ofMul_mul, ofMul_pow]
  linear_combination (norm := abel) -key

/-- **The pullback of a line bundle along `[n]`** (blueprint: `thm:cube-mulby-pullback`): for
every `n : ℤ`, writing `N := [-1]^*L`,

`[n]^*L ≅ L^⊗((n²+n)/2) ⊗ N^⊗((n²-n)/2)`,

read in the Picard group of `A`. The two exponents `n(n+1)/2` and `n(n-1)/2` are integers, and
in fact non-negative ones, for every `n : ℤ`.

The proof is the two-directional induction over `ℤ` that the blueprint spells out: the three
base cases `n = 0, 1, -1`, the second-difference identity `a(n+1) + a(n-1) = 2a(n) + 1` for
both exponents, and the recursion
`AlgebraicGeometry.IsAbelianVariety.map_zpow_add_one_mul_map_zpow_sub_one`, which determines
each of `[n+1]^*L` and `[n-1]^*L` from the other two.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem map_zpow (ℓ : G.left.Pic) (n : ℤ) :
    Pic.map (GrpObj.zpow G n).left ℓ =
      ℓ ^ (n * (n + 1) / 2) * Pic.map (GrpObj.zpow G (-1)).left ℓ ^ (n * (n - 1) / 2) := by
  -- the exponents are integers, and satisfy the second-difference identity
  have hdvd : ∀ m : ℤ, 2 * (m * (m + 1) / 2) = m * (m + 1) := by
    intro m
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self m
    rw [hk]
    omega
  have hdvd' : ∀ m : ℤ, 2 * (m * (m - 1) / 2) = m * (m - 1) := by
    intro m
    have h := hdvd (m - 1)
    rwa [show m - 1 + 1 = m by ring, mul_comm (m - 1) m] at h
  have ha : ∀ m : ℤ, (m + 1) * (m + 1 + 1) / 2 + (m - 1) * (m - 1 + 1) / 2 =
      m * (m + 1) / 2 + m * (m + 1) / 2 + 1 := by
    intro m
    linarith [hdvd (m + 1), hdvd (m - 1), hdvd m]
  have hb : ∀ m : ℤ, (m + 1) * (m + 1 - 1) / 2 + (m - 1) * (m - 1 - 1) / 2 =
      m * (m - 1) / 2 + m * (m - 1) / 2 + 1 := by
    intro m
    linarith [hdvd' (m + 1), hdvd' (m - 1), hdvd' m]
  -- the abstract two-directional induction: two solutions of the second-order recursion
  -- `u(m+1) * u(m-1) = u(m)² * c` agreeing at `-1`, `0` and `1` agree everywhere
  have key : ∀ (F E : ℤ → G.left.Pic) (c : G.left.Pic),
      (∀ m : ℤ, F (m + 1) * F (m - 1) = F m * F m * c) →
      (∀ m : ℤ, E (m + 1) * E (m - 1) = E m * E m * c) →
      F 0 = E 0 → F 1 = E 1 → F (-1) = E (-1) → ∀ m : ℤ, F m = E m := by
    intro F E c hF hE h0 h1 hm1
    suffices h : ∀ m : ℤ, F m = E m ∧ F (m + 1) = E (m + 1) from fun m ↦ (h m).1
    intro m
    induction m using Int.induction_on with
    | zero => exact ⟨h0, h1⟩
    | succ i ih =>
        refine ⟨ih.2, ?_⟩
        have e1 := hF ((i : ℤ) + 1)
        have e2 := hE ((i : ℤ) + 1)
        rw [show (i : ℤ) + 1 - 1 = (i : ℤ) by ring] at e1 e2
        refine mul_right_cancel (b := F (i : ℤ)) ?_
        rw [e1, ih.1, ih.2, e2]
    | pred i ih =>
        refine ⟨?_, by rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]; exact ih.1⟩
        have e1 := hF (-(i : ℤ))
        have e2 := hE (-(i : ℤ))
        refine mul_left_cancel (a := F (-(i : ℤ) + 1)) ?_
        rw [e1, ih.1, ih.2, e2]
  set ν := Pic.map (GrpObj.zpow G (-1)).left ℓ with hν
  have hcomb : ∀ p q r s : ℤ, ℓ ^ p * ν ^ q * (ℓ ^ r * ν ^ s) = ℓ ^ (p + r) * ν ^ (q + s) := by
    intro p q r s
    rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  refine key (fun m ↦ Pic.map (GrpObj.zpow G m).left ℓ)
    (fun m ↦ ℓ ^ (m * (m + 1) / 2) * ν ^ (m * (m - 1) / 2)) (ℓ * ν) ?_ ?_ ?_ ?_ ?_ n
  · intro m
    rw [hν]
    have h := map_zpow_add_one_mul_map_zpow_sub_one G hkunneth ℓ m
    rwa [pow_two, mul_assoc] at h
  · intro m
    rw [hcomb, ha m, hb m, zpow_add, zpow_add, zpow_add, zpow_add, zpow_one, zpow_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel
  · rw [GrpObj.zpow_zero, ← Hom.one_def, map_one_left]
    norm_num
  · rw [GrpObj.zpow_one, Over.id_left, Pic.map_id, MonoidHom.id_apply]
    norm_num
  · rw [hν]
    norm_num

/-- **The pullback of a symmetric line bundle along `[n]`** (blueprint:
`thm:cube-mulby-pullback`): if `[-1]^*L ≅ L`, then `[n]^*L ≅ L^⊗(n²)` for every `n : ℤ`, read
in the Picard group of `A`.

This is the case `N = L` of `AlgebraicGeometry.IsAbelianVariety.map_zpow`, the two exponents
adding up to `n(n+1)/2 + n(n-1)/2 = n²`.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem map_zpow_of_isSymmetric {L : G.left.Modules} (hL : L.Invertible)
    (hsymm : L.IsSymmetric G) (n : ℤ) :
    Pic.map (GrpObj.zpow G n).left (Pic.mk L hL) = Pic.mk L hL ^ (n ^ 2) := by
  have hnu : Pic.map (GrpObj.zpow G (-1)).left (Pic.mk L hL) = Pic.mk L hL := by
    rw [GrpObj.zpow_neg_one, Pic.map_mk, Pic.mk_eq_mk_iff]
    exact hsymm
  have hexp : n * (n + 1) / 2 + n * (n - 1) / 2 = n ^ 2 := by
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
    have h1 : n * (n + 1) = 2 * k := by rw [hk]; ring
    have h2 : n * (n - 1) = 2 * k - 2 * n := by linarith [h1]
    have h3 : n ^ 2 = 2 * k - n := by linarith [h1]
    rw [h1, h2, h3]
    omega
  rw [map_zpow G hkunneth _ n, hnu, ← zpow_add, hexp]

/-- **The pullback of a symmetric line bundle along `[n]` for `n : ℕ`**: if `[-1]^*L ≅ L`, then
`[n]^*L ≅ L^⊗(n²)`, read in the Picard group of `A`.

This is `AlgebraicGeometry.IsAbelianVariety.map_zpow_of_isSymmetric` specialised along
`CategoryTheory.GrpObj.zpow_natCast` to the `ℕ`-indexed multiplication-by-`n` endomorphism
`AlgebraicGeometry.IsAbelianVariety.mulBy`, which is what the theory of the isogeny `[n]` is
stated in terms of. -/
theorem map_mulBy_of_isSymmetric {L : G.left.Modules} (hL : L.Invertible)
    (hsymm : L.IsSymmetric G) (n : ℕ) :
    Pic.map (mulBy G n).left (Pic.mk L hL) = Pic.mk L hL ^ ((n : ℤ) ^ 2) := by
  have h : mulBy G n = GrpObj.zpow G (n : ℤ) := (GrpObj.zpow_natCast G n).symm
  rw [h, map_zpow_of_isSymmetric G hkunneth hL hsymm]

/-- **The pullback of a symmetric line bundle along `[n]`, on sheaves**: if `[-1]^*L ≅ L`, then
`[n]^*L ≅ L^⊗(n²)` for every `n : ℕ`.

This is the form the degree computation for the isogeny `[n]` uses: for a symmetric ample line
bundle `L`, which exists on every abelian variety by
`AlgebraicGeometry.IsAbelianVariety.exists_invertible_isAmple_isSymmetric`, it identifies
`[n]^*L` with the `n²`-th tensor power of `L`.

The Künneth hypothesis `hkunneth` is carried, not discharged; see the implementation notes of
this file. -/
theorem nonempty_pullback_mulBy_iso_tensorPow {L : G.left.Modules} (hL : L.Invertible)
    (hsymm : L.IsSymmetric G) (n : ℕ) :
    Nonempty ((Modules.pullback (mulBy G n).left).obj L ≅ L ^⊗ (n ^ 2)) := by
  rw [← Pic.mk_eq_mk_iff (hM := hL.pullback _) (hN := hL.tensorPow (n ^ 2)),
    ← Pic.map_mk (mulBy G n).left hL, Pic.mk_tensorPow (hM := hL),
    map_mulBy_of_isSymmetric G hkunneth hL hsymm]
  norm_cast

end Cube

end IsAbelianVariety

end AlgebraicGeometry
