/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The `n`-torsion subgroup scheme of an abelian variety

Let `A` be an abelian variety over a field `K` and let `n : ℕ`. Since `A` is commutative, the
multiplication by `n` map `[n] : A ⟶ A` is a homomorphism of group schemes, so it has a kernel
in the sense of `CategoryTheory.GrpObj.ker`. This kernel is the `n`-torsion subgroup scheme
`A[n]`.

## Main definitions

- `AlgebraicGeometry.IsAbelianVariety.torsion`: the `n`-torsion subgroup scheme `A[n]` of an
  abelian variety `A`, as a group scheme over `K`.

## Main results

- `AlgebraicGeometry.IsAbelianVariety.torsionHomMulEquiv`: the `T`-points of `A[n]` are exactly
  the `T`-points of `A` killed by `n`. Taking `T = Spec K`, the `K`-points of `A[n]` are the
  `n`-torsion of the group `A(K)`.
- `A[n]` is a closed subscheme of `A`, and is proper and separated over `K`.
- `AlgebraicGeometry.IsAbelianVariety.isFinite_torsion` and
  `AlgebraicGeometry.IsAbelianVariety.flat_torsion`: for `n ≠ 0`, the scheme `A[n]` is finite and
  flat over `K`.
- `AlgebraicGeometry.IsAbelianVariety.finrank_torsion`: for `n ≠ 0`, the rank of `A[n]` over `K`
  is `n ^ (2 * g)`, where `g` is the dimension of `A`.
- `AlgebraicGeometry.IsAbelianVariety.etale_torsion`: if `n` is invertible in `K`, then `A[n]` is
  étale over `K`.

The last four are obtained from the corresponding statements for the isogeny `[n] : A ⟶ A` in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny` by base change along the identity
section `η[A] : Spec K ⟶ A`, since `A[n]` is by definition the kernel of `[n]`.

## Blueprint

`isFinite_torsion`, `flat_torsion`, `finrank_torsion` and `etale_torsion` are the geometric half
of Proposition 2.8 of §2.6 of `blueprint/curve_estimates.pdf`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry.IsAbelianVariety

universe u

variable {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] [IsAbelianVariety G] (n : ℕ)

/-- The `n`-torsion subgroup scheme `A[n]` of an abelian variety `A` over `K`: the kernel of the
multiplication by `n` isogeny `[n] : A ⟶ A`. -/
noncomputable def torsion : Over (Spec (.of K)) :=
  GrpObj.ker (GrpObj.npow G n)

/-- The `n`-torsion `A[n]` is a group scheme over `K`. -/
noncomputable instance : GrpObj (torsion G n) :=
  inferInstanceAs (GrpObj (GrpObj.ker (GrpObj.npow G n)))

/-- The inclusion `A[n] ⟶ A` is a closed immersion, since it is the base change of the identity
section of `A` along `[n]`. -/
instance : IsClosedImmersion (GrpObj.kerι (GrpObj.npow G n)).left :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    ((Over.forget (Spec (.of K))).map_isPullback
      (GrpObj.isPullback_kerι (GrpObj.npow G n)).flip)
    (inferInstanceAs (IsClosedImmersion η[G].left))

/-- The `n`-torsion of an abelian variety is proper over the base field. -/
instance : IsProper (torsion G n).hom := by
  have h : (torsion G n).hom = (GrpObj.kerι (GrpObj.npow G n)).left ≫ G.hom :=
    (Over.w (GrpObj.kerι (GrpObj.npow G n))).symm
  rw [h]
  infer_instance

/-- The `n`-torsion of an abelian variety is separated over the base field. -/
instance : IsSeparated (torsion G n).hom := inferInstance

omit [IsAbelianVariety G] in
/-- The `n`-torsion `A[n]` is the kernel of the multiplication by `n` isogeny `[n] : A ⟶ A`. -/
lemma torsion_eq_ker_mulBy : torsion G n = GrpObj.ker (mulBy G n) := rfl

omit [IsAbelianVariety G] in
/-- The defining pullback square of `A[n]`: it is the base change of the multiplication by `n`
isogeny `[n] : A ⟶ A` along the identity section `η[A] : Spec K ⟶ A`. -/
lemma isPullback_torsion :
    IsPullback (GrpObj.kerι (mulBy G n)).left (torsion G n).hom (mulBy G n).left η[G].left :=
  (Over.forget (Spec (.of K))).map_isPullback (GrpObj.isPullback_kerι (mulBy G n))

/-- For `n ≠ 0`, the `n`-torsion `A[n]` of an abelian variety is finite over the base field,
being the base change of the finite morphism `[n]`. -/
theorem isFinite_torsion (hn : n ≠ 0) : IsFinite (torsion G n).hom :=
  have := isFinite_mulBy G hn
  MorphismProperty.of_isPullback (isPullback_torsion G n) ‹_›

/-- For `n ≠ 0`, the `n`-torsion `A[n]` of an abelian variety is flat over the base field,
being the base change of the flat morphism `[n]`. -/
theorem flat_torsion (hn : n ≠ 0) : Flat (torsion G n).hom :=
  have := flat_mulBy G hn
  MorphismProperty.of_isPullback (isPullback_torsion G n) ‹_›

/-- For `n ≠ 0`, the `n`-torsion `A[n]` of an abelian variety of dimension `g` has rank
`n ^ (2 * g)` over the base field, this being the degree of the isogeny `[n]`. -/
theorem finrank_torsion {g : ℕ} [SmoothOfRelativeDimension g G.hom] (hn : n ≠ 0)
    (x : Spec (.of K)) : (torsion G n).hom.finrank x = n ^ (2 * g) := by
  have := isFinite_mulBy G hn
  have := flat_mulBy G hn
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_torsion G n) x,
    finrank_mulBy (g := g) G hn]

/-- If `n` is invertible in the base field `K`, then the `n`-torsion `A[n]` of an abelian variety
is étale over `K`, being the base change of the étale morphism `[n]`. -/
theorem etale_torsion (hn : (n : K) ≠ 0) : Etale (torsion G n).hom :=
  have := etale_mulBy G hn
  MorphismProperty.of_isPullback (isPullback_torsion G n) ‹_›

/-- The `T`-points of `A[n]` are exactly the `n`-torsion `T`-points of `A`. Taking
`T = Spec K`, this says that the `K`-points of `A[n]` are the `n`-torsion of the group `A(K)`. -/
noncomputable def torsionHomMulEquiv (T : Over (Spec (.of K))) :
    (T ⟶ torsion G n) ≃* (powMonoidHom n : (T ⟶ G) →* (T ⟶ G)).ker :=
  (GrpObj.kerHomMulEquiv (GrpObj.npow G n) T).trans <| MulEquiv.subgroupCongr <| by
    ext x
    simp [MonoidHom.mem_ker, GrpObj.comp_npow]

@[simp]
lemma coe_torsionHomMulEquiv {T : Over (Spec (.of K))} (a : T ⟶ torsion G n) :
    ((torsionHomMulEquiv G n T a : (powMonoidHom n : (T ⟶ G) →* (T ⟶ G)).ker) : T ⟶ G) =
      a ≫ GrpObj.kerι (GrpObj.npow G n) :=
  rfl

end AlgebraicGeometry.IsAbelianVariety
