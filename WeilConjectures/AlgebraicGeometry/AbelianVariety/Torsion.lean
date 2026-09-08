/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
public import WeilConjectures.Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.Mathlib.GroupTheory.FiniteAbelian.Basic

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
- `AlgebraicGeometry.IsAbelianVariety.finite_torsionHom` and
  `AlgebraicGeometry.IsAbelianVariety.natCard_torsionHom`: if `K` is algebraically closed and `n`
  is invertible in `K`, then `A[n]` has finitely many points with values in `K`, in fact exactly
  `n ^ (2 * g)` of them.
- `AlgebraicGeometry.IsAbelianVariety.nonempty_torsionHom_mulEquiv_pi`: if `K` is algebraically
  closed and `n` is invertible in `K`, then `A[n](K) ≅ (ℤ/n)^(2 * g)`.

The finiteness, flatness, rank and étaleness of `A[n]` are obtained from the corresponding
statements for the isogeny `[n] : A ⟶ A` in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny` by base change along the identity
section `η[A] : Spec K ⟶ A`, since `A[n]` is by definition the kernel of `[n]`. The number of
`K`-points of `A[n]` is then its rank over `K`, because `A[n]` is finite étale over the
algebraically closed field `K`, and the group `A[n](K)` is determined by these counts for all
divisors of `n` via `CommGroup.nonempty_equiv_pi_multiplicative_zmod_of_card_torsion`.

## Implementation notes

The elementary facts about the kernel of the `n`-th power map of an abstract commutative group
that are used to identify the `m`-torsion of `A[n](K)` with `A[m](K)` are kept as private lemmas
in this file.

## Blueprint

`isFinite_torsion`, `flat_torsion`, `finrank_torsion` and `etale_torsion` are the geometric half
of Proposition 2.8 of §2.6 of `blueprint/curve_estimates.pdf`, and `natCard_torsionHom` together
with `nonempty_torsionHom_mulEquiv_pi` are its group-theoretic half.
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

section Points

/-- If `n` is invertible in a field `K` and `m` divides `n`, then `m` is invertible in `K`. -/
private lemma natCast_ne_zero_of_dvd {F : Type*} [Field F] {m n : ℕ} (hn : (n : F) ≠ 0)
    (hm : m ∣ n) : (m : F) ≠ 0 := fun h =>
  hn ((ringChar.spec F n).mpr (((ringChar.spec F m).mp h).trans hm))

/-- An element of the kernel of the `n`-th power map of a commutative group is killed by `n`. -/
private lemma pow_eq_one_of_mem_ker_powMonoidHom {H : Type*} [CommGroup H] (n : ℕ)
    (y : (powMonoidHom n : H →* H).ker) : y ^ n = 1 := by
  rw [← OneMemClass.coe_eq_one, SubmonoidClass.coe_pow]
  simpa using MonoidHom.mem_ker.mp y.2

/-- If `m` divides `n`, the `m`-torsion of the kernel of the `n`-th power map of a commutative
group is the kernel of the `m`-th power map. -/
private def kerPowMonoidHomTorsionEquiv {H : Type*} [CommGroup H] {m n : ℕ}
    (hmn : m ∣ n) :
    {x : (powMonoidHom n : H →* H).ker // x ^ m = 1} ≃ (powMonoidHom m : H →* H).ker where
  toFun x := ⟨(x.1 : H), by
    have h := x.2
    rw [← OneMemClass.coe_eq_one, SubmonoidClass.coe_pow] at h
    simpa using h⟩
  invFun y :=
    have hy : (y.1 : H) ^ m = 1 := by simpa using MonoidHom.mem_ker.mp y.2
    ⟨⟨(y.1 : H), by
      obtain ⟨k, rfl⟩ := hmn
      simp [MonoidHom.mem_ker, pow_mul, hy]⟩, by
      rw [← OneMemClass.coe_eq_one, SubmonoidClass.coe_pow]
      simpa using hy⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [IsAlgClosed K]

/-- If `n` is invertible in an algebraically closed field `K`, then the group `A[n](K)` of
`K`-points of the `n`-torsion of an abelian variety `A` over `K` is finite. -/
theorem finite_torsionHom (hn : (n : K) ≠ 0) :
    Finite (𝟙_ (Over (Spec (.of K))) ⟶ torsion G n) := by
  have hn₀ : n ≠ 0 := by rintro rfl; simp at hn
  have := isFinite_torsion G n hn₀
  have := etale_torsion G n hn
  have : Finite (torsion G n).left := finite_of_isFinite_over_field (torsion G n).hom
  exact .of_equiv _
    ((Over.unitHomEquiv (torsion G n)).trans (pointEquiv (torsion G n).hom)).symm

variable {g : ℕ} [SmoothOfRelativeDimension g G.hom]

/-- If `n` is invertible in an algebraically closed field `K`, then the `n`-torsion of an abelian
variety `A` of dimension `g` over `K` has exactly `n ^ (2 * g)` points with values in `K`. This is
the rank of `A[n]` over `K`, since `A[n]` is finite étale over the algebraically closed field
`K`. -/
theorem natCard_torsionHom (hn : (n : K) ≠ 0) :
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ torsion G n) = n ^ (2 * g) := by
  have hn₀ : n ≠ 0 := by rintro rfl; simp at hn
  have := isFinite_torsion G n hn₀
  have := etale_torsion G n hn
  rw [Nat.card_congr (Over.unitHomEquiv (torsion G n)),
    natCard_pointHom_eq_finrank (torsion G n).hom (IsLocalRing.closedPoint K),
    finrank_torsion (g := g) G n hn₀]

/-- **Proposition 2.8**: if `n` is invertible in an algebraically closed field `K`, then the group
`A[n](K)` of `K`-points of the `n`-torsion of an abelian variety `A` of dimension `g` over `K` is
isomorphic to `(ℤ/n)^(2 * g)`.

The point is that for every `m` dividing `n`, the `m`-torsion of `A[n](K)` is `A[m](K)`, which has
`m ^ (2 * g)` elements by `AlgebraicGeometry.IsAbelianVariety.natCard_torsionHom`; a finite abelian
group killed by `n` with this many `m`-torsion points for all `m ∣ n` is free of rank `2 * g`
over `ℤ/n`. -/
theorem nonempty_torsionHom_mulEquiv_pi (hn : (n : K) ≠ 0) :
    Nonempty ((𝟙_ (Over (Spec (.of K))) ⟶ torsion G n) ≃*
      (Fin (2 * g) → Multiplicative (ZMod n))) := by
  have hn₀ : n ≠ 0 := by rintro rfl; simp at hn
  have := finite_torsionHom G n hn
  have : Finite (powMonoidHom n : (𝟙_ (Over (Spec (.of K))) ⟶ G) →* _).ker :=
    .of_equiv _ (torsionHomMulEquiv G n _).toEquiv
  obtain ⟨e⟩ := CommGroup.nonempty_equiv_pi_multiplicative_zmod_of_card_torsion
    (G := (powMonoidHom n : (𝟙_ (Over (Spec (.of K))) ⟶ G) →* _).ker) (r := 2 * g) hn₀
    (pow_eq_one_of_mem_ker_powMonoidHom n) fun m hm => by
      rw [Nat.card_congr ((kerPowMonoidHomTorsionEquiv hm).trans
          (torsionHomMulEquiv G m (𝟙_ (Over (Spec (.of K))))).toEquiv.symm),
        natCard_torsionHom (g := g) G m (natCast_ne_zero_of_dvd hn hm)]
  exact ⟨(torsionHomMulEquiv G n _).trans e⟩

end Points

end AlgebraicGeometry.IsAbelianVariety
