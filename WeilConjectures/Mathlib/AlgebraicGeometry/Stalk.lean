/-
Copyright (c) 2026 The Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Infinitesimal neighbourhoods of a point of a scheme

For a scheme `X` and a point `x : X` we define the `n`-th infinitesimal neighbourhood
`Xₙ = Spec (𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1))` of `x` in `X`, together with its canonical morphism to `X`.

The last section base changes a morphism `f : W ⟶ T` along `Tₙ ⟶ T` for a point `t` of `T`.

## Main definitions

- `AlgebraicGeometry.Scheme.infinitesimalRing X x n`: the ring `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)`.
- `AlgebraicGeometry.Scheme.infinitesimalNeighborhood X x n`: the scheme
  `Spec (𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1))`.
- `AlgebraicGeometry.Scheme.fromInfinitesimalNeighborhood X x n`: the canonical morphism
  `Xₙ ⟶ X`.
- `AlgebraicGeometry.Scheme.infinitesimalNeighborhoodMap X x h`: for `m ≤ n`, the closed
  immersion `Xₘ ⟶ Xₙ`, compatible with the morphisms to `X`.
- `AlgebraicGeometry.Scheme.infinitesimalBaseChange f t n`: the base change `W ×_T Tₙ` of
  `f : W ⟶ T` along `Tₙ ⟶ T`, together with its two projections
  `AlgebraicGeometry.Scheme.infinitesimalBaseChangeFst` and
  `AlgebraicGeometry.Scheme.infinitesimalBaseChangeSnd` and the transition morphisms
  `AlgebraicGeometry.Scheme.infinitesimalBaseChangeMap`.
- `AlgebraicGeometry.Scheme.toInfinitesimalBaseChangeΓ`: the ring map
  `𝒪_{T, t} ⟶ Γ(W ×_T Tₙ, 𝒪)`.

## Main results

- `AlgebraicGeometry.Scheme.infinitesimalNeighborhoodIsoSpecResidueField`: `X₀ ≅ Spec κ(x)`,
  and `AlgebraicGeometry.Scheme.descResidueField_fromInfinitesimalNeighborhood_zero`, which says
  that a `K`-rational point `Spec K ⟶ X` factors through `X₀ ⟶ X`.
- `AlgebraicGeometry.Scheme.finite_infinitesimalRing`: for a `k`-rational point of a locally
  noetherian scheme, `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` is a finite-dimensional `k`-algebra.
- `AlgebraicGeometry.Scheme.preimage_infinitesimalBaseChangeFst_eq_top`: every point of
  `W ×_T Tₙ` lies over `t`, so `W ×_T Tₙ` lies over every open neighbourhood of `t`.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (x : X)

section Ring

/-- The ring `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` of the `n`-th infinitesimal neighbourhood of `x`. -/
noncomputable def infinitesimalRing (n : ℕ) : CommRingCat.{u} :=
  .of (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ (n + 1))

instance (n : ℕ) : IsLocalRing (X.infinitesimalRing x n) :=
  inferInstanceAs
    (IsLocalRing (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ (n + 1)))

/-- The quotient map `𝒪_{X, x} ⟶ 𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)`. -/
noncomputable def toInfinitesimalRing (n : ℕ) : X.presheaf.stalk x ⟶ X.infinitesimalRing x n :=
  CommRingCat.ofHom (Ideal.Quotient.mk _)

lemma toInfinitesimalRing_surjective (n : ℕ) :
    Function.Surjective (X.toInfinitesimalRing x n) :=
  Ideal.Quotient.mk_surjective

instance (n : ℕ) : IsLocalHom (X.toInfinitesimalRing x n).hom :=
  IsLocalHom.of_surjective _ (X.toInfinitesimalRing_surjective x n)

/-- For `m ≤ n`, the transition map `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1) ⟶ 𝒪_{X, x} ⧸ 𝔪_x ^ (m + 1)`. -/
noncomputable def infinitesimalRingMap {m n : ℕ} (h : m ≤ n) :
    X.infinitesimalRing x n ⟶ X.infinitesimalRing x m :=
  CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.succ_le_succ h)))

lemma infinitesimalRingMap_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (X.infinitesimalRingMap x h) :=
  Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.succ_le_succ h))

@[reassoc (attr := simp)]
lemma toInfinitesimalRing_infinitesimalRingMap {m n : ℕ} (h : m ≤ n) :
    X.toInfinitesimalRing x n ≫ X.infinitesimalRingMap x h = X.toInfinitesimalRing x m := rfl

instance {m n : ℕ} (h : m ≤ n) : IsLocalHom (X.infinitesimalRingMap x h).hom :=
  IsLocalHom.of_surjective _ (X.infinitesimalRingMap_surjective x h)

/-- An element of `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` whose image in `𝒪_{X, x} ⧸ 𝔪_x ^ (m + 1)` is a
unit is itself a unit. -/
lemma isUnit_of_isUnit_infinitesimalRingMap {m n : ℕ} (h : m ≤ n)
    (a : X.infinitesimalRing x n) (ha : IsUnit (X.infinitesimalRingMap x h a)) : IsUnit a :=
  isUnit_of_map_unit (X.infinitesimalRingMap x h).hom a ha

/-- The residue field of `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` is the residue field of `X` at `x`. -/
noncomputable def residueFieldInfinitesimalRingIso (n : ℕ) :
    CommRingCat.of (ResidueField (X.infinitesimalRing x n)) ≅ X.residueField x :=
  (IsLocalRing.residueFieldQuotientMaximalIdealPow n).toCommRingCatIso

@[simp]
lemma infinitesimalRingMap_refl (n : ℕ) : X.infinitesimalRingMap x (le_refl n) = 𝟙 _ := by
  ext y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

@[reassoc (attr := simp)]
lemma infinitesimalRingMap_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    X.infinitesimalRingMap x h₂ ≫ X.infinitesimalRingMap x h₁ =
      X.infinitesimalRingMap x (h₁.trans h₂) := by
  ext y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

/-- The `0`-th infinitesimal ring of `x` is the residue field at `x`. -/
noncomputable def infinitesimalRingIsoResidueField : X.infinitesimalRing x 0 ≅ X.residueField x :=
  (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).toCommRingCatIso

@[reassoc (attr := simp)]
lemma toInfinitesimalRing_infinitesimalRingIsoResidueField_hom :
    X.toInfinitesimalRing x 0 ≫ (X.infinitesimalRingIsoResidueField x).hom = X.residue x := rfl

@[reassoc (attr := simp)]
lemma residue_infinitesimalRingIsoResidueField_inv :
    X.residue x ≫ (X.infinitesimalRingIsoResidueField x).inv = X.toInfinitesimalRing x 0 := by
  rw [← toInfinitesimalRing_infinitesimalRingIsoResidueField_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end Ring

section Neighborhood

/-- The `n`-th infinitesimal neighbourhood `Spec (𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1))` of `x` in `X`. -/
noncomputable abbrev infinitesimalNeighborhood (n : ℕ) : Scheme.{u} :=
  Spec (X.infinitesimalRing x n)

/-- The canonical morphism from the `n`-th infinitesimal neighbourhood of `x` to `X`. -/
noncomputable def fromInfinitesimalNeighborhood (n : ℕ) : X.infinitesimalNeighborhood x n ⟶ X :=
  Spec.map (X.toInfinitesimalRing x n) ≫ X.fromSpecStalk x

lemma fromInfinitesimalNeighborhood_eq (n : ℕ) : X.fromInfinitesimalNeighborhood x n =
    Spec.map (X.toInfinitesimalRing x n) ≫ X.fromSpecStalk x := rfl

/-- For `m ≤ n`, the closed immersion of the `m`-th into the `n`-th infinitesimal
neighbourhood of `x`. -/
noncomputable def infinitesimalNeighborhoodMap {m n : ℕ} (h : m ≤ n) :
    X.infinitesimalNeighborhood x m ⟶ X.infinitesimalNeighborhood x n :=
  Spec.map (X.infinitesimalRingMap x h)

instance {m n : ℕ} (h : m ≤ n) : IsClosedImmersion (X.infinitesimalNeighborhoodMap x h) :=
  IsClosedImmersion.spec_of_surjective _ (X.infinitesimalRingMap_surjective x h)

instance (n : ℕ) : IsPreimmersion (X.fromInfinitesimalNeighborhood x n) := by
  have : IsClosedImmersion (Spec.map (X.toInfinitesimalRing x n)) :=
    IsClosedImmersion.spec_of_surjective _ (X.toInfinitesimalRing_surjective x n)
  exact IsPreimmersion.comp _ _

@[simp]
lemma infinitesimalNeighborhoodMap_refl (n : ℕ) :
    X.infinitesimalNeighborhoodMap x (le_refl n) = 𝟙 _ := by
  rw [infinitesimalNeighborhoodMap, infinitesimalRingMap_refl, Spec.map_id]

@[reassoc (attr := simp)]
lemma infinitesimalNeighborhoodMap_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    X.infinitesimalNeighborhoodMap x h₁ ≫ X.infinitesimalNeighborhoodMap x h₂ =
      X.infinitesimalNeighborhoodMap x (h₁.trans h₂) := by
  rw [infinitesimalNeighborhoodMap, infinitesimalNeighborhoodMap, infinitesimalNeighborhoodMap,
    ← Spec.map_comp, infinitesimalRingMap_comp]

/-- The morphisms `Xₘ ⟶ X` and `Xₙ ⟶ X` are compatible with the transition morphism
`Xₘ ⟶ Xₙ`; in particular `Xₘ ⟶ X` factors through `Xₙ` for `m ≤ n`. -/
@[reassoc (attr := simp)]
lemma infinitesimalNeighborhoodMap_fromInfinitesimalNeighborhood {m n : ℕ} (h : m ≤ n) :
    X.infinitesimalNeighborhoodMap x h ≫ X.fromInfinitesimalNeighborhood x n =
      X.fromInfinitesimalNeighborhood x m := by
  rw [infinitesimalNeighborhoodMap, fromInfinitesimalNeighborhood, fromInfinitesimalNeighborhood,
    ← Category.assoc, ← Spec.map_comp, toInfinitesimalRing_infinitesimalRingMap]

/-- The `0`-th infinitesimal neighbourhood of `x` is `Spec κ(x)`. -/
noncomputable def infinitesimalNeighborhoodIsoSpecResidueField :
    X.infinitesimalNeighborhood x 0 ≅ Spec (X.residueField x) :=
  asIso (Spec.map (X.infinitesimalRingIsoResidueField x).inv)

@[reassoc (attr := simp)]
lemma infinitesimalNeighborhoodIsoSpecResidueField_hom_fromSpecResidueField :
    (X.infinitesimalNeighborhoodIsoSpecResidueField x).hom ≫ X.fromSpecResidueField x =
      X.fromInfinitesimalNeighborhood x 0 := by
  rw [infinitesimalNeighborhoodIsoSpecResidueField, fromSpecResidueField,
    fromInfinitesimalNeighborhood, asIso_hom, ← Category.assoc, ← Spec.map_comp,
    residue_infinitesimalRingIsoResidueField_inv]

/-- A `K`-rational point `Spec K ⟶ X` of a scheme factors through the `0`-th infinitesimal
neighbourhood of its image point. -/
lemma descResidueField_fromInfinitesimalNeighborhood_zero (K : Type u) [Field K]
    (f : Spec (.of K) ⟶ X) :
    Spec.map ((X.infinitesimalRingIsoResidueField (f (closedPoint K))).hom ≫
        X.descResidueField (Scheme.stalkClosedPointTo f)) ≫
      X.fromInfinitesimalNeighborhood (f (closedPoint K)) 0 = f := by
  have h := descResidueField_stalkClosedPointTo_fromSpecResidueField K X f
  rw [fromSpecResidueField] at h
  rw [fromInfinitesimalNeighborhood, ← Spec.map_comp_assoc, ← Category.assoc,
    toInfinitesimalRing_infinitesimalRingIsoResidueField_hom, Spec.map_comp, Category.assoc]
  exact h

end Neighborhood

section Kernel

variable (n : ℕ)

/-- The kernel of the transition map `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 2) ⟶ 𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)`
is the image of `𝔪_x ^ (n + 1)`, that is, `𝔪_x ^ (n + 1) ⧸ 𝔪_x ^ (n + 2)`. -/
lemma ker_infinitesimalRingMap :
    RingHom.ker (X.infinitesimalRingMap x (Nat.le_succ n)).hom =
      (maximalIdeal (X.presheaf.stalk x) ^ (n + 1)).map
        (Ideal.Quotient.mk (maximalIdeal (X.presheaf.stalk x) ^ (n + 1 + 1))) :=
  Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.le_succ n)))

/-- The kernel of `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 2) ⟶ 𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` is square zero. -/
lemma sq_ker_infinitesimalRingMap :
    RingHom.ker (X.infinitesimalRingMap x (Nat.le_succ n)).hom ^ 2 = ⊥ := by
  rw [ker_infinitesimalRingMap]
  exact Ideal.sq_map_pow_eq_bot _ n.succ_ne_zero

/-- The kernel of `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 2) ⟶ 𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` is annihilated by the
maximal ideal. -/
lemma maximalIdeal_mul_ker_infinitesimalRingMap :
    maximalIdeal (X.infinitesimalRing x (n + 1)) *
      RingHom.ker (X.infinitesimalRingMap x (Nat.le_succ n)).hom = ⊥ := by
  have hm : maximalIdeal (X.infinitesimalRing x (n + 1)) =
      (maximalIdeal (X.presheaf.stalk x)).map
        (Ideal.Quotient.mk (maximalIdeal (X.presheaf.stalk x) ^ (n + 1 + 1))) :=
    (IsLocalRing.map_maximalIdeal_quotient_pow (n + 1)).symm
  rw [hm, ker_infinitesimalRingMap]
  exact Ideal.map_mul_map_pow_eq_bot _ (n + 1)

end Kernel

section Finite

variable {k : Type u} [Field k] [Algebra k (X.presheaf.stalk x)]

/-- If `x` is a `k`-rational point of a locally noetherian scheme `X`, then the ring
`𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` of the `n`-th infinitesimal neighbourhood of `x` is a
finite-dimensional `k`-algebra. -/
theorem finite_infinitesimalRing [IsNoetherianRing (X.presheaf.stalk x)]
    (hk : Function.Surjective
      ((IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap k (X.presheaf.stalk x))))
    (n : ℕ) :
    Module.Finite k (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ (n + 1)) :=
  Module.Finite.quotient_maximalIdeal_pow hk (n + 1)

/-- For a `k`-rational point of a locally noetherian scheme, the kernel
`𝔪_x ^ (n + 1) ⧸ 𝔪_x ^ (n + 2)` of the transition map is a finite-dimensional `k`-vector
space. -/
theorem finite_map_maximalIdeal_pow [IsNoetherianRing (X.presheaf.stalk x)]
    (hk : Function.Surjective
      ((IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap k (X.presheaf.stalk x))))
    (n : ℕ) :
    Module.Finite k ((maximalIdeal (X.presheaf.stalk x) ^ (n + 1)).map
      (Ideal.Quotient.mk (maximalIdeal (X.presheaf.stalk x) ^ (n + 1 + 1)))) :=
  Module.Finite.ideal_quotient_maximalIdeal_pow hk (n + 1 + 1) _

end Finite

section Points

variable (X : Scheme.{u}) (x : X) (n : ℕ)

/-- The maximal ideal of `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` is nilpotent. -/
lemma maximalIdeal_infinitesimalRing_pow :
    maximalIdeal (X.infinitesimalRing x n) ^ (n + 1) = ⊥ := by
  have h : maximalIdeal (X.infinitesimalRing x n) =
      (maximalIdeal (X.presheaf.stalk x)).map (Ideal.Quotient.mk _) :=
    (IsLocalRing.map_maximalIdeal_quotient_pow n).symm
  rw [h, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

/-- The `n`-th infinitesimal neighbourhood of `x` has a single point. -/
lemma eq_closedPoint_infinitesimalNeighborhood
    (z : PrimeSpectrum (X.infinitesimalRing x n)) :
    z = closedPoint (X.infinitesimalRing x n) := by
  have hmax : (closedPoint (X.infinitesimalRing x n)).asIdeal =
    maximalIdeal (X.infinitesimalRing x n) := rfl
  refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal z.2.ne_top)
    (Ideal.IsPrime.le_of_pow_le (n := n + 1) ?_))
  rw [hmax, X.maximalIdeal_infinitesimalRing_pow x n]
  exact bot_le

/-- Every point of the `n`-th infinitesimal neighbourhood of `x` maps to `x`. -/
@[simp]
lemma fromInfinitesimalNeighborhood_apply (z : X.infinitesimalNeighborhood x n) :
    X.fromInfinitesimalNeighborhood x n z = x := by
  rw [fromInfinitesimalNeighborhood, Scheme.Hom.comp_apply,
    X.eq_closedPoint_infinitesimalNeighborhood x n z, Spec_closedPoint,
    fromSpecStalk_closedPoint]

/-- The `n`-th infinitesimal neighbourhood of `x` lies over every open neighbourhood of `x`. -/
lemma preimage_fromInfinitesimalNeighborhood_eq_top {U : X.Opens} (hxU : x ∈ U) :
    X.fromInfinitesimalNeighborhood x n ⁻¹ᵁ U = ⊤ := by
  ext z
  simpa using hxU

/-- Pulling a function on an open neighbourhood `U` of `x` back to the `n`-th infinitesimal
neighbourhood of `x` is taking its germ at `x` and reducing modulo `𝔪_x ^ (n + 1)`:

```
                Γ(X, U) ------- germ U x -------> 𝒪_{X, x}
                   |                                  |
                   | (fromInfinitesimalNeighborhood).appLE
                   |                                  | toInfinitesimalRing x n
                   v                                  v
  Γ(Xₙ, ⊤) <--- ΓSpecIso.inv ---- 𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)
```
-/
lemma fromInfinitesimalNeighborhood_appLE {U : X.Opens} (hxU : x ∈ U)
    (h : (⊤ : (X.infinitesimalNeighborhood x n).Opens) ≤
      X.fromInfinitesimalNeighborhood x n ⁻¹ᵁ U) :
    (X.fromInfinitesimalNeighborhood x n).appLE U ⊤ h =
      X.presheaf.germ U x hxU ≫ X.toInfinitesimalRing x n ≫
        (ΓSpecIso (X.infinitesimalRing x n)).inv := by
  rw [Scheme.Hom.appLE_congr_hom (X.fromInfinitesimalNeighborhood_eq x n) U ⊤ h h,
    Scheme.Hom.comp_appLE, fromSpecStalk_app hxU, Category.assoc, Category.assoc,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE_eq_appTop, ← ΓSpecIso_inv_naturality]

end Points

section InfinitesimalBaseChange

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T)

/-- The base change `W ×_T Tₙ` of `f : W ⟶ T` along the `n`-th infinitesimal neighbourhood
of `t`.

This is an `abbrev` on purpose: the two projections below are `Limits.pullback.fst` and
`Limits.pullback.snd`, and the lemmas about them are proved by `Limits.pullback.hom_ext` and
`Limits.pullback.condition`, all of which need the pullback to be visible. -/
noncomputable abbrev infinitesimalBaseChange (n : ℕ) : Scheme.{u} :=
  Limits.pullback f (T.fromInfinitesimalNeighborhood t n)

/-- The projection `W ×_T Tₙ ⟶ W`. -/
noncomputable abbrev infinitesimalBaseChangeFst (n : ℕ) : infinitesimalBaseChange f t n ⟶ W :=
  Limits.pullback.fst _ _

/-- The projection `W ×_T Tₙ ⟶ Tₙ`. -/
noncomputable abbrev infinitesimalBaseChangeSnd (n : ℕ) :
    infinitesimalBaseChange f t n ⟶ T.infinitesimalNeighborhood t n :=
  Limits.pullback.snd _ _

/-- For `m ≤ n`, the morphism `W ×_T Tₘ ⟶ W ×_T Tₙ` induced by `Tₘ ⟶ Tₙ`. -/
noncomputable def infinitesimalBaseChangeMap {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChange f t m ⟶ infinitesimalBaseChange f t n :=
  Limits.pullback.map _ _ _ _ (𝟙 W) (T.infinitesimalNeighborhoodMap t h) (𝟙 T) (by simp) (by simp)

/-- The transition morphism commutes with the projections to `W`:

```
  W ×_T Tₘ ---- infinitesimalBaseChangeMap f t h ----> W ×_T Tₙ
           ╲                                         ╱
            ╲  infinitesimalBaseChangeFst f t m     ╱  infinitesimalBaseChangeFst f t n
             ╲                                     ╱
              ────────────────>  W  <─────────────
```
-/
@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMap_fst {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChangeMap f t h ≫ infinitesimalBaseChangeFst f t n =
      infinitesimalBaseChangeFst f t m := by
  simp [infinitesimalBaseChangeMap]

/-- The transition morphism commutes with the projections to the infinitesimal
neighbourhoods:

```
  W ×_T Tₘ ---- infinitesimalBaseChangeMap f t h ----> W ×_T Tₙ
      |                                                   |
      | infinitesimalBaseChangeSnd f t m                  | infinitesimalBaseChangeSnd f t n
      v                                                   v
     Tₘ -------- infinitesimalNeighborhoodMap t h ------> Tₙ
```
-/
@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMap_snd {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChangeMap f t h ≫ infinitesimalBaseChangeSnd f t n =
      infinitesimalBaseChangeSnd f t m ≫ T.infinitesimalNeighborhoodMap t h := by
  simp [infinitesimalBaseChangeMap]

@[simp]
lemma infinitesimalBaseChangeMap_refl (n : ℕ) :
    infinitesimalBaseChangeMap f t (le_refl n) = 𝟙 _ := by
  apply Limits.pullback.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMap_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    infinitesimalBaseChangeMap f t h₁ ≫ infinitesimalBaseChangeMap f t h₂ =
      infinitesimalBaseChangeMap f t (h₁.trans h₂) := by
  apply Limits.pullback.hom_ext <;>
    simp [T.infinitesimalNeighborhoodMap_comp t h₁ h₂]

/-- Every point of `W ×_T Tₙ` lies over `t`. -/
lemma apply_infinitesimalBaseChangeFst (n : ℕ) (w : infinitesimalBaseChange f t n) :
    f (infinitesimalBaseChangeFst f t n w) = t := by
  rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply,
    T.fromInfinitesimalNeighborhood_apply]

/-- `W ×_T Tₙ` lies over any open neighbourhood of `t`. -/
lemma preimage_infinitesimalBaseChangeFst_eq_top (n : ℕ) {U : T.Opens} (hU : t ∈ U) :
    infinitesimalBaseChangeFst f t n ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := by
  ext w
  simpa [apply_infinitesimalBaseChangeFst f t n w] using hU

/-- The ring homomorphism `𝒪_{T, t} ⟶ Γ(W ×_T Tₙ, 𝒪)`, through which `𝒪_{T, t}` acts on the
sections of a sheaf on `W ×_T Tₙ`. -/
noncomputable def toInfinitesimalBaseChangeΓ (n : ℕ) :
    T.presheaf.stalk t ⟶ Γ(infinitesimalBaseChange f t n, ⊤) :=
  T.toInfinitesimalRing t n ≫ (Scheme.ΓSpecIso _).inv ≫ (infinitesimalBaseChangeSnd f t n).appTop

/-- The action of `𝒪_{T, t}` on the sections over `W ×_T Tₙ` is compatible with the transition
morphisms:

```
                toInfinitesimalBaseChangeΓ f t n
  𝒪_{T, t} ---------------------------------------> Γ(W ×_T Tₙ, 𝒪)
          ╲                                                 |
           ╲  toInfinitesimalBaseChangeΓ f t m              | appTop of
            ╲                                               | infinitesimalBaseChangeMap f t h
             ╲                                              v
              ─────────────────────────────────> Γ(W ×_T Tₘ, 𝒪)
```
-/
@[reassoc (attr := simp)]
lemma toInfinitesimalBaseChangeΓ_comp_appTop {m n : ℕ} (h : m ≤ n) :
    toInfinitesimalBaseChangeΓ f t n ≫ (infinitesimalBaseChangeMap f t h).appTop =
      toInfinitesimalBaseChangeΓ f t m := by
  rw [toInfinitesimalBaseChangeΓ, toInfinitesimalBaseChangeΓ, Category.assoc, Category.assoc,
    ← Scheme.Hom.comp_appTop, infinitesimalBaseChangeMap_snd, Scheme.Hom.comp_appTop,
    ← Category.assoc ((Scheme.ΓSpecIso _).inv), Scheme.infinitesimalNeighborhoodMap,
    ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, ← Category.assoc,
    Scheme.toInfinitesimalRing_infinitesimalRingMap, Category.assoc]

/-- Pulling a function on an open neighbourhood `U` of `t` back to `W ×_T Tₙ` is taking its
germ at `t` and mapping it by `𝒪_{T, t} ⟶ Γ(W ×_T Tₙ, 𝒪)`:

```
  Γ(T, U) ------------- germ U t -------------> 𝒪_{T, t}
        ╲                                            |
         ╲ (infinitesimalBaseChangeFst f t n ≫ f).appLE U ⊤
          ╲                                          | toInfinitesimalBaseChangeΓ f t n
           ╲                                         v
            ──────────────────────────────> Γ(W ×_T Tₙ, 𝒪)
```
-/
lemma infinitesimalBaseChangeFst_comp_appLE (n : ℕ) {U : T.Opens} (hU : t ∈ U)
    (h : (⊤ : (infinitesimalBaseChange f t n).Opens) ≤
      (infinitesimalBaseChangeFst f t n ≫ f) ⁻¹ᵁ U) :
    (infinitesimalBaseChangeFst f t n ≫ f).appLE U ⊤ h =
      T.presheaf.germ U t hU ≫ toInfinitesimalBaseChangeΓ f t n := by
  rw [Scheme.Hom.appLE_congr_hom (Limits.pullback.condition
      (f := f) (g := T.fromInfinitesimalNeighborhood t n)) U ⊤ h
      (by simp [T.preimage_fromInfinitesimalNeighborhood_eq_top t n hU]),
    ← Scheme.Hom.appLE_comp_appLE (infinitesimalBaseChangeSnd f t n)
      (T.fromInfinitesimalNeighborhood t n) U ⊤ ⊤
      (T.preimage_fromInfinitesimalNeighborhood_eq_top t n hU).ge (by simp),
    T.fromInfinitesimalNeighborhood_appLE t n hU, Scheme.Hom.appLE_eq_appTop,
    toInfinitesimalBaseChangeΓ, Category.assoc, Category.assoc]

/-- An element of `𝔪_t ^ (n + 1)` acts as zero on `Γ(W ×_T Tₙ, 𝒪)`, because the action of
`𝒪_{T, t}` factors through `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)`. -/
lemma toInfinitesimalBaseChangeΓ_eq_zero (n : ℕ) {r : T.presheaf.stalk t}
    (hr : r ∈ maximalIdeal (T.presheaf.stalk t) ^ (n + 1)) :
    toInfinitesimalBaseChangeΓ f t n r = 0 := by
  have h0 : T.toInfinitesimalRing t n r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [toInfinitesimalBaseChangeΓ, CommRingCat.comp_apply, h0, map_zero]

end InfinitesimalBaseChange

end AlgebraicGeometry.Scheme
