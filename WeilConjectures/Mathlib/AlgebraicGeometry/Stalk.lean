/-
Copyright (c) 2026 The Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Infinitesimal neighbourhoods of a point of a scheme

For a scheme `X` and a point `x : X` we define the `n`-th infinitesimal neighbourhood
`Xₙ = Spec (𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1))` of `x` in `X`, together with its canonical morphism to `X`.

## Main definitions

- `AlgebraicGeometry.Scheme.infinitesimalRing X x n`: the ring `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)`.
- `AlgebraicGeometry.Scheme.infinitesimalNeighborhood X x n`: the scheme
  `Spec (𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1))`.
- `AlgebraicGeometry.Scheme.fromInfinitesimalNeighborhood X x n`: the canonical morphism
  `Xₙ ⟶ X`.
- `AlgebraicGeometry.Scheme.infinitesimalNeighborhoodMap X x h`: for `m ≤ n`, the closed
  immersion `Xₘ ⟶ Xₙ`, compatible with the morphisms to `X`.

## Main results

- `AlgebraicGeometry.Scheme.infinitesimalNeighborhoodIsoSpecResidueField`: `X₀ ≅ Spec κ(x)`,
  and `AlgebraicGeometry.Scheme.descResidueField_fromInfinitesimalNeighborhood_zero`, which says
  that a `K`-rational point `Spec K ⟶ X` factors through `X₀ ⟶ X`.
- `AlgebraicGeometry.Scheme.finite_infinitesimalRing`: for a `k`-rational point of a locally
  noetherian scheme, `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` is a finite-dimensional `k`-algebra.
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

end Points

end AlgebraicGeometry.Scheme
