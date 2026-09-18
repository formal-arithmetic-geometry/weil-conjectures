/-
Copyright (c) 2026 The Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Zero

/-!
# Infinitesimal neighbourhoods of a point of a scheme

For a scheme `X` and a point `x : X` we define the `n`-th infinitesimal neighbourhood
`Xₙ = Spec (𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1))` of `x` in `X`, together with its canonical morphism to `X`.

A preliminary section records the stalk of `Spec R` at the closed point of a local ring `R`.
The last sections base change a morphism `f : W ⟶ T` along `Tₙ ⟶ T` for a point `t` of `T`.

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
  `𝒪_{T, t} ⟶ Γ(W ×_T Tₙ, 𝒪)`, and `AlgebraicGeometry.Scheme.infinitesimalRingToΓ`, the ring
  map `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1) ⟶ Γ(W ×_T Tₙ, 𝒪)` it factors through.
- `AlgebraicGeometry.Scheme.infinitesimalBaseChangeZeroIsoFiber`: the identification
  `W ×_T T₀ ≅ W_t` of the zeroth infinitesimal base change with the scheme-theoretic fibre.
- `AlgebraicGeometry.Scheme.infinitesimalRingToStalk`: the ring homomorphism
  `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1) ⟶ 𝒪_{W ×_T Tₙ, x}` through which `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)` acts
  on a stalk of `W ×_T Tₙ`.

## Main results

- `AlgebraicGeometry.Scheme.infinitesimalNeighborhoodIsoSpecResidueField`: `X₀ ≅ Spec κ(x)`,
  and `AlgebraicGeometry.Scheme.descResidueField_fromInfinitesimalNeighborhood_zero`, which says
  that a `K`-rational point `Spec K ⟶ X` factors through `X₀ ⟶ X`.
- `AlgebraicGeometry.Scheme.fromInfinitesimalNeighborhood_zero_comp_of_comp_eq_id`: if
  `f : Spec K ⟶ X` is a section of `π : X ⟶ Spec K` and `x` is the point it picks out, then
  `X₀ ⟶ X` is unchanged by composing with `X ⟶ Spec K ⟶ X`.
- `AlgebraicGeometry.Scheme.finite_infinitesimalRing`: for a `k`-rational point of a locally
  noetherian scheme, `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` is a finite-dimensional `k`-algebra.
- `AlgebraicGeometry.Scheme.preimage_infinitesimalBaseChangeFst_eq_top`: every point of
  `W ×_T Tₙ` lies over `t`, so `W ×_T Tₙ` lies over every open neighbourhood of `t`.
- `AlgebraicGeometry.Scheme.thickeningIdeal`: the ideal sheaf cutting out the closed immersion
  `W ×_T Tₙ ↪ W ×_T T_{n+1}`, and
  `AlgebraicGeometry.Scheme.infinitesimalBaseChangeMapZero`: the closed immersion
  `W ×_T T₀ ↪ W ×_T T_{n+1}` of the zeroth infinitesimal neighbourhood.
- `AlgebraicGeometry.Scheme.mul_ker_infinitesimalBaseChangeMap`: the kernel ideal sheaves of
  `W ×_T T_{m₁} ↪ W ×_T Tₙ` and `W ×_T T_{m₂} ↪ W ×_T Tₙ` annihilate each other as soon as
  `n ≤ m₁ + m₂ + 1`; `AlgebraicGeometry.Scheme.sq_thickeningIdeal` and
  `AlgebraicGeometry.Scheme.ker_mul_thickeningIdeal_eq_zero`, which says that the thickening
  ideal is annihilated by the kernel ideal sheaf of `W ×_T T₀ ↪ W ×_T T_{n+1}`, are the two
  cases of it that are used.
- `AlgebraicGeometry.Scheme.surjective_appTop_infinitesimalBaseChangeMap` and
  `AlgebraicGeometry.Scheme.exists_isUnit_appTop_infinitesimalBaseChangeMap`: if the global
  sections of `W ×_T Tₘ` are `𝒪_{T, t} ⧸ 𝔪_t ^ (m + 1)`, then every function on `W ×_T Tₘ`,
  and every unit of `Γ(W ×_T Tₘ, 𝒪)` as a unit, extends to `W ×_T Tₙ` for `m ≤ n`;
  `AlgebraicGeometry.Scheme.nontrivial_infinitesimalBaseChangeΓ` says that `Γ(W ×_T Tₙ, 𝒪)` is
  then non-trivial.
- `AlgebraicGeometry.Scheme.infinitesimalBaseChangeMapOver`: the base change
  `W' ×_T Tₙ ⟶ W ×_T Tₙ` of a morphism `W' ⟶ W` over `T`, and
  `AlgebraicGeometry.Scheme.comap_thickeningIdeal_le`, which says that it pulls the thickening
  ideal of `W` into the thickening ideal of `W'`.
- `AlgebraicGeometry.ΓSpecIso_inv_comp_germ_closedPoint`: for a local ring `R`, the composite
  `R ⟶ Γ(Spec R, 𝒪) ⟶ 𝒪_{Spec R, 𝔪}` is the inverse of
  `AlgebraicGeometry.stalkClosedPointIso`;
  `AlgebraicGeometry.flat_ΓSpecIso_inv_comp_appTop_comp_germ` says that the corresponding map
  `R ⟶ 𝒪_{X, x}` is flat for a flat morphism `X ⟶ Spec R` and a point `x` over `𝔪`.
- the `AlgebraicGeometry.Surjective` instance on
  `AlgebraicGeometry.Scheme.infinitesimalBaseChangeMap`: for `m ≤ n` the transition morphism
  `W ×_T Tₘ ⟶ W ×_T Tₙ` is surjective.
- `AlgebraicGeometry.Scheme.flat_infinitesimalRingToStalk`: the stalks of `W ×_T Tₙ` are flat
  over `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)` when `f` is flat.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

section SpecLocalRing

/-! ### Stalks of a scheme over the spectrum of a local ring -/

variable (R : CommRingCat.{u}) [IsLocalRing R] {X : Scheme.{u}}

/-- **The stalk of `Spec R` at the closed point of a local ring `R` is `R`**: the composite

```
  R ---- ΓSpecIso.inv ----> Γ(Spec R, 𝒪) ---- germ ⊤ 𝔪 ----> 𝒪_{Spec R, 𝔪}
```

is the inverse of `AlgebraicGeometry.stalkClosedPointIso`. -/
lemma ΓSpecIso_inv_comp_germ_closedPoint :
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (closedPoint R) trivial =
      (stalkClosedPointIso R).inv := by
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable {R}

/-- The composite `R ⟶ Γ(Spec R, 𝒪) ⟶ 𝒪_{Spec R, y}` is an isomorphism for a point `y` of
`Spec R` that is the closed point of the local ring `R`. -/
lemma isIso_ΓSpecIso_inv_comp_germ_of_eq_closedPoint (y : Spec R) (hy : y = closedPoint R) :
    IsIso ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ y trivial) := by
  subst hy
  rw [ΓSpecIso_inv_comp_germ_closedPoint]
  infer_instance

omit [IsLocalRing R] in
/-- For a morphism `g : X ⟶ Spec R` and a point `x` of `X`, the ring homomorphism
`R ⟶ 𝒪_{X, x}` obtained by taking global sections and then the germ at `x` is the stalk map of
`g` at `x`, precomposed with the germ at the image of `x`:

```
                 ΓSpecIso.inv                 g.appTop            germ ⊤ x
              R ──────────────▶ Γ(Spec R, 𝒪) ──────────▶ Γ(X, 𝒪) ──────────▶ 𝒪_{X, x}
                                     │                                          ▲
                                     │ germ ⊤ (g.base x)           g.stalkMap x │
                                     └────────────▶ 𝒪_{Spec R, g.base x} ───────┘
```
-/
lemma ΓSpecIso_inv_comp_appTop_comp_germ (g : X ⟶ Spec R) (x : X) :
    (Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ x trivial =
      ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (g.base x) trivial) ≫ g.stalkMap x := by
  rw [Category.assoc, Scheme.Hom.germ_stalkMap g ⊤ x trivial]
  rfl

/-- **The ring homomorphism `R ⟶ 𝒪_{X, x}` induced by a flat morphism `g : X ⟶ Spec R` to the
spectrum of a local ring is flat**, at a point `x` lying over the closed point: it is the stalk
map of `g`, which is flat, composed with an isomorphism. -/
lemma flat_ΓSpecIso_inv_comp_appTop_comp_germ (g : X ⟶ Spec R) [Flat g] (x : X)
    (hx : g.base x = closedPoint R) :
    ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.Flat := by
  have : IsIso ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (g.base x) trivial) :=
    isIso_ΓSpecIso_inv_comp_germ_of_eq_closedPoint _ hx
  rw [ΓSpecIso_inv_comp_appTop_comp_germ, CommRingCat.hom_comp]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
    (Flat.stalkMap _ x)

end SpecLocalRing

namespace Scheme

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

/-- **A rational point is fixed by the retraction it defines on the zeroth infinitesimal
neighbourhood.** Let `π : X ⟶ Spec K` be a morphism to the spectrum of a field and let
`f : Spec K ⟶ X` be a section of it, cutting out the point `x`. Then composing `X₀ ⟶ X` with
`X ⟶ Spec K ⟶ X` changes nothing, because `X₀ ≅ Spec κ(x)` and `f` identifies `κ(x)` with `K`.

This is the form in which "`x` is the point `f` picks out" is used in the theorem of the
cube. -/
lemma fromInfinitesimalNeighborhood_zero_comp_of_comp_eq_id (K : Type u) [Field K]
    (π : X ⟶ Spec (.of K)) (f : Spec (.of K) ⟶ X) (hf : f ≫ π = 𝟙 _) :
    X.fromInfinitesimalNeighborhood (f (closedPoint K)) 0 ≫ π ≫ f =
      X.fromInfinitesimalNeighborhood (f (closedPoint K)) 0 := by
  set y := f (closedPoint K) with hydef
  set ι := X.fromInfinitesimalNeighborhood y 0 with hιdef
  set ψ : X.infinitesimalRing y 0 ⟶ .of K :=
    (X.infinitesimalRingIsoResidueField y).hom ≫
      X.descResidueField (Scheme.stalkClosedPointTo f) with hψdef
  have hs : Spec.map ψ ≫ ι = f := descResidueField_fromInfinitesimalNeighborhood_zero X K f
  have hsg : Spec.map ψ ≫ ι ≫ π = 𝟙 _ := by rw [← Category.assoc, hs, hf]
  -- `ψ` is injective, being a ring homomorphism out of a field
  have hinj : Function.Injective ψ.hom := by
    rw [hψdef, CommRingCat.hom_comp]
    exact (X.descResidueField (Scheme.stalkClosedPointTo f)).hom.injective.comp
      ((ConcreteCategory.bijective_of_isIso (X.infinitesimalRingIsoResidueField y).hom).1)
  -- `ψ` is surjective, because `Spec ψ` has a retraction
  have hΓ : (ΓSpecIso (X.infinitesimalRing y 0)).inv ≫ (Spec.map ψ).appTop ≫
      (ΓSpecIso (CommRingCat.of K)).hom = ψ := by
    rw [ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hsurj : Function.Surjective ψ.hom := by
    have h1 : Function.Surjective (Spec.map ψ).appTop.hom := fun y ↦
      ⟨(ι ≫ π).appTop y, by
        simpa using ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hsg) y⟩
    intro a
    obtain ⟨z, hz⟩ := h1 ((ΓSpecIso (CommRingCat.of K)).inv a)
    refine ⟨(ΓSpecIso (X.infinitesimalRing y 0)).hom z, ?_⟩
    have h2 := ConcreteCategory.congr_hom hΓ ((ΓSpecIso (X.infinitesimalRing y 0)).hom z)
    simp only [ConcreteCategory.comp_apply] at h2
    rw [← h2]
    simp [hz]
  have : IsIso ψ := (ConcreteCategory.isIso_iff_bijective ψ).mpr ⟨hinj, hsurj⟩
  have hg : ι ≫ π = inv (Spec.map ψ) := by
    rw [← Category.id_comp (ι ≫ π), ← IsIso.inv_hom_id (Spec.map ψ), Category.assoc, hsg,
      Category.comp_id]
  calc ι ≫ π ≫ f = (ι ≫ π) ≫ f := (Category.assoc _ _ _).symm
    _ = inv (Spec.map ψ) ≫ Spec.map ψ ≫ ι := by rw [hg, hs]
    _ = ι := by rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end Neighborhood

section Kernel

/-- The kernel of the transition map `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1) ⟶ 𝒪_{X, x} ⧸ 𝔪_x ^ (m + 1)`
is the image of `𝔪_x ^ (m + 1)`, that is, `𝔪_x ^ (m + 1) ⧸ 𝔪_x ^ (n + 1)`. -/
lemma ker_infinitesimalRingMap {m n : ℕ} (h : m ≤ n) :
    RingHom.ker (X.infinitesimalRingMap x h).hom =
      (maximalIdeal (X.presheaf.stalk x) ^ (m + 1)).map
        (Ideal.Quotient.mk (maximalIdeal (X.presheaf.stalk x) ^ (n + 1))) :=
  Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.succ_le_succ h))

/-- The kernel of the transition map `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1) ⟶ 𝒪_{X, x} ⧸ 𝔪_x` down to the
zeroth infinitesimal neighbourhood is the maximal ideal of `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)`. -/
lemma ker_infinitesimalRingMap_zero_eq_maximalIdeal (n : ℕ) :
    RingHom.ker (X.infinitesimalRingMap x (Nat.zero_le n)).hom =
      maximalIdeal (X.infinitesimalRing x n) := by
  rw [ker_infinitesimalRingMap, zero_add, pow_one]
  exact IsLocalRing.map_maximalIdeal_quotient_pow n

/-- **The kernels of two transition maps out of `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` annihilate each
other** as soon as the two neighbourhoods they go down to are large enough, namely
`n ≤ m₁ + m₂ + 1`: the kernels are the images of `𝔪_x ^ (m₁ + 1)` and `𝔪_x ^ (m₂ + 1)`, whose
product lands in `𝔪_x ^ (n + 1)`. -/
lemma mul_ker_infinitesimalRingMap {m₁ m₂ n : ℕ} (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n)
    (h : n ≤ m₁ + m₂ + 1) :
    RingHom.ker (X.infinitesimalRingMap x h₁).hom *
      RingHom.ker (X.infinitesimalRingMap x h₂).hom = ⊥ := by
  rw [ker_infinitesimalRingMap, ker_infinitesimalRingMap]
  exact Ideal.map_pow_mul_map_pow_eq_bot _ (by omega)

/-- The kernel of `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 2) ⟶ 𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` is square zero. -/
lemma sq_ker_infinitesimalRingMap (n : ℕ) :
    RingHom.ker (X.infinitesimalRingMap x (Nat.le_succ n)).hom ^ 2 = ⊥ := by
  rw [sq]
  exact X.mul_ker_infinitesimalRingMap x (Nat.le_succ n) (Nat.le_succ n) (by omega)

/-- The kernel of `𝒪_{X, x} ⧸ 𝔪_x ^ (n + 2) ⟶ 𝒪_{X, x} ⧸ 𝔪_x ^ (n + 1)` is annihilated by the
maximal ideal. -/
lemma maximalIdeal_mul_ker_infinitesimalRingMap (n : ℕ) :
    maximalIdeal (X.infinitesimalRing x (n + 1)) *
      RingHom.ker (X.infinitesimalRingMap x (Nat.le_succ n)).hom = ⊥ := by
  rw [← X.ker_infinitesimalRingMap_zero_eq_maximalIdeal x (n + 1)]
  exact X.mul_ker_infinitesimalRingMap x (Nat.zero_le (n + 1)) (Nat.le_succ n) (by omega)

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

instance : Ring.KrullDimLE 0 (X.infinitesimalRing x n) :=
  .of_isNilpotent_maximalIdeal ⟨n + 1, by simp [X.maximalIdeal_infinitesimalRing_pow x n]⟩

/-- The `n`-th infinitesimal neighbourhood of `x` has a single point. -/
lemma eq_closedPoint_infinitesimalNeighborhood
    (z : PrimeSpectrum (X.infinitesimalRing x n)) :
    z = closedPoint (X.infinitesimalRing x n) :=
  Subsingleton.elim _ _

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

section Singleton

/-! ### The infinitesimal neighbourhoods are one-point schemes -/

noncomputable instance (n : ℕ) : Unique (X.infinitesimalNeighborhood x n) :=
  inferInstanceAs (Unique (PrimeSpectrum (X.infinitesimalRing x n)))

end Singleton

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

/-- The ring homomorphism `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1) ⟶ Γ(W ×_T Tₙ, 𝒪)` induced by the
projection `W ×_T Tₙ ⟶ Tₙ`, through which `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)` acts on the sections of a
sheaf on `W ×_T Tₙ`. -/
noncomputable def infinitesimalRingToΓ (n : ℕ) :
    T.infinitesimalRing t n ⟶ Γ(infinitesimalBaseChange f t n, ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (infinitesimalBaseChangeSnd f t n).appTop

/-- The action of `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)` on the sections over `W ×_T Tₙ` is compatible with
the transition morphisms:

```
                    infinitesimalRingToΓ f t n
  𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1) ──────────────────────▶ Γ(W ×_T Tₙ, 𝒪)
             │                                             │
             │ infinitesimalRingMap t h                    │ appTop of
             │                                             │ infinitesimalBaseChangeMap f t h
             ▼                                             ▼
  𝒪_{T, t} ⧸ 𝔪_t ^ (m + 1) ──────────────────────▶ Γ(W ×_T Tₘ, 𝒪)
                    infinitesimalRingToΓ f t m
```
-/
@[reassoc (attr := simp)]
lemma infinitesimalRingToΓ_comp_appTop {m n : ℕ} (h : m ≤ n) :
    infinitesimalRingToΓ f t n ≫ (infinitesimalBaseChangeMap f t h).appTop =
      T.infinitesimalRingMap t h ≫ infinitesimalRingToΓ f t m := by
  rw [infinitesimalRingToΓ, infinitesimalRingToΓ, Category.assoc,
    ← Scheme.Hom.comp_appTop, infinitesimalBaseChangeMap_snd, Scheme.Hom.comp_appTop,
    ← Category.assoc, Scheme.infinitesimalNeighborhoodMap, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]

/-- The ring homomorphism `𝒪_{T, t} ⟶ Γ(W ×_T Tₙ, 𝒪)`, through which `𝒪_{T, t}` acts on the
sections of a sheaf on `W ×_T Tₙ`: the quotient map to `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)` followed by
`AlgebraicGeometry.Scheme.infinitesimalRingToΓ`. -/
noncomputable def toInfinitesimalBaseChangeΓ (n : ℕ) :
    T.presheaf.stalk t ⟶ Γ(infinitesimalBaseChange f t n, ⊤) :=
  T.toInfinitesimalRing t n ≫ infinitesimalRingToΓ f t n

/-- The action of `𝒪_{T, t}` on the sections over `W ×_T Tₙ` factors through the quotient
`𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)`:

```
  𝒪_{T, t} ──────── toInfinitesimalRing t n ───────▶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)
          ╲                                                   │
           ╲  toInfinitesimalBaseChangeΓ f t n                │ infinitesimalRingToΓ f t n
            ╲                                                 ▼
             ──────────────────────────────────▶ Γ(W ×_T Tₙ, 𝒪)
```
-/
@[reassoc]
lemma toInfinitesimalRing_comp_infinitesimalRingToΓ (n : ℕ) :
    T.toInfinitesimalRing t n ≫ infinitesimalRingToΓ f t n =
      toInfinitesimalBaseChangeΓ f t n := rfl

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
  rw [← toInfinitesimalRing_comp_infinitesimalRingToΓ, Category.assoc,
    infinitesimalRingToΓ_comp_appTop, ← Category.assoc,
    Scheme.toInfinitesimalRing_infinitesimalRingMap,
    toInfinitesimalRing_comp_infinitesimalRingToΓ]

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
    toInfinitesimalBaseChangeΓ, infinitesimalRingToΓ, Category.assoc, Category.assoc]

/-- An element of `𝔪_t ^ (n + 1)` acts as zero on `Γ(W ×_T Tₙ, 𝒪)`, because the action of
`𝒪_{T, t}` factors through `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)`. -/
lemma toInfinitesimalBaseChangeΓ_eq_zero (n : ℕ) {r : T.presheaf.stalk t}
    (hr : r ∈ maximalIdeal (T.presheaf.stalk t) ^ (n + 1)) :
    toInfinitesimalBaseChangeΓ f t n r = 0 := by
  have h0 : T.toInfinitesimalRing t n r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [toInfinitesimalBaseChangeΓ, CommRingCat.comp_apply, h0, map_zero]

/-- **Functions lift along the infinitesimal base changes.** If the global sections of
`W ×_T Tₘ` are the ring `𝒪_{T, t} ⧸ 𝔪_t ^ (m + 1)`, then for `m ≤ n` every function on
`W ×_T Tₘ` is the restriction of a function on `W ×_T Tₙ`, because
`𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1) ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (m + 1)` is surjective. -/
lemma surjective_appTop_infinitesimalBaseChangeMap {m n : ℕ} (h : m ≤ n)
    (hm : Function.Surjective (infinitesimalRingToΓ f t m)) :
    Function.Surjective (infinitesimalBaseChangeMap f t h).appTop := by
  intro y
  obtain ⟨b, rfl⟩ := hm y
  obtain ⟨c, rfl⟩ := T.infinitesimalRingMap_surjective t h b
  refine ⟨infinitesimalRingToΓ f t n c, ?_⟩
  rw [← CommRingCat.comp_apply, infinitesimalRingToΓ_comp_appTop, CommRingCat.comp_apply]

/-- **The sections over an infinitesimal base change form a non-trivial ring**, as soon as they
are the ring `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)` of the `n`-th infinitesimal neighbourhood: the latter is
a local ring, hence non-trivial. Geometrically this says that `W ×_T Tₙ` is non-empty. -/
lemma nontrivial_infinitesimalBaseChangeΓ (n : ℕ) (hn : IsIso (infinitesimalRingToΓ f t n)) :
    Nontrivial Γ(infinitesimalBaseChange f t n, ⊤) :=
  (asIso (infinitesimalRingToΓ f t n)).commRingCatIsoToRingEquiv.toEquiv.symm.nontrivial

/-- **Units lift along the infinitesimal base changes.**

If the global sections of `W ×_T Tₘ` are the ring `𝒪_{T, t} ⧸ 𝔪_t ^ (m + 1)` of the `m`-th
infinitesimal neighbourhood, then for `m ≤ n` every unit of `Γ(W ×_T Tₘ, 𝒪)` is the restriction
of a unit of `Γ(W ×_T Tₙ, 𝒪)`: a unit of `𝒪_{T, t} ⧸ 𝔪_t ^ (m + 1)` lifts to a unit of
`𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)`, the latter being a local ring. -/
lemma exists_isUnit_appTop_infinitesimalBaseChangeMap {m n : ℕ} (h : m ≤ n)
    (hm : IsIso (infinitesimalRingToΓ f t m))
    {a : Γ(infinitesimalBaseChange f t m, ⊤)} (ha : IsUnit a) :
    ∃ b : Γ(infinitesimalBaseChange f t n, ⊤), IsUnit b ∧
      (infinitesimalBaseChangeMap f t h).appTop b = a := by
  let e := (asIso (infinitesimalRingToΓ f t m)).commRingCatIsoToRingEquiv
  have ha₀ : IsUnit (e.symm a) := ha.map e.symm
  obtain ⟨c, hc⟩ := T.infinitesimalRingMap_surjective t h (e.symm a)
  have hcu : IsUnit c := T.isUnit_of_isUnit_infinitesimalRingMap t h c (hc ▸ ha₀)
  refine ⟨infinitesimalRingToΓ f t n c, hcu.map (infinitesimalRingToΓ f t n).hom, ?_⟩
  rw [← CommRingCat.comp_apply, infinitesimalRingToΓ_comp_appTop, CommRingCat.comp_apply, hc]
  exact e.apply_symm_apply a

/-- **The zeroth infinitesimal base change is the scheme-theoretic fibre.** The zeroth
infinitesimal neighbourhood of `t` is `Spec κ(t)`, so the map of pullback squares

```
  W ×_T T₀ ────────▶ T₀ = Spec (𝒪_{T, t} ⧸ 𝔪_t)
      │   ╲              │   ╲
      │    ╲             │    ╲ infinitesimalNeighborhoodIsoSpecResidueField t
      │     ▼            │     ▼
      │    W_t ─────────────▶ Spec κ(t)
      ▼     │            ▼     │
      W ════╪══════════▶ T ════╪═════▶ T
       ╲    ▼             ╲    ▼
        ──▶ W ─────────────────────▶ T
```

induced by the identity of `W`, the identity of `T` and that isomorphism is an isomorphism
`W ×_T T₀ ≅ W_t`. -/
noncomputable def infinitesimalBaseChangeZeroIsoFiber :
    infinitesimalBaseChange f t 0 ≅ f.fiber t :=
  asIso (Limits.pullback.map f (T.fromInfinitesimalNeighborhood t 0) f
    (T.fromSpecResidueField t) (𝟙 W) (T.infinitesimalNeighborhoodIsoSpecResidueField t).hom
    (𝟙 T) (by simp) (by simp))

/-- The isomorphism `W ×_T T₀ ≅ W_t` commutes with the two projections to `W`:

```
                  infinitesimalBaseChangeZeroIsoFiber f t
  W ×_T T₀ ----------------------------------------------------> W_t
           ╲                                                      |
            ╲  infinitesimalBaseChangeFst f t 0                   | f.fiberι t
             ╲                                                    v
              ──────────────────────────────────────────────────> W
```
-/
@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeZeroIsoFiber_hom_fiberι :
    (infinitesimalBaseChangeZeroIsoFiber f t).hom ≫ f.fiberι t =
      infinitesimalBaseChangeFst f t 0 := by
  simp [infinitesimalBaseChangeZeroIsoFiber, Scheme.Hom.fiberι]

end InfinitesimalBaseChange

section Thickening

open Limits

/-! ### The square-zero thickenings of an infinitesimal base change -/

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T)

/-- **The transition squares of the infinitesimal base change are cartesian**: `W ×_T Tₘ` is
the base change of `Tₘ ⟶ Tₙ` along `W ×_T Tₙ ⟶ Tₙ`.

```
  W ×_T Tₘ ──infinitesimalBaseChangeMap──▶ W ×_T Tₙ
      │                                        │
      │ pr₂                                    │ pr₂
      ▼                                        ▼
     Tₘ ───infinitesimalNeighborhoodMap──────▶ Tₙ
```
-/
lemma isPullback_infinitesimalBaseChangeMap {m n : ℕ} (h : m ≤ n) :
    IsPullback (infinitesimalBaseChangeMap f t h) (infinitesimalBaseChangeSnd f t m)
      (infinitesimalBaseChangeSnd f t n) (T.infinitesimalNeighborhoodMap t h) := by
  refine IsPullback.of_right ?_ (infinitesimalBaseChangeMap_snd f t h)
    (IsPullback.of_hasPullback f (T.fromInfinitesimalNeighborhood t n))
  rw [infinitesimalBaseChangeMap_fst,
    T.infinitesimalNeighborhoodMap_fromInfinitesimalNeighborhood t h]
  exact IsPullback.of_hasPullback f (T.fromInfinitesimalNeighborhood t m)

instance {m n : ℕ} (h : m ≤ n) : IsClosedImmersion (infinitesimalBaseChangeMap f t h) :=
  MorphismProperty.of_isPullback (isPullback_infinitesimalBaseChangeMap f t h).flip
    inferInstance

/-- The kernel ideal sheaf of `W ×_T Tₘ ↪ W ×_T Tₙ` is the pullback of the kernel ideal sheaf
of `Tₘ ↪ Tₙ`. -/
lemma ker_infinitesimalBaseChangeMap {m n : ℕ} (h : m ≤ n) :
    (infinitesimalBaseChangeMap f t h).ker =
      (T.infinitesimalNeighborhoodMap t h).ker.comap (infinitesimalBaseChangeSnd f t n) := by
  have H := isPullback_infinitesimalBaseChangeMap f t h
  rw [← H.isoPullback_hom_fst, Hom.ker_comp_of_isIso,
    IdealSheafData.ker_fst_of_isClosedImmersion]

/-- **The kernel ideal sheaves of two infinitesimal base changes annihilate each other** as
soon as the two neighbourhoods they come from are large enough, namely `n ≤ m₁ + m₂ + 1`:

```
  W ×_T T_{m₁}                W ×_T T_{m₂}
          ╲                        ╱
       J₁  ╲                      ╱  J₂
            ╲                    ╱
             ───▶ W ×_T Tₙ ◀────
```

This is the sheaf-level form of
`AlgebraicGeometry.Scheme.mul_ker_infinitesimalRingMap`, from which it is obtained by
descending to the affine neighbourhoods `Tₘ ↪ Tₙ` and pulling back along the projection
`W ×_T Tₙ ⟶ Tₙ`. -/
lemma mul_ker_infinitesimalBaseChangeMap {m₁ m₂ n : ℕ} (h₁ : m₁ ≤ n) (h₂ : m₂ ≤ n)
    (h : n ≤ m₁ + m₂ + 1) :
    (infinitesimalBaseChangeMap f t h₁).ker * (infinitesimalBaseChangeMap f t h₂).ker = 0 := by
  have hT : (T.infinitesimalNeighborhoodMap t h₁).ker *
      (T.infinitesimalNeighborhoodMap t h₂).ker = 0 :=
    Hom.mul_ker_specMap_eq_zero _ _ (T.mul_ker_infinitesimalRingMap t h₁ h₂ h)
  rw [ker_infinitesimalBaseChangeMap, ker_infinitesimalBaseChangeMap,
    ← IdealSheafData.comap_mul, hT]
  simp

/-- **The thickening ideal**: the kernel ideal sheaf of the closed immersion
`W ×_T Tₙ ↪ W ×_T T_{n+1}`. It is square zero
(`AlgebraicGeometry.Scheme.sq_thickeningIdeal`). -/
noncomputable def thickeningIdeal (n : ℕ) :
    (infinitesimalBaseChange f t (n + 1)).IdealSheafData :=
  (infinitesimalBaseChangeMap f t (Nat.le_succ n)).ker

/-- **The thickening `W ×_T Tₙ ↪ W ×_T T_{n+1}` is square zero.** -/
lemma sq_thickeningIdeal (n : ℕ) : thickeningIdeal f t n ^ 2 = 0 := by
  rw [thickeningIdeal, sq]
  exact mul_ker_infinitesimalBaseChangeMap f t (Nat.le_succ n) (Nat.le_succ n) (by omega)

/-- The closed immersion `i₀ : W ×_T T₀ ↪ W ×_T T_{n+1}` of the zeroth infinitesimal
neighbourhood, abbreviating
`AlgebraicGeometry.Scheme.infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1))`. -/
noncomputable abbrev infinitesimalBaseChangeMapZero (n : ℕ) :
    infinitesimalBaseChange f t 0 ⟶ infinitesimalBaseChange f t (n + 1) :=
  infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1))

/-- **The thickening ideal is annihilated by the ideal of the zeroth infinitesimal
neighbourhood.** Writing `J` for the kernel ideal sheaf of `W ×_T T₀ ↪ W ×_T T_{n+1}` and `Iₙ`
for the thickening ideal, `J * Iₙ = 0`; this is the sheaf-level form of `𝔪 · Iₙ = 0`.

```
  W ×_T T₀                      W ×_T Tₙ
         ╲                        ╱
       J  ╲                      ╱  Iₙ
           ╲                    ╱
            ──▶ W ×_T T_{n+1} ◀──
```
-/
lemma ker_mul_thickeningIdeal_eq_zero (n : ℕ) :
    (infinitesimalBaseChangeMapZero f t n).ker * thickeningIdeal f t n = 0 :=
  mul_ker_infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1)) (Nat.le_succ n) (by omega)

/-- The canonical isomorphism `W ×_T Tₙ ≅ V(Iₙ)` between the `n`-th infinitesimal base change
and the closed subscheme of `W ×_T T_{n+1}` cut out by the thickening ideal. -/
noncomputable def thickeningIso (n : ℕ) :
    infinitesimalBaseChange f t n ≅ (thickeningIdeal f t n).subscheme :=
  asIso (infinitesimalBaseChangeMap f t (Nat.le_succ n)).toImage

/-- The isomorphism `W ×_T Tₙ ≅ V(Iₙ)` is compatible with the two closed immersions into
`W ×_T T_{n+1}`:

```
  W ×_T Tₙ ────≅────▶ V(Iₙ)
        ╲              │
         ╲             │ subschemeι
          ╲            ▼
           ───────▶ W ×_T T_{n+1}
```
-/
@[reassoc (attr := simp)]
lemma thickeningIso_hom_subschemeι (n : ℕ) :
    (thickeningIso f t n).hom ≫ (thickeningIdeal f t n).subschemeι =
      infinitesimalBaseChangeMap f t (Nat.le_succ n) :=
  (infinitesimalBaseChangeMap f t (Nat.le_succ n)).toImage_imageι

/-- The other half of the triangle of `thickeningIso_hom_subschemeι`: the closed immersion of
`V(Iₙ)` is the transition morphism read through the isomorphism `W ×_T Tₙ ≅ V(Iₙ)`. -/
@[reassoc (attr := simp)]
lemma thickeningIso_inv_infinitesimalBaseChangeMap (n : ℕ) :
    (thickeningIso f t n).inv ≫ infinitesimalBaseChangeMap f t (Nat.le_succ n) =
      (thickeningIdeal f t n).subschemeι := by
  rw [← thickeningIso_hom_subschemeι f t n, Iso.inv_hom_id_assoc]

end Thickening

section SurjectiveBaseChange

/-! ### Surjectivity of the transition morphisms of the infinitesimal base change -/

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T)

/-- **The transition morphism `W ×_T Tₘ ⟶ W ×_T Tₙ` is surjective** for `m ≤ n`:

```
             infinitesimalBaseChangeMap f t h
  W ×_T Tₘ ──────────────────────────────────▶ W ×_T Tₙ
      │                                            │
      │ infinitesimalBaseChangeSnd f t m           │ infinitesimalBaseChangeSnd f t n
      ▼                                            ▼
     Tₘ ─────────────────────────────────────▶    Tₙ
              infinitesimalNeighborhoodMap t h
```
-/
instance {m n : ℕ} (h : m ≤ n) : Surjective (infinitesimalBaseChangeMap f t h) :=
  MorphismProperty.of_isPullback (isPullback_infinitesimalBaseChangeMap f t h).flip inferInstance

end SurjectiveBaseChange

section FlatStalk

/-! ### The stalks of the infinitesimal base change of a flat morphism -/

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T)

/-- The ring homomorphism `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1) ⟶ 𝒪_{W ×_T Tₙ, x}` obtained from
`AlgebraicGeometry.Scheme.infinitesimalRingToΓ` by taking germs at `x`; it is the map through
which `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)` acts on a stalk of `W ×_T Tₙ`:

```
                    infinitesimalRingToΓ f t n                germ ⊤ x
  𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1) ──────────────▶ Γ(W ×_T Tₙ, 𝒪) ──────────▶ 𝒪_{W ×_T Tₙ, x}
```
-/
noncomputable def infinitesimalRingToStalk (n : ℕ) (x : infinitesimalBaseChange f t n) :
    T.infinitesimalRing t n ⟶ (infinitesimalBaseChange f t n).presheaf.stalk x :=
  infinitesimalRingToΓ f t n ≫ (infinitesimalBaseChange f t n).presheaf.germ ⊤ x trivial

/-- Every point of `W ×_T Tₙ` lies over the closed point of `Tₙ`. -/
@[simp]
lemma infinitesimalBaseChangeSnd_apply (n : ℕ) (x : infinitesimalBaseChange f t n) :
    (infinitesimalBaseChangeSnd f t n).base x = closedPoint (T.infinitesimalRing t n) :=
  Subsingleton.elim _ _

/-- The action of `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)` on the stalk of `W ×_T Tₙ` at `x` is the stalk map
of the projection `W ×_T Tₙ ⟶ Tₙ`, read through the identification of `Tₙ = Spec 𝒪_{T, t} ⧸
𝔪_t ^ (n + 1)` with its own stalk:

```
                                germ ⊤ (pr₂ x)                     stalkMap x
  𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1) ── ΓSpecIso.inv ──▶ 𝒪_{Tₙ, pr₂ x} ──────────────▶ 𝒪_{W ×_T Tₙ, x}
```
-/
lemma infinitesimalRingToStalk_eq_comp_stalkMap (n : ℕ) (x : infinitesimalBaseChange f t n) :
    infinitesimalRingToStalk f t n x =
      ((ΓSpecIso (T.infinitesimalRing t n)).inv ≫
        (T.infinitesimalNeighborhood t n).presheaf.germ ⊤
          ((infinitesimalBaseChangeSnd f t n).base x) trivial) ≫
        (infinitesimalBaseChangeSnd f t n).stalkMap x := by
  rw [infinitesimalRingToStalk, infinitesimalRingToΓ, Category.assoc]
  exact ΓSpecIso_inv_comp_appTop_comp_germ _ x

/-- **The stalks of `W ×_T Tₙ` are flat over `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)`** when `f` is flat.

The `Module.Flat` form is obtained at the call site by introducing the algebra structure with
`algebraize [(infinitesimalRingToStalk f t n x).hom]`; there is deliberately no global
`Algebra (T.infinitesimalRing t n) 𝒪_{W ×_T Tₙ, x}` instance. -/
lemma flat_infinitesimalRingToStalk [Flat f] (n : ℕ) (x : infinitesimalBaseChange f t n) :
    (infinitesimalRingToStalk f t n x).hom.Flat := by
  rw [infinitesimalRingToStalk, infinitesimalRingToΓ, Category.assoc]
  exact flat_ΓSpecIso_inv_comp_appTop_comp_germ _ x (infinitesimalBaseChangeSnd_apply f t n x)

end FlatStalk

section BaseChangeOver

open Limits

/-! ### Base change of a morphism over `T` to the infinitesimal neighbourhoods -/

variable {W W' T : Scheme.{u}} (f : W ⟶ T) (f' : W' ⟶ T) (u : W' ⟶ W) (hu : u ≫ f = f') (t : T)

/-- **The base change `W' ×_T Tₙ ⟶ W ×_T Tₙ`** of a morphism `u : W' ⟶ W` over `T`:

```
                infinitesimalBaseChangeMapOver
  W' ×_T Tₙ ──────────────────────────────▶ W ×_T Tₙ
      │     ╲                            ╱      │
  pr₁ │       ╲ pr₂                pr₂ ╱        │ pr₁
      ▼         ▼                    ▼          ▼
      W' ──────▶ Tₙ ═══════════════ Tₙ ◀─────── W
            u ▶
```
-/
noncomputable def infinitesimalBaseChangeMapOver (n : ℕ) :
    infinitesimalBaseChange f' t n ⟶ infinitesimalBaseChange f t n :=
  pullback.map f' (T.fromInfinitesimalNeighborhood t n) f (T.fromInfinitesimalNeighborhood t n)
    u (𝟙 _) (𝟙 _) (by simp [hu]) (by simp)

@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMapOver_fst (n : ℕ) :
    infinitesimalBaseChangeMapOver f f' u hu t n ≫ infinitesimalBaseChangeFst f t n =
      infinitesimalBaseChangeFst f' t n ≫ u := by
  simp [infinitesimalBaseChangeMapOver]

@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMapOver_snd (n : ℕ) :
    infinitesimalBaseChangeMapOver f f' u hu t n ≫ infinitesimalBaseChangeSnd f t n =
      infinitesimalBaseChangeSnd f' t n := by
  simp [infinitesimalBaseChangeMapOver]

/-- The base change of `u` commutes with the transition morphisms of the infinitesimal
neighbourhoods:

```
  W' ×_T Tₘ ──infinitesimalBaseChangeMap──▶ W' ×_T Tₙ
      │                                          │
      │ infinitesimalBaseChangeMapOver           │ infinitesimalBaseChangeMapOver
      ▼                                          ▼
  W ×_T Tₘ ───infinitesimalBaseChangeMap───▶ W ×_T Tₙ
```
-/
@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMap_comp_mapOver {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChangeMap f' t h ≫ infinitesimalBaseChangeMapOver f f' u hu t n =
      infinitesimalBaseChangeMapOver f f' u hu t m ≫ infinitesimalBaseChangeMap f t h := by
  apply pullback.hom_ext <;> simp [infinitesimalBaseChangeMapOver_snd_assoc]

/-- **The base change of `u` pulls the thickening ideal of `W` into the thickening ideal of
`W'`**: it carries the square of `infinitesimalBaseChangeMap_comp_mapOver` for `n ≤ n + 1`,

```
  W' ×_T Tₙ ─────────▶ W' ×_T T_{n+1}
      │                      │
      ▼                      ▼
  W ×_T Tₙ ──────────▶ W ×_T T_{n+1}
```

and the ideal of a closed immersion pulls back into the ideal of the closed immersion it
factors through. -/
lemma comap_thickeningIdeal_le (n : ℕ) :
    (thickeningIdeal f t n).comap (infinitesimalBaseChangeMapOver f f' u hu t (n + 1)) ≤
      thickeningIdeal f' t n := by
  refine IdealSheafData.le_map_iff_comap_le.mp ?_
  rw [IdealSheafData.map, ← Hom.ker_comp_of_isIso (thickeningIso f' t n).hom,
    ← Category.assoc, thickeningIso_hom_subschemeι, infinitesimalBaseChangeMap_comp_mapOver]
  exact Hom.le_ker_comp _ _

end BaseChangeOver

section SliceInclusion

open Limits

/-! ### The zeroth infinitesimal base change of a product and a slice -/

variable {S Z V : Scheme.{u}} (πV : V ⟶ S) (πZ : Z ⟶ S)

/-- **The zeroth infinitesimal base change `(V ×_S Z) ×_Z Z₀ ⟶ V ×_S Z` factors through the
slice `V ⟶ V ×_S Z`** at a section `z₀` of `πZ`, provided `t` is the point `z₀` picks out, in
the precise sense that `Z₀ ⟶ Z` is unchanged by `Z ⟶ S ⟶ Z`:

```
  (V ×_S Z) ×_Z Z₀ ──pr₁──▶ V ×_S Z ──pr₁──▶ V
        ╲                                    │
          ╲                                  │ sliceInclusionFst
            ╲                                ▼
              ─────────────pr₁────────▶ V ×_S Z
```
-/
lemma infinitesimalBaseChangeFst_zero_comp_sliceInclusionFst
    (z₀ : S ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 S) (t : Z)
    (ht : Z.fromInfinitesimalNeighborhood t 0 ≫ πZ ≫ z₀ =
      Z.fromInfinitesimalNeighborhood t 0) :
    (infinitesimalBaseChangeFst (pullback.snd πV πZ) t 0 ≫ pullback.fst πV πZ) ≫
      sliceInclusionFst πV πZ z₀ hz₀ = infinitesimalBaseChangeFst (pullback.snd πV πZ) t 0 := by
  refine pullback.hom_ext (by simp) ?_
  have h1 : pullback.fst πV πZ ≫ πV = pullback.snd πV πZ ≫ πZ := pullback.condition
  have h2 : infinitesimalBaseChangeFst (pullback.snd πV πZ) t 0 ≫ pullback.snd πV πZ =
      infinitesimalBaseChangeSnd (pullback.snd πV πZ) t 0 ≫
        Z.fromInfinitesimalNeighborhood t 0 := pullback.condition
  rw [Category.assoc, Category.assoc, sliceInclusionFst_snd,
    ← Category.assoc (pullback.fst πV πZ), h1, Category.assoc,
    ← Category.assoc (infinitesimalBaseChangeFst (pullback.snd πV πZ) t 0), h2, Category.assoc, ht]

end SliceInclusion

end Scheme

end AlgebraicGeometry
