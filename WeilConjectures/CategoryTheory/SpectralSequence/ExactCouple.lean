/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Tactic.Linarith

/-!
# Exact couples

An exact couple `(D, E, α, f, g)` in an abelian category `C` consists of bigraded objects
`D^{p,q}` and `E^{p,q}` (`p q : ℤ`) together with morphisms
```
  α : D^{p,q} ⟶ D^{p-1,q+1},   f : E^{p,q} ⟶ D^{p+2,q-1},   g : D^{p,q} ⟶ E^{p+s,q-s}
```
such that the three sequences
```
  E^{p-2,q+1} ⟶ D^{p,q} ⟶ D^{p-1,q+1},
  D^{p-s,q+s} ⟶ E^{p,q} ⟶ D^{p+2,q-1},
  D^{p+1,q-1} ⟶ D^{p,q} ⟶ E^{p+s,q-s}
```
are exact. The integer `s ≥ 0` is the *type* of the couple: exact couples in the sense of the
blueprint (`def-sp-exact-couple`) have type `0`, and the `r`-th derived couple of such a couple
has type `r`. These are the bidegrees of the truncation couple of a t-structure filtration, for
which the spectral sequence of the couple has `E₂^{p,q} ⇒ H^{p+q}`.

To avoid casts between the objects `D^{p,q}` for propositionally equal indices, the structure
maps are indexed by all pairs of bidegrees together with hypotheses relating them (proved by
`lia` by default), as in `CategoryTheory.SpectralSequence`.

## Main definitions

- `CategoryTheory.ExactCouple C s`: exact couples of type `s` in `C`.
- `CategoryTheory.ExactCouple.d`: the differential `d = g ∘ f : E^{p,q} ⟶ E^{p+s+2,q-s-1}`.
- `CategoryTheory.ExactCouple.Hom`: morphisms of exact couples, and the category structure.

## References

* [Stacks Project, Tag 011Q](https://stacks.math.columbia.edu/tag/011Q)
* [Stacks Project, Tag 0AMJ](https://stacks.math.columbia.edu/tag/0AMJ)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable (C : Type*) [Category* C] [Abelian C]

/-- An exact couple of type `s` in an abelian category `C`: bigraded objects `D^{p,q}`,
`E^{p,q}` with maps `α : D^{p,q} ⟶ D^{p-1,q+1}`, `f : E^{p,q} ⟶ D^{p+2,q-1}` and
`g : D^{p,q} ⟶ E^{p+s,q-s}` such that consecutive composites vanish and the three resulting
three-term sequences are exact. Type `0` is the exact couple of the blueprint.

This is blueprint `def-sp-exact-couple` (type `0`) and the couples of type `s` of
`lem-sp-derived-couple-exact`. -/
structure ExactCouple (s : ℕ) where
  /-- The `D`-terms of the couple. -/
  D (p q : ℤ) : C
  /-- The `E`-terms of the couple. -/
  E (p q : ℤ) : C
  /-- The map `α : D^{p,q} ⟶ D^{p-1,q+1}`, of bidegree `(-1, 1)`. -/
  α (p q p' q' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia) : D p q ⟶ D p' q'
  /-- The map `f : E^{p,q} ⟶ D^{p+2,q-1}`, of bidegree `(2, -1)`. -/
  f (p q p' q' : ℤ) (hp : p + 2 = p' := by lia) (hq : q' + 1 = q := by lia) : E p q ⟶ D p' q'
  /-- The map `g : D^{p,q} ⟶ E^{p+s,q-s}`, of bidegree `(s, -s)`. -/
  g (p q p' q' : ℤ) (hp : p + s = p' := by lia) (hq : q' + s = q := by lia) : D p q ⟶ E p' q'
  f_α (p q p' q' p'' q'' : ℤ) (hp : p + 2 = p' := by lia) (hq : q' + 1 = q := by lia)
    (hp' : p'' + 1 = p' := by lia) (hq' : q' + 1 = q'' := by lia) :
    f p q p' q' ≫ α p' q' p'' q'' = 0
  g_f (p q p' q' p'' q'' : ℤ) (hp : p + s = p' := by lia) (hq : q' + s = q := by lia)
    (hp' : p' + 2 = p'' := by lia) (hq' : q'' + 1 = q' := by lia) :
    g p q p' q' ≫ f p' q' p'' q'' = 0
  α_g (p q p' q' p'' q'' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia)
    (hp' : p' + s = p'' := by lia) (hq' : q'' + s = q' := by lia) :
    α p q p' q' ≫ g p' q' p'' q'' = 0
  /-- Exactness of `E^{p-2,q+1} ⟶ D^{p,q} ⟶ D^{p-1,q+1}` (`ker α = im f`). -/
  exact_f_α (p q p' q' p'' q'' : ℤ) (hp : p + 2 = p' := by lia) (hq : q' + 1 = q := by lia)
    (hp' : p'' + 1 = p' := by lia) (hq' : q' + 1 = q'' := by lia) :
    (ShortComplex.mk _ _ (f_α p q p' q' p'' q'')).Exact
  /-- Exactness of `D^{p-s,q+s} ⟶ E^{p,q} ⟶ D^{p+2,q-1}` (`ker f = im g`). -/
  exact_g_f (p q p' q' p'' q'' : ℤ) (hp : p + s = p' := by lia) (hq : q' + s = q := by lia)
    (hp' : p' + 2 = p'' := by lia) (hq' : q'' + 1 = q' := by lia) :
    (ShortComplex.mk _ _ (g_f p q p' q' p'' q'')).Exact
  /-- Exactness of `D^{p+1,q-1} ⟶ D^{p,q} ⟶ E^{p+s,q-s}` (`ker g = im α`). -/
  exact_α_g (p q p' q' p'' q'' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia)
    (hp' : p' + s = p'' := by lia) (hq' : q'' + s = q' := by lia) :
    (ShortComplex.mk _ _ (α_g p q p' q' p'' q'')).Exact

namespace ExactCouple

variable {C} {s : ℕ} (X : ExactCouple C s)

attribute [reassoc (attr := simp)] f_α g_f α_g

/-- The differential `d = g ∘ f : E^{p,q} ⟶ E^{p+s+2,q-s-1}` of an exact couple of type `s`. -/
def d (p q p' q' : ℤ) (hp : p + s + 2 = p' := by lia) (hq : q' + s + 1 = q := by lia) :
    X.E p q ⟶ X.E p' q' :=
  X.f p q (p + 2) (q - 1) ≫ X.g (p + 2) (q - 1) p' q'

lemma d_eq (p q p' q' p₁ q₁ : ℤ) (hp : p + s + 2 = p' := by lia)
    (hq : q' + s + 1 = q := by lia) (hp₁ : p + 2 = p₁ := by lia) (hq₁ : q₁ + 1 = q := by lia) :
    X.d p q p' q' = X.f p q p₁ q₁ ≫ X.g p₁ q₁ p' q' := by
  obtain rfl : p₁ = p + 2 := by lia
  obtain rfl : q₁ = q - 1 := by lia
  rfl

@[reassoc (attr := simp)]
lemma d_d (p q p' q' p'' q'' : ℤ) (hp : p + s + 2 = p' := by lia)
    (hq : q' + s + 1 = q := by lia) (hp' : p' + s + 2 = p'' := by lia)
    (hq' : q'' + s + 1 = q' := by lia) :
    X.d p q p' q' ≫ X.d p' q' p'' q'' = 0 := by
  simp only [d, assoc, X.g_f_assoc (p + 2) (q - 1) p' q' (p' + 2) (q' - 1), zero_comp,
    comp_zero]

/-- A morphism of exact couples of type `s`: maps on the `D`- and `E`-terms commuting with the
three structure maps. (blueprint `lem-sp-couple-morphism`) -/
@[ext]
structure Hom (X Y : ExactCouple C s) where
  /-- The map on `D`-terms. -/
  hD (p q : ℤ) : X.D p q ⟶ Y.D p q
  /-- The map on `E`-terms. -/
  hE (p q : ℤ) : X.E p q ⟶ Y.E p q
  comm_α (p q p' q' : ℤ) (hp : p' + 1 = p := by lia) (hq : q + 1 = q' := by lia) :
    X.α p q p' q' ≫ hD p' q' = hD p q ≫ Y.α p q p' q'
  comm_f (p q p' q' : ℤ) (hp : p + 2 = p' := by lia) (hq : q' + 1 = q := by lia) :
    X.f p q p' q' ≫ hD p' q' = hE p q ≫ Y.f p q p' q'
  comm_g (p q p' q' : ℤ) (hp : p + s = p' := by lia) (hq : q' + s = q := by lia) :
    X.g p q p' q' ≫ hE p' q' = hD p q ≫ Y.g p q p' q'

attribute [reassoc] Hom.comm_α Hom.comm_f Hom.comm_g

@[simps! id_hD id_hE comp_hD comp_hE]
instance : Category (ExactCouple C s) where
  Hom := Hom
  id X :=
    { hD _ _ := 𝟙 _
      hE _ _ := 𝟙 _
      comm_α _ _ _ _ _ _ := by simp
      comm_f _ _ _ _ _ _ := by simp
      comm_g _ _ _ _ _ _ := by simp }
  comp φ ψ :=
    { hD p q := φ.hD p q ≫ ψ.hD p q
      hE p q := φ.hE p q ≫ ψ.hE p q
      comm_α p q p' q' hp hq := by rw [φ.comm_α_assoc p q p' q', ψ.comm_α p q p' q', assoc]
      comm_f p q p' q' hp hq := by rw [φ.comm_f_assoc p q p' q', ψ.comm_f p q p' q', assoc]
      comm_g p q p' q' hp hq := by rw [φ.comm_g_assoc p q p' q', ψ.comm_g p q p' q', assoc] }

attribute [reassoc] comp_hD comp_hE

@[ext]
lemma hom_ext {X Y : ExactCouple C s} {φ ψ : X ⟶ Y} (hD : ∀ p q, φ.hD p q = ψ.hD p q)
    (hE : ∀ p q, φ.hE p q = ψ.hE p q) : φ = ψ :=
  Hom.ext (funext fun p ↦ funext (hD p)) (funext fun p ↦ funext (hE p))

variable {X} in
@[reassoc]
lemma Hom.comm_d {Y : ExactCouple C s} (φ : X ⟶ Y) (p q p' q' : ℤ)
    (hp : p + s + 2 = p' := by lia) (hq : q' + s + 1 = q := by lia) :
    X.d p q p' q' ≫ φ.hE p' q' = φ.hE p q ≫ Y.d p q p' q' := by
  simp only [d, assoc, φ.comm_g (p + 2) (q - 1) p' q', φ.comm_f_assoc p q (p + 2) (q - 1)]

/-- The functor sending an exact couple to its `D`-term in bidegree `(p, q)`. -/
@[simps]
def evalD (p q : ℤ) : ExactCouple C s ⥤ C where
  obj X := X.D p q
  map φ := φ.hD p q

/-- The functor sending an exact couple to its `E`-term in bidegree `(p, q)`. -/
@[simps]
def evalE (p q : ℤ) : ExactCouple C s ⥤ C where
  obj X := X.E p q
  map φ := φ.hE p q

end ExactCouple

end CategoryTheory
