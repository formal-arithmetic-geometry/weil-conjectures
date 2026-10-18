/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius

/-!
# Existence of the Frobenius of a scheme over a finite field

The `p ^ n`-power absolute Frobenius `AlgebraicGeometry.Scheme.iterateFrobenius` of a scheme in
which the prime `p` vanishes is natural (`AlgebraicGeometry.Scheme.comp_iterateFrobenius`) and is
the `p ^ n`-power Frobenius in the sense of `AlgebraicGeometry.Scheme.Hom.IsFrobenius`
(`AlgebraicGeometry.Scheme.isFrobenius_iterateFrobenius`). Consequently every scheme over a
finite field `k` has a `#k`-power Frobenius
(`AlgebraicGeometry.Scheme.Hom.exists_isFrobenius`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} (hp : p.Prime) (n : ℕ)

/-- The absolute Frobenius is natural: `g ≫ F_X = F_Y ≫ g` for every morphism `g : Y ⟶ X` of
schemes in which `p` vanishes. -/
lemma comp_iterateFrobenius {X Y : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (g : Y ⟶ X) :
    g ≫ X.iterateFrobenius hp hX n = Y.iterateFrobenius hp hY n ≫ g := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext s
  simp only [Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, preimage_iterateFrobenius,
    Hom.comp_app, eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id,
    CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  exact map_pow (g.app U).hom s (p ^ n)

/-- If `p` vanishes in the global sections of `X`, it vanishes in those of every `Y` over `X`. -/
lemma natCast_top_eq_zero_of_hom {X Y : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (g : Y ⟶ X) :
    (p : Γ(Y, ⊤)) = 0 := by
  rw [← map_natCast g.appTop.hom, hX, map_zero]

/-- The `p ^ n`-power absolute Frobenius is the `p ^ n`-power Frobenius: on every affine scheme
`t : Spec R ⟶ X` over `X` it acts as `r ↦ r ^ (p ^ n)`. -/
lemma isFrobenius_iterateFrobenius {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) :
    (X.iterateFrobenius hp hX n).IsFrobenius (p ^ n) := by
  intro R t φ hφ
  rw [comp_iterateFrobenius hp n hX (natCast_top_eq_zero_of_hom hX t) t]
  congr 1
  apply ext_of_isAffine
  rw [← cancel_mono (ΓSpecIso R).hom, ΓSpecIso_naturality]
  ext s
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hφ]
  exact map_pow (ΓSpecIso R).hom.hom s (p ^ n)

/-- Every scheme over a finite field `k` has a `#k`-power Frobenius. -/
theorem Hom.exists_isFrobenius {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : ∃ F : X ⟶ X, F.IsFrobenius (Nat.card k) := by
  have := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have hX : ((ringChar k : ℕ) : Γ(X, ⊤)) = 0 := by
    rw [← map_natCast ((ΓSpecIso (.of k)).inv ≫ f.appTop).hom, ringChar.Nat.cast_ringChar,
      map_zero]
  refine ⟨X.iterateFrobenius hp hX n, ?_⟩
  rw [Nat.card_eq_fintype_card, hcard]
  exact isFrobenius_iterateFrobenius hp n hX

end AlgebraicGeometry.Scheme
