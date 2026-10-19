/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Finiteness of the n-fold relative Frobenius

Source: Stacks Project, Varieties, Tags 0CCD and 0CCG
(blueprint: lem-trf-relative-frobenius-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of every iterate, since ring maps preserve powers.
Source: Stacks Project, Tag 0CC7 (blueprint: lem-trf-relative-frobenius-finite). -/
private theorem frobenius_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (n : ℕ) :
    X.iterateFrobenius hp hX n ≫ f = f ≫ Y.iterateFrobenius hp hY n := by
  apply Scheme.Hom.ext (by ext x; rfl)
  intro U
  simp only [Scheme.Hom.comp_app]
  change f.app U ≫ (X.iterateFrobenius hp hX n).app (f ⁻¹ᵁ U) ≫
    X.presheaf.map (𝟙 _) =
      (Y.iterateFrobenius hp hY n).app U ≫ f.app U
  rw [X.presheaf.map_id, Category.comp_id]
  ext s
  change ((f.app U).hom s) ^ p ^ n = (f.app U).hom (s ^ p ^ n)
  exact (map_pow (f.app U).hom s _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every section is integral over the power map, using `T^(p^n) - C(s)`.
Source: Stacks Project, Tag 0CC8 (blueprint: lem-trf-relative-frobenius-finite). -/
private theorem frobenius_integral (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ) :
    IsIntegralHom (X.iterateFrobenius hp hX n) where
  isIntegral_app U _ := by
    change (iterateFrobeniusOfPrime Γ(X, U) hp
      (natCast_eq_zero_of_natCast_top_eq_zero hX U) n).IsIntegral
    intro x
    refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C x (pow_ne_zero n hp.ne_zero), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    change x ^ (p ^ n) - x ^ (p ^ n) = 0
    exact sub_self _

/-- For a locally finite type morphism to a characteristic-`p` scheme, the n-fold
relative Frobenius is finite.

Source: Stacks Project, Varieties, Tags 0CCD and 0CCG
(blueprint: lem-trf-relative-frobenius-finite).

Proof:

1. Pull `p = 0` back along `f`, and restrict to every open of `X`. Ring maps
   preserve powers, so the n-fold absolute Frobenius is natural (Tag 0CC7).
   The pullback universal property constructs the relative map and proves uniqueness.
2. The n-fold absolute Frobenius is affine since its underlying map is the identity.
   Every section `s` is a root of the monic polynomial `T^(p^n) - C(s)` over its
   section map, so it is integral (the argument of Tag 0CC8).
3. The first pullback projection is affine, as a base change of the absolute
   Frobenius of `S`, and hence separated. Since the relative map composed with
   this projection is the integral absolute Frobenius of `X`, it is integral
   by Tag 035D (`IsIntegralHom.of_comp`).
4. Its composite with the second projection is `f`, so it is locally of finite
   type by Tag 01T8 (`locallyOfFiniteType_of_comp`).
5. Apply Tag 01WJ (`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`).
-/
theorem relativeFrobenius_finite
    (p : ℕ) (S X : Scheme.{u}) (hS : S.IsCharacteristic p) (f : X ⟶ S)
    [LocallyOfFiniteType f] (n : ℕ) (hn : 1 ≤ n) :
    ∃ hX : X.IsCharacteristic p,
      ∃ r : X ⟶ pullback f (S.iterateFrobenius hS.1 (hS.2 ⊤) n),
        r ≫ pullback.fst f (S.iterateFrobenius hS.1 (hS.2 ⊤) n) =
            X.iterateFrobenius hX.1 (hX.2 ⊤) n ∧
        r ≫ pullback.snd f (S.iterateFrobenius hS.1 (hS.2 ⊤) n) = f ∧
        IsFinite r ∧
        ∀ s : X ⟶ pullback f (S.iterateFrobenius hS.1 (hS.2 ⊤) n),
          s ≫ pullback.fst f (S.iterateFrobenius hS.1 (hS.2 ⊤) n) =
              X.iterateFrobenius hX.1 (hX.2 ⊤) n →
          s ≫ pullback.snd f (S.iterateFrobenius hS.1 (hS.2 ⊤) n) = f →
          s = r := by
  have _hn := hn
  have hXt : (p : Γ(X, ⊤)) = 0 := by
    rw [← map_natCast f.appTop.hom, hS.2 ⊤, map_zero]
  have hX : X.IsCharacteristic p :=
    ⟨hS.1, natCast_eq_zero_of_natCast_top_eq_zero hXt⟩
  let F := S.iterateFrobenius hS.1 (hS.2 ⊤) n
  let G := X.iterateFrobenius hX.1 (hX.2 ⊤) n
  let r : X ⟶ pullback f F :=
    pullback.lift G f (frobenius_naturality f hS.1 (hX.2 ⊤) (hS.2 ⊤) n)
  have hr₁ : r ≫ pullback.fst f F = G := pullback.lift_fst _ _ _
  have hr₂ : r ≫ pullback.snd f F = f := pullback.lift_snd _ _ _
  have : IsIntegralHom G := frobenius_integral X hX.1 (hX.2 ⊤) n
  have : IsIntegralHom (r ≫ pullback.fst f F) := hr₁.symm ▸ ‹IsIntegralHom G›
  have : IsIntegralHom r := IsIntegralHom.of_comp r (pullback.fst f F)
  have : LocallyOfFiniteType (r ≫ pullback.snd f F) := hr₂.symm ▸ ‹LocallyOfFiniteType f›
  have : LocallyOfFiniteType r := locallyOfFiniteType_of_comp r (pullback.snd f F)
  refine ⟨hX, r, hr₁, hr₂,
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType r).2 ⟨‹_›, ‹_›⟩, ?_⟩
  intro s hs₁ hs₂
  exact pullback.hom_ext (hs₁.trans hr₁.symm) (hs₂.trans hr₂.symm)

end AlgebraicGeometry.Scheme
