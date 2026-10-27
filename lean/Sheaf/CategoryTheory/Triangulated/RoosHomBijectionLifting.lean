/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! # Lifting Hom bijections through a specified Roos triangle

Source: blueprint, `sec-smooth-purity/sk-prop-sf-closed-unit/`
`prop-sf-closed-unit-all-stages.proof.md`, integral-stage paragraph
(blueprint: lem-sf-roos-hom-bijection-lifting).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

open CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- An exact functor lifts the shifted tower-term Hom bijections to the specified
Roos reconstruction. Source: blueprint, `prop-sf-closed-unit-all-stages.proof.md`,
integral-stage paragraph (blueprint: lem-sf-roos-hom-bijection-lifting).

Here `T n` denotes the paper's term numbered `n + 1`. The specified Roos triangle
is `Q ⟶ ∏ᶜ T ⟶ ∏ᶜ T ⟶ Q⟦1⟧`, with arrows `q`, `1-s`, and `d`.
The triangle used in the target category is its image under `F`, transported
through `piComparison F T` and `F.commShiftIso 1`: its augmentation is
`F.map q ≫ piComparison F T`, and its connecting arrow is
`inv (piComparison F T) ≫ F.map d ≫ (F.commShiftIso 1).hom.app Q`.
Thus no independently chosen target triangle or connecting arrow is involved.

Proof plan:
1. The universal property of products (def-weil-category-product) identifies Hom
into the product with the product of the tower-term Hom groups. Under these
identifications, the comparison is precisely the componentwise maps in `hT`.
It is bijective for all shifts, in particular for shifts zero and one.
2. Product projections give `rho F(s) = s' rho`; additivity then identifies
`F(1-s)` with `1-s'` after transport. Exactness of `F`
(def-weil-triangulated-category) makes the transported image distinguished,
with connecting arrow the displayed transport of `F.map d`.
3. Hom exactness and rotation (lem-weil-pbc-hom-into-triangle-exact) give the
five-term exact rows with terms Hom(P[1],B), Hom(P[1],B), Hom(P,Q), Hom(P,B),
and Hom(P,B), and the corresponding row in the target category.
4. The vertical maps are the product comparisons and `F.map` in the middle.
The product squares commute by the projection equations. The augmentation
square commutes by functoriality. For the boundary square, shift the equality
back: naturality of the specified shift comparison identifies `F` of the
source boundary with the target boundary of the product comparison. Faithfulness
of shift gives the unshifted equality, with exactly the transported `F.map d`.
5. The four outer maps are bijective by step 1. The five lemma
(lem-weil-pbc-five-lemma) makes the middle map bijective. This middle map is
`u ↦ F.map u`; no vanishing of a derived limit or Mittag--Leffler condition
has been used. -/
theorem map_bijective_of_roos
    {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ m : ℤ, (shiftFunctor C m).Additive] [Pretriangulated C]
    [HasCountableProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ m : ℤ, (shiftFunctor D m).Additive] [Pretriangulated D]
    [HasCountableProducts D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (P Q : C) (T : ℕ → C) (t : ∀ n : ℕ, T (n + 1) ⟶ T n)
    (q : Q ⟶ ∏ᶜ T) (d : ∏ᶜ T ⟶ Q⟦(1 : ℤ)⟧)
    (hQ : IsDerivedLimitTriangle t Q q d) [IsIso (piComparison F T)]
    (hT : ∀ (n : ℕ) (m : ℤ), Function.Bijective
      (fun (a : P⟦m⟧ ⟶ T n) ↦ (F.commShiftIso m).inv.app P ≫ F.map a)) :
    Function.Bijective (fun (a : P ⟶ Q) ↦ F.map a) := by
  classical
  -- First remove the invertible source comparison, then use product projections.
  have hterm (m : ℤ) (n : ℕ) :
      Function.Bijective (F.map : (P⟦m⟧ ⟶ T n) → _) := by
    constructor
    · intro a b hab
      exact (hT n m).injective (by simp only [hab])
    · intro b
      obtain ⟨a, ha⟩ := (hT n m).surjective ((F.commShiftIso m).inv.app P ≫ b)
      exact ⟨a, (cancel_epi ((F.commShiftIso m).inv.app P)).mp ha⟩
  have hprod (m : ℤ) :
      Function.Bijective (F.map : (P⟦m⟧ ⟶ ∏ᶜ T) → _) := by
    constructor
    · intro a b hab
      apply Pi.hom_ext
      intro n
      apply (hterm m n).injective
      simp only [F.map_comp, hab]
    · intro b
      choose a ha using fun n ↦ (hterm m n).surjective (b ≫ F.map (Pi.π T n))
      refine ⟨Pi.lift a, ?_⟩
      apply (cancel_mono (piComparison F T)).mp
      apply Pi.hom_ext
      intro n
      simpa only [Category.assoc, piComparison_comp_π, ← F.map_comp, Pi.lift_π]
        using ha n
  have hzero : Function.Bijective (F.map : (P ⟶ ∏ᶜ T) → _) := by
    let e : P⟦(0 : ℤ)⟧ ≅ P := (shiftFunctorZero C ℤ).app P
    constructor
    · intro a b hab
      have h := (hprod 0).injective
        (show F.map (e.hom ≫ a) = F.map (e.hom ≫ b) by simp only [F.map_comp, hab])
      exact (cancel_epi e.hom).mp h
    · intro b
      obtain ⟨a, ha⟩ := (hprod 0).surjective (F.map e.hom ≫ b)
      exact ⟨e.inv ≫ a, by simp [ha]⟩
  -- Work with the actual image triangle, keeping its specified connecting arrow.
  let S := Pretriangulated.Triangle.mk q (towerTransitionEndomorphism t) d
  have hS : S ∈ Pretriangulated.distinguishedTriangles := hQ
  have hFS := F.map_distinguished S hS
  dsimp [S, mapTriangle, Pretriangulated.Triangle.mk] at hFS
  have hqv : q ≫ towerTransitionEndomorphism t = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ S hS
  have hvd : towerTransitionEndomorphism t ≫ d = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₂₃ S hS
  have hshift (u : P ⟶ Q) :
      F.map (u⟦(1 : ℤ)⟧') ≫ (F.commShiftIso 1).hom.app Q =
        (F.commShiftIso 1).hom.app P ≫ (F.map u)⟦(1 : ℤ)⟧' :=
    F.commShiftIso_hom_naturality u 1
  -- The kernel chase uses the preceding product copy and shifted Hom groups.
  have hkernel (u : P ⟶ Q) (hu : F.map u = 0) : u = 0 := by
    have huq : u ≫ q = 0 := (hzero.injective (by simp [hu]))
    obtain ⟨a, ha⟩ := Pretriangulated.Triangle.coyoneda_exact₁ S hS
      (u⟦(1 : ℤ)⟧') (by
        simp only [S, Pretriangulated.Triangle.mk_mor₁, ← Functor.map_comp, huq, Functor.map_zero])
    dsimp [S, Pretriangulated.Triangle.mk] at a ha
    have hFa : F.map a ≫ (F.map d ≫ (F.commShiftIso 1).hom.app Q) = 0 := by
      rw [← Category.assoc, ← F.map_comp, ← ha, hshift, hu, Functor.map_zero,
        comp_zero]
    obtain ⟨b', hb'⟩ := Pretriangulated.Triangle.coyoneda_exact₃ _ hFS (F.map a) hFa
    dsimp [Pretriangulated.Triangle.mk] at b' hb'
    obtain ⟨b, hb⟩ := (hprod 1).surjective b'
    have hab : a = b ≫ towerTransitionEndomorphism t :=
      (hprod 1).injective (by simpa only [F.map_comp, hb] using hb')
    apply (shiftFunctor C (1 : ℤ)).map_injective
    rw [Functor.map_zero, ha, hab, Category.assoc, hvd, comp_zero]
  constructor
  · intro a b hab
    exact sub_eq_zero.mp (hkernel (a - b) (by simp [hab]))
  · intro z
    -- Lift the augmentation, then correct its lift by the connecting arrow.
    obtain ⟨b, hb⟩ := hzero.surjective (z ≫ F.map q)
    have hbv : b ≫ towerTransitionEndomorphism t = 0 := by
      apply hzero.injective
      simp only [F.map_comp, hb, Category.assoc, F.map_zero]
      rw [← F.map_comp, hqv, F.map_zero, comp_zero]
    obtain ⟨u, hu⟩ := Pretriangulated.Triangle.coyoneda_exact₂ S hS b hbv
    dsimp [S, Pretriangulated.Triangle.mk] at u hu
    have hzq : (z - F.map u) ≫ F.map q = 0 := by
      rw [Preadditive.sub_comp, ← F.map_comp, ← hu, hb, sub_self]
    obtain ⟨a', ha'⟩ := Pretriangulated.Triangle.coyoneda_exact₁ _ hFS
      ((z - F.map u)⟦(1 : ℤ)⟧')
      (by simp only [← Functor.map_comp, hzq, Functor.map_zero])
    dsimp [Pretriangulated.Triangle.mk] at a' ha'
    obtain ⟨a, ha⟩ := (hprod 1).surjective ((F.commShiftIso 1).hom.app P ≫ a')
    obtain ⟨w, hw⟩ := (shiftFunctor C (1 : ℤ)).map_surjective (a ≫ d)
    have hwz : F.map w = z - F.map u := by
      apply (shiftFunctor D (1 : ℤ)).map_injective
      apply (cancel_epi ((F.commShiftIso 1).hom.app P)).mp
      rw [← hshift, hw, F.map_comp, ha, Category.assoc]
      simpa only [Category.assoc] using
        congrArg (fun k ↦ (F.commShiftIso 1).hom.app P ≫ k) ha'.symm
    exact ⟨u + w, by dsimp; rw [F.map_add, hwz]; abel⟩

end CategoryTheory.Functor
