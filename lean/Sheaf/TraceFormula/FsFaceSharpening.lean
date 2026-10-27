/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.FaceLocalizationFs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Saturated
public import Mathlib.LinearAlgebra.FreeModule.PID

import Mathlib.GroupTheory.MonoidLocalization.Finite

/-!
# Localization at a face and sharpening of an fs monoid

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, §§3.1.1--3.1.5,
printed pp. 98--99, and Exposé VI, §§1.6 and 3.7(a), printed pp. 70 and 75
(blueprint: lem-trf-fs-face-sharpening).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

private theorem completion_fraction {M : Type u} [CommMonoid M]
    (g : Algebra.GrothendieckGroup M) :
    ∃ a b : M, g = Algebra.GrothendieckGroup.of a /
      Algebra.GrothendieckGroup.of b := by
  obtain ⟨⟨a, b⟩, h⟩ := (Localization.monoidOf (⊤ : Submonoid M)).surj g
  exact ⟨a, b, (eq_div_iff_mul_eq').2 h⟩

private theorem completion_lift_of {M G : Type u} [CommMonoid M] [CommGroup G]
    (f : M →* G) (x : M) :
    Algebra.GrothendieckGroup.lift f (Algebra.GrothendieckGroup.of x) = f x := by
  simp [Algebra.GrothendieckGroup.lift]

private theorem associates_cancel {M : Type u} [CommMonoid M] [IsCancelMul M] :
    IsCancelMul (Associates M) := by
  have : IsLeftCancelMul (Associates M) := ⟨by
    intro a b c h
    obtain ⟨a, rfl⟩ := Associates.mk_surjective a
    obtain ⟨b, rfl⟩ := Associates.mk_surjective b
    obtain ⟨c, rfl⟩ := Associates.mk_surjective c
    obtain ⟨v, hv⟩ := Associates.mk_eq_mk_iff_associated.mp h
    apply Associates.mk_eq_mk_iff_associated.mpr
    exact ⟨v, mul_left_cancel (by simpa only [mul_assoc] using hv)⟩⟩
  exact CommMagma.IsLeftCancelMul.toIsCancelMul _

private theorem associates_fs {M : Type u} [CommMonoid M]
    (hM : IsFineSaturatedMonoid M) : IsFineSaturatedMonoid (Associates M) := by
  have : IsCancelMul M := hM.2.1.isCancelMul _ (map_mul _)
  have : IsCancelMul (Associates M) := associates_cancel
  have : Monoid.FG M := ⟨hM.1⟩
  have : Monoid.FG (Associates M) :=
    Monoid.fg_of_surjective Associates.mkMonoidHom Associates.mk_surjective
  let j : Algebra.GrothendieckGroup M →*
      Algebra.GrothendieckGroup (Associates M) :=
    Algebra.GrothendieckGroup.lift
      (Algebra.GrothendieckGroup.of.comp Associates.mkMonoidHom)
  have hj (x : M) : j (Algebra.GrothendieckGroup.of x) =
      Algebra.GrothendieckGroup.of (Associates.mk x) := completion_lift_of _ x
  refine ⟨Monoid.FG.fg_top, Algebra.GrothendieckGroup.of_injective, ?_⟩
  intro g n hn ⟨r, hr⟩
  obtain ⟨a, b, rfl⟩ := completion_fraction g
  obtain ⟨a, rfl⟩ := Associates.mk_surjective a
  obtain ⟨b, rfl⟩ := Associates.mk_surjective b
  obtain ⟨r, rfl⟩ := Associates.mk_surjective r
  have heq : Associates.mk (a ^ n) = Associates.mk (r * b ^ n) := by
    apply Algebra.GrothendieckGroup.of_injective
    simpa only [map_mul, Associates.mk_pow, ← Associates.mk_mul_mk, map_pow,
      div_pow] using (div_eq_iff_eq_mul.mp (by simpa only [div_pow] using hr.symm))
  obtain ⟨v, hv⟩ := Associates.mk_eq_mk_iff_associated.mp heq
  have hpow : ∃ p : M, Algebra.GrothendieckGroup.of p =
      (Algebra.GrothendieckGroup.of a / Algebra.GrothendieckGroup.of b) ^ n := by
    refine ⟨r * (↑v⁻¹ : M), ?_⟩
    have hv' := congrArg (Algebra.GrothendieckGroup.of (M := M)) hv
    simp only [map_mul, map_pow] at hv'
    rw [div_pow, eq_div_iff_mul_eq']
    calc
      _ = (Algebra.GrothendieckGroup.of r * Algebra.GrothendieckGroup.of (↑v⁻¹ : M)) *
          Algebra.GrothendieckGroup.of b ^ n := by rw [map_mul]
      _ = Algebra.GrothendieckGroup.of a ^ n := by
        rw [mul_right_comm, ← hv', mul_assoc, ← map_mul]
        simp
  obtain ⟨p, hp⟩ := hM.2.2 _ n hn hpow
  refine ⟨Associates.mk p, ?_⟩
  rw [← hj, hp, map_div, hj, hj]

private theorem sharp_completion_torsionFree {M : Type u} [CommMonoid M]
    (hM : IsFineSaturatedMonoid M) (hs : ∀ x : M, IsUnit x → x = 1) :
    IsMulTorsionFree (Algebra.GrothendieckGroup M) := by
  have hsat : (MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := M))).PowSaturated := by
    intro n g hg
    by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr (hM.2.2 g n (Nat.pos_of_ne_zero hn) hg)
  have root (g : Algebra.GrothendieckGroup M) (n : ℕ) (hn : n ≠ 0)
      (hg : g ^ n = 1) : g = 1 := by
    obtain ⟨p, hp⟩ := (hsat (g := g) (n := n)
      ⟨1, by simpa using hg.symm⟩).resolve_left hn
    obtain ⟨q, hq⟩ := (hsat (g := g⁻¹) (n := n)
      ⟨1, by simp only [map_one, inv_pow, hg, inv_one]⟩).resolve_left hn
    have hpq : p * q = 1 := hM.2.1 (by simp only [map_mul, map_one, hp, hq, mul_inv_cancel])
    rw [← hp, hs p (isUnit_iff_exists_inv.mpr ⟨q, hpq⟩), map_one]
  refine ⟨?_⟩
  intro n hn x y hxy
  exact div_eq_one.mp (root (x / y) n hn (by simp [div_pow, hxy]))

private theorem face_subgroup_mem {Q : Type u} [CommMonoid Q] (F : Submonoid Q)
    (g : Algebra.GrothendieckGroup Q)
    (hg : g ∈ Subgroup.closure (Algebra.GrothendieckGroup.of '' (F : Set Q))) :
    g ∈ Algebra.faceLocalization Q F ∧ g⁻¹ ∈ Algebra.faceLocalization Q F := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      exact ⟨⟨f, 1, by simp⟩, ⟨1, ⟨f, hf⟩, by simp⟩⟩
  | one => exact ⟨Submonoid.one_mem _, by rw [inv_one]; exact Submonoid.one_mem _⟩
  | mul x y hx hy ihx ihy =>
      exact ⟨Submonoid.mul_mem _ ihx.1 ihy.1,
        by simpa only [mul_inv_rev] using Submonoid.mul_mem _ ihy.2 ihx.2⟩
  | inv x hx ih => exact ⟨ih.2, by simpa using ih.1⟩

private theorem face_units {Q : Type u} [CommMonoid Q]
    (hQ : IsFineSaturatedMonoid Q) (F : Submonoid Q)
    (hF : ∀ a b : Q, a * b ∈ F → a ∈ F ∧ b ∈ F)
    (x : Algebra.faceLocalization Q F) :
    IsUnit x ↔ (x : Algebra.GrothendieckGroup Q) ∈
      Subgroup.closure (Algebra.GrothendieckGroup.of '' (F : Set Q)) := by
  let i : Q →* Algebra.GrothendieckGroup Q := Algebra.GrothendieckGroup.of
  let H := Subgroup.closure (i '' (F : Set Q))
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
    obtain ⟨a, f, ha⟩ := x.2
    obtain ⟨b, k, hb⟩ := y.2
    have hab : a * b = f.1 * k.1 := by
      apply hQ.2.1
      have hxy := congrArg Subtype.val hy
      change (x : Algebra.GrothendieckGroup Q) * y = 1 at hxy
      rw [ha, hb] at hxy
      change i a * (i f.1)⁻¹ * (i b * (i k.1)⁻¹) = 1 at hxy
      have hh : i a * i b * (i f.1 * i k.1)⁻¹ = 1 := by
        simpa only [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using hxy
      change i (a * b) = i (f.1 * k.1)
      rw [map_mul, map_mul]
      exact mul_inv_eq_one.mp hh
    have haf : a ∈ F := (hF a b (hab ▸ F.mul_mem f.2 k.2)).1
    rw [ha]
    exact H.mul_mem (Subgroup.subset_closure ⟨a, haf, rfl⟩)
      (H.inv_mem (Subgroup.subset_closure ⟨f.1, f.2, rfl⟩))
  · intro hx
    have hinv := (face_subgroup_mem F x.1 hx).2
    exact isUnit_iff_exists_inv.mpr
      ⟨⟨x.1⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel x.1)⟩

private theorem face_quotient {Q : Type u} [CommMonoid Q]
    (F : Submonoid Q)
    (hu : ∀ x : Algebra.faceLocalization Q F,
      IsUnit x ↔ (x : Algebra.GrothendieckGroup Q) ∈
        Subgroup.closure (Algebra.GrothendieckGroup.of '' (F : Set Q)))
    (hb : Function.Bijective (Algebra.faceLocalizationGroupMap F)) :
    let R := Associates (Algebra.faceLocalization Q F)
    let H := Subgroup.closure (Algebra.GrothendieckGroup.of '' (F : Set Q))
    ∃ φ : R →* (Algebra.GrothendieckGroup Q ⧸ H),
      (∀ x : Algebra.faceLocalization Q F,
        φ (Associates.mk x) = QuotientGroup.mk' H
          (Algebra.faceLocalizationGroupMap F (Algebra.GrothendieckGroup.of x))) ∧
      Function.Injective φ ∧
      ∃ e : Algebra.GrothendieckGroup R ≃* (Algebra.GrothendieckGroup Q ⧸ H),
        ∀ r : R, e (Algebra.GrothendieckGroup.of r) = φ r := by
  let L := Algebra.faceLocalization Q F
  let H := Subgroup.closure (Algebra.GrothendieckGroup.of '' (F : Set Q))
  have : IsCancelMul (Associates L) := associates_cancel
  let k : L →* (Algebra.GrothendieckGroup Q ⧸ H) :=
    (QuotientGroup.mk' H).comp L.subtype
  have hk (x : L) (hx : IsUnit x) : k x = 1 :=
    (QuotientGroup.eq_one_iff x.1).mpr ((hu x).mp hx)
  let φ : Associates L →* (Algebra.GrothendieckGroup Q ⧸ H) :=
    { toFun := Quotient.lift k (by
        intro x y h
        obtain ⟨v, rfl⟩ := h
        rw [map_mul, hk _ v.isUnit, mul_one])
      map_one' := map_one k
      map_mul' := by
        intro x y
        obtain ⟨x, rfl⟩ := Associates.mk_surjective x
        obtain ⟨y, rfl⟩ := Associates.mk_surjective y
        exact map_mul k x y }
  have hφ (x : L) : φ (Associates.mk x) = k x := rfl
  have hφinj : Function.Injective φ := by
    intro x y h
    obtain ⟨x, rfl⟩ := Associates.mk_surjective x
    obtain ⟨y, rfl⟩ := Associates.mk_surjective y
    have hxy : y.1 / x.1 ∈ H :=
      QuotientGroup.eq_iff_div_mem.mp h.symm
    have hm := (face_subgroup_mem F (y.1 / x.1) hxy).1
    obtain ⟨v, hv⟩ := (hu ⟨y.1 / x.1, hm⟩).mpr hxy
    apply Associates.mk_eq_mk_iff_associated.mpr
    refine ⟨v, Subtype.ext ?_⟩
    have hv' := congrArg Subtype.val hv
    change x.1 * ((↑v : L) : Algebra.GrothendieckGroup Q) = y.1
    rw [hv']
    exact mul_div_cancel _ _
  let t := Algebra.GrothendieckGroup.lift φ
  have htinj : Function.Injective t := by
    change Function.Injective ((Localization.monoidOf (⊤ : Submonoid (Associates L))).lift _)
    apply (Submonoid.LocalizationMap.lift_injective_iff _ _).2
    intro x y
    exact ⟨fun h ↦ congrArg φ (Algebra.GrothendieckGroup.of_injective h),
      fun h ↦ congrArg Algebra.GrothendieckGroup.of (hφinj h)⟩
  have htsurj : Function.Surjective t := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H z
    obtain ⟨w, hw⟩ := hb.2 g
    obtain ⟨a, b, rfl⟩ := completion_fraction w
    refine ⟨Algebra.GrothendieckGroup.of (Associates.mk a) /
      Algebra.GrothendieckGroup.of (Associates.mk b), ?_⟩
    rw [map_div, completion_lift_of, completion_lift_of, hφ, hφ, ← hw]
    simp only [map_div, Algebra.faceLocalizationGroupMap, completion_lift_of]
    rfl
  refine ⟨φ, ?_, hφinj, MulEquiv.ofBijective t ⟨htinj, htsurj⟩, ?_⟩
  · intro x
    rw [hφ]
    simp only [Algebra.faceLocalizationGroupMap, completion_lift_of]
    rfl
  · exact completion_lift_of φ

/-- The localization `Q_F` of an fs monoid at a face is fine saturated and its units
are exactly the subgroup `H = F^gp` generated by the face.  Quotienting by these
units gives a sharp fs monoid; its canonical map into the ambient group quotient is
injective and its group completion is that quotient.  The displayed representative
equation fixes the canonical map, while the final basis clause records finite
freeness.
Source: Illusie--Laszlo--Orgogozo, Exposé VIII, §§3.1.1--3.1.5, printed pp. 98--99,
and Exposé VI, §§1.6 and 3.7(a), printed pp. 70 and 75
(blueprint: lem-trf-fs-face-sharpening).

Proof. Apply the face-localization fs theorem to obtain the fine saturated
localization and identify its group completion with the ambient completion.
The face condition identifies the units with the subgroup generated by the face:
if a fraction has an inverse, clearing denominators puts its numerator in the face.
The quotient `Associates` is sharp and fine saturated. For saturation, represent a
group element by `a / b`; an equation for its positive power in `Associates` lifts
to an equation up to a unit in the original monoid, where saturation applies.
The representative formula defines the canonical map to the group quotient;
the units characterization gives its injectivity, and the universal property of
group completion gives the displayed multiplicative equivalence. For a torsion
element in the completion of a sharp saturated monoid, saturation puts both it
and its inverse in the monoid. They are units, hence trivial. Finite generation
passes through `Associates` and group completion. Applying
`Module.basisOfFiniteTypeTorsionFree'` over `ℤ` yields the finite basis.
-/
theorem face_sharpening
    (Q : Type u) [CommMonoid Q] (hQ : IsFineSaturatedMonoid Q)
    (F : Submonoid Q)
    (hF : ∀ a b : Q, a * b ∈ F → a ∈ F ∧ b ∈ F) :
    let R := Associates (Algebra.faceLocalization Q F)
    let H := Subgroup.closure
      (Algebra.GrothendieckGroup.of '' (F : Set Q))
    IsFineSaturatedMonoid (Algebra.faceLocalization Q F) ∧
      (∀ x : Algebra.faceLocalization Q F,
        IsUnit x ↔ (x : Algebra.GrothendieckGroup Q) ∈ H) ∧
      IsFineSaturatedMonoid R ∧
      (∀ r : R, IsUnit r → r = 1) ∧
      ∃ φ : R →* (Algebra.GrothendieckGroup Q ⧸ H),
        (∀ x : Algebra.faceLocalization Q F,
          φ (Associates.mk x) =
            QuotientGroup.mk' H
              (Algebra.faceLocalizationGroupMap F
                (Algebra.GrothendieckGroup.of x))) ∧
        Function.Injective φ ∧
        (∃ e : Algebra.GrothendieckGroup R ≃*
            (Algebra.GrothendieckGroup Q ⧸ H),
          ∀ r : R, e (Algebra.GrothendieckGroup.of r) = φ r) ∧
      (∃ n : ℕ,
        Nonempty
          (Module.Basis (Fin n) ℤ
            (Additive (Algebra.GrothendieckGroup R)))) := by
  obtain ⟨hL, hb⟩ := faceLocalization_fineSaturated hQ F hF
  have hu := face_units hQ F hF
  have hR := associates_fs hL
  have hs (r : Associates (Algebra.faceLocalization Q F)) : IsUnit r → r = 1 :=
    (Associates.isUnit_iff_eq_one r).mp
  obtain ⟨φ, hφ, hi, e, he⟩ := face_quotient F hu hb
  refine ⟨hL, hu, hR, hs, φ, hφ, hi, ⟨e, he⟩, ?_⟩
  let R := Associates (Algebra.faceLocalization Q F)
  have : Monoid.FG R := ⟨hR.1⟩
  have : IsMulTorsionFree (Algebra.GrothendieckGroup R) :=
    sharp_completion_torsionFree hR hs
  let b := Module.basisOfFiniteTypeTorsionFree'
    (R := ℤ) (M := Additive (Algebra.GrothendieckGroup R))
  exact ⟨b.1, ⟨b.2⟩⟩

end AlgebraicGeometry
