/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import WeilConjectures.RingTheory.FilteredColimitIsDomain
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime

/-!
# Integral closedness of filtered colimits of normal domains

A filtered colimit of integrally closed domains is integrally closed. Consequently, the
localization of a filtered colimit at a prime is integrally closed when every stage localization
at the contracted prime is an integrally closed domain.

## Implementation details

The common-stage argument is applied only to colimit cocones of domains. An integral fraction
`a / b` is handled by lifting `a`, `b` and the coefficients of a monic annihilating polynomial
to a common stage. The denominator-cleared evaluation `(q.scaleRoots b).eval a` vanishes at a
later stage, where `b` is nonzero; integral closedness there gives `a = b * y`, and `y` maps to
the original fraction.

## References

* [Stacks, Tag 037D]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

private theorem lift_fin_after
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hcol : IsColimit c)
    (i : I) (n : ℕ) (x : Fin n → c.pt) :
    ∃ (j : I) (_ : i ⟶ j) (y : Fin n → D.obj j),
      ∀ k, (c.ι.app j).hom (y k) = x k := by
  classical
  induction n with
  | zero => exact ⟨i, 𝟙 i, Fin.elim0, fun k ↦ Fin.elim0 k⟩
  | succ n ih =>
    obtain ⟨j, f, y, hy⟩ := ih (fun k ↦ x k.succ)
    have ht := isColimitOfPreserves (forget CommRingCat) hcol
    obtain ⟨k, a, ha⟩ := Types.jointly_surjective_of_isColimit ht (x 0)
    change D.obj k at a
    change (c.ι.app k).hom a = x 0 at ha
    let l := IsFiltered.max j k
    let g : j ⟶ l := IsFiltered.leftToMax j k
    let h : k ⟶ l := IsFiltered.rightToMax j k
    refine ⟨l, f ≫ g, Fin.cons ((D.map h).hom a) (fun t ↦ (D.map g).hom (y t)), ?_⟩
    intro t
    refine Fin.cases ?_ (fun t ↦ ?_) t
    · change (c.ι.app l).hom ((D.map h).hom a) = x 0
      exact (ConcreteCategory.congr_hom (c.w h) a).trans ha
    · change (c.ι.app l).hom ((D.map g).hom (y t)) = x t.succ
      exact (ConcreteCategory.congr_hom (c.w g) (y t)).trans (hy t)

set_option backward.isDefEq.respectTransparency false in
/-- A filtered colimit of integrally closed domains is integrally closed. -/
theorem integrallyClosed_of_localization_cocone
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {R : Type u} [CommRing R]
    (D : I ⥤ CommRingCat.{u})
    (c : Cocone D) (hc : c.pt = CommRingCat.of R) (hcol : IsColimit c)
    (hD : ∀ i : I, IsDomain (D.obj i) ∧ IsIntegrallyClosed (D.obj i)) :
    IsIntegrallyClosed R := by
  classical
  suffices h : IsIntegrallyClosed c.pt by
    rw [hc] at h
    exact h
  let : ∀ i : I, IsDomain (D.obj i) := fun i ↦ (hD i).1
  let : ∀ i : I, IsIntegrallyClosed (D.obj i) := fun i ↦ (hD i).2
  let : IsDomain c.pt := isDomain_of_filtered_colimit_cocone D c hcol
    (fun i ↦ (hD i).1) rfl
  apply (isIntegrallyClosed_iff (FractionRing c.pt)).mpr
  intro x hx
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective c.pt x
  have hbfrac : algebraMap c.pt (FractionRing c.pt) b ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective c.pt (FractionRing c.pt)).ne
        (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  obtain ⟨i, ai, bi, hai, hbi⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (isColimitOfPreserves (forget CommRingCat) hcol) a b
  change D.obj i at ai bi
  change (c.ι.app i).hom ai = a at hai
  change (c.ι.app i).hom bi = b at hbi
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨j, f, coeff, hcoeff⟩ := lift_fin_after D c hcol i p.natDegree
    (fun k ↦ p.coeff k)
  let aj := (D.map f).hom ai
  let bj := (D.map f).hom bi
  have haj : (c.ι.app j).hom aj = a :=
    (ConcreteCategory.congr_hom (c.w f) ai).trans hai
  have hbj : (c.ι.app j).hom bj = b :=
    (ConcreteCategory.congr_hom (c.w f) bi).trans hbi
  let q : Polynomial (D.obj j) := Polynomial.X ^ p.natDegree +
    ∑ k : Fin p.natDegree, Polynomial.C (coeff k) * Polynomial.X ^ (k : ℕ)
  have hq : q.Monic :=
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hqmap : q.map (c.ι.app j).hom = p := by
    rw [hp.as_sum]
    simp only [q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, hcoeff]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun k ↦ (Polynomial.C (p.coeff k) : Polynomial c.pt) *
        (Polynomial.X : Polynomial c.pt) ^ k) p.natDegree
  have hz : (c.ι.app j).hom ((q.scaleRoots bj).eval aj) = 0 := by
    apply IsFractionRing.injective c.pt (FractionRing c.pt)
    rw [map_zero, ← Polynomial.eval₂_at_apply, Polynomial.hom_eval₂]
    rw [← Polynomial.eval₂_map]
    rw [Polynomial.map_scaleRoots _ _ _ (by simp [hq.leadingCoeff]), hqmap]
    change Polynomial.eval₂ (algebraMap c.pt (FractionRing c.pt))
      (algebraMap c.pt (FractionRing c.pt) ((c.ι.app j).hom aj))
      (p.scaleRoots ((c.ι.app j).hom bj)) = 0
    rw [hbj, haj]
    have hax : algebraMap c.pt (FractionRing c.pt) a =
        algebraMap c.pt (FractionRing c.pt) b * x := by
      rw [← hab, mul_div_cancel₀ _ hbfrac]
    rw [hax, Polynomial.scaleRoots_eval₂_mul, hpx, mul_zero]
  have hz' : (c.ι.app j).hom ((q.scaleRoots bj).eval aj) = (c.ι.app j).hom 0 := by
    simpa only [map_zero] using hz
  obtain ⟨k, g, hg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget CommRingCat) hcol) _ _).mp hz'
  change (D.map g).hom ((q.scaleRoots bj).eval aj) = (D.map g).hom 0 at hg
  let ak := (D.map g).hom aj
  let bk := (D.map g).hom bj
  let qk := q.map (D.map g).hom
  have hqk : qk.Monic := hq.map _
  have hak : (c.ι.app k).hom ak = a :=
    (ConcreteCategory.congr_hom (c.w g) aj).trans haj
  have hbk : (c.ι.app k).hom bk = b :=
    (ConcreteCategory.congr_hom (c.w g) bj).trans hbj
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbk0 : bk ≠ 0 := by
    intro h
    apply hb0
    rw [← hbk, h, map_zero]
  have hbkfrac : algebraMap (D.obj k) (FractionRing (D.obj k)) bk ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (D.obj k) (FractionRing (D.obj k))).ne hbk0
  let z : FractionRing (D.obj k) :=
    algebraMap (D.obj k) (FractionRing (D.obj k)) ak /
      algebraMap (D.obj k) (FractionRing (D.obj k)) bk
  have hzk : IsIntegral (D.obj k) z := by
    refine ⟨qk, hqk, ?_⟩
    have hscaled : (qk.scaleRoots bk).eval ak = 0 := by
      rw [← Polynomial.eval_map_apply] at hg
      rw [Polynomial.map_scaleRoots q bj (D.map g).hom
        (by simp [hq.leadingCoeff]), map_zero] at hg
      exact hg
    have hscaled' := congrArg (algebraMap (D.obj k) (FractionRing (D.obj k))) hscaled
    rw [map_zero, ← Polynomial.eval₂_at_apply] at hscaled'
    have hmul : algebraMap (D.obj k) (FractionRing (D.obj k)) bk * z =
        algebraMap (D.obj k) (FractionRing (D.obj k)) ak := by
      dsimp [z]
      field_simp
    rw [← hmul, Polynomial.scaleRoots_eval₂_mul] at hscaled'
    exact (mul_eq_zero.mp hscaled').resolve_left (pow_ne_zero _ hbkfrac)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hzk
  have hay : ak = bk * y := by
    apply IsFractionRing.injective (D.obj k) (FractionRing (D.obj k))
    rw [map_mul, hy]
    dsimp [z]
    field_simp
  let ck : D.obj k →+* c.pt := (c.ι.app k).hom
  refine ⟨ck y, ?_⟩
  have heq : a = b * ck y := by
    calc
      a = ck ak := hak.symm
      _ = ck (bk * y) := congrArg ck hay
      _ = ck bk * ck y := map_mul _ _ _
      _ = b * ck y := by rw [show ck bk = b from hbk]
  rw [← hab, heq, map_mul]
  exact (mul_div_cancel_left₀ _ hbfrac).symm

/-- The localization of a filtered colimit at a prime is integrally closed when
every stage localization at a contracted prime is an integrally closed domain.
-/
theorem filtered_colimit_localization_isIntegrallyClosed
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (hF : ∀ i : I, ∀ (p : Ideal (F.obj i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (p : Ideal ((colimit F : CommRingCat.{u}) : Type u)) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  let ι : ∀ i : I, (F.obj i) ⟶ colimit F := fun i => colimit.ι F i
  let pᵢ : ∀ i : I, Ideal ((F.obj i : CommRingCat) : Type u) :=
    fun i => Ideal.comap (ι i).hom p
  obtain ⟨hpᵢ, _, D, hD, _, c, hc, _, hcol⟩ :=
    AlgebraicGeometry.filteredColimitLocalizationAtPrime F p
  have hDi : ∀ i : I, IsDomain (D.obj i) ∧ IsIntegrallyClosed (D.obj i) := by
    intro i
    rw [hD i]
    exact hF i (pᵢ i)
  exact integrallyClosed_of_localization_cocone D c hc hcol.some hDi

end CommRingCat
