/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# The lowest-row edge of a first-quadrant spectral sequence

Source: Stacks Project, Homology, Tags 011N, 011O, 0121 and 0132
(blueprint: lem-pur-first-quadrant-lowest-row-edge).

The stable term at `(p,q)` of total degree `n` is represented on page `n+2`.
The convergence identifications are transported along the canonical stabilization
comparison to this representative of the recursive cycle/boundary quotient.
The conclusion specifies stationary page comparisons by their cycle inclusions
and homology projections, and specifies the edge by its quotient square.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The lowest-row edge is an isomorphism, with its canonical survival comparisons.
Source: Stacks Project, Homology, Tags 011N, 011O, 0121 and 0132
(blueprint: lem-pur-first-quadrant-lowest-row-edge).

Proof:
1. The zeros outside the first quadrant and below row `m` propagate through all
   pages, since a subquotient of a zero object is zero (`def-sp-abelian`,
   `def-sp-spectral-sequence`).
2. At `(0,m)` every incoming source has negative first index. Every outgoing
   target has second index less than `m`. Thus both differentials vanish.
   The recursive cycles remain the whole initial entry and boundaries remain zero
   (`def-sp-convergence`). Starting with the identity, lift to cycles and project
   to homology using the page isomorphism. This gives exactly `a` and `b` below,
   so `a m` is the canonical survival isomorphism to the stable page `m+2`.
3. For `1 ≤ p ≤ m`, the stable term `(p,m-p)` vanishes, so the supplied convergence
   comparison makes the corresponding graded piece zero (`def-sp-filtration`).
4. Descend from `F^(m+1) = 0`: a monomorphism with zero cokernel is an isomorphism
   in an abelian category. Thus successive filtration steps agree and `F^1 = 0`.
   For `m=0` this is already the terminal filtration hypothesis.
5. The edge is quotient from `F^0 = H^m`, followed by the supplied convergence
   comparison and the inverse stationary comparison. Its defining quotient square
   is displayed below. Quotient by the now zero `F^1` is an isomorphism; hence
   every factor, and therefore this particular edge, is an isomorphism.
-/
theorem first_quadrant_lowest_row_edge
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : E₂CohomologicalSpectralSequence C)
    (hfirst : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2).X (p, q)))
    (H : ℕ → C) (F : ∀ n : ℕ, DecreasingFiltration (H n))
    (htop : ∀ n : ℕ, (F n).F 0 = ⊤)
    (hbottom : ∀ n : ℕ, (F n).F ((n : ℤ) + 1) = ⊥)
    (conv : ∀ (n p q : ℕ) (_hpq : p + q = n),
      (F n).gr p ≅ (E.page ((n : ℤ) + 2)).X (p, q))
    (m : ℕ)
    (hrow : ∀ p q : ℕ, q < m → IsZero ((E.page 2).X (p, q))) :
    ∃ (a : ∀ r : ℕ, (E.page 2).X (0, m) ≅
          (E.page ((r : ℤ) + 2)).X (0, m))
      (b : ∀ r : ℕ, (E.page 2).X (0, m) ⟶
          (E.page ((r : ℤ) + 2)).cycles (0, m)),
      (a 0).hom = 𝟙 _ ∧
      (∀ r : ℕ,
        b r ≫ (E.page ((r : ℤ) + 2)).iCycles (0, m) = (a r).hom ∧
        b r ≫ (E.page ((r : ℤ) + 2)).homologyπ (0, m) ≫
          (E.iso ((r : ℤ) + 2) ((r : ℤ) + 3) (0, m)).hom = (a (r + 1)).hom) ∧
      (F m).F 1 = ⊥ ∧
      ∃ edge : H m ⟶ (E.page 2).X (0, m),
        ((F m).F 0).arrow ≫ edge ≫ (a m).hom =
          cokernel.π (Subobject.ofLE _ _ ((F m).F_succ_le 0)) ≫
            (conv m 0 m (by omega)).hom ∧ IsIso edge := by
  -- Every term to the left of column zero or below row m stays zero.
  have hzero (r : ℕ) (p q : ℤ) (h : p < 0 ∨ q < (m : ℤ)) :
      IsZero ((E.page ((r : ℤ) + 2)).X (p, q)) := by
    have hz : IsZero ((E.page 2).X (p, q)) := by
      rcases h with hp | hq
      · exact hfirst p q (Or.inl hp)
      · by_cases hp : p < 0
        · exact hfirst p q (Or.inl hp)
        by_cases hq' : q < 0
        · exact hfirst p q (Or.inr hq')
        have hp' : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by omega)
        have hq'' : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
        simpa only [hp', hq''] using hrow p.toNat q.toNat (by omega)
    induction r with
    | zero => exact hz
    | succ r ih =>
      exact (E.iso ((r : ℤ) + 2) (((r + 1 : ℕ) : ℤ) + 2) (p, q)).isZero_iff.mp
        (((E.page ((r : ℤ) + 2)).sc (p, q)).isZero_homology_of_isZero_X₂ ih)
  have hout (r : ℕ) :
      (E.page ((r : ℤ) + 2)).d (0, m) ((r : ℤ) + 2, (m : ℤ) - (r + 2) + 1) = 0 :=
    (hzero r _ _ (Or.inr (by omega))).eq_of_tgt _ _
  have hin (r : ℕ) :
      (E.page ((r : ℤ) + 2)).d (-((r : ℤ) + 2), (m : ℤ) + (r + 2) - 1) (0, m) =
        0 :=
    (hzero r _ _ (Or.inl (by omega))).eq_of_src _ _
  have hnext (r : ℕ) :
      (ComplexShape.up' (((r : ℤ) + 2, 1 - (r + 2)) : ℤ × ℤ)).next (0, m) =
        ((r : ℤ) + 2, (m : ℤ) - (r + 2) + 1) := by
    apply ComplexShape.next_eq'
    change ((0, (m : ℤ)) : ℤ × ℤ) +
      (((r : ℤ) + 2, 1 - ((r : ℤ) + 2)) : ℤ × ℤ) = _
    ext <;> dsimp <;> omega
  have hprev (r : ℕ) :
      (ComplexShape.up' (((r : ℤ) + 2, 1 - (r + 2)) : ℤ × ℤ)).prev (0, m) =
        (-((r : ℤ) + 2), (m : ℤ) + (r + 2) - 1) := by
    apply ComplexShape.prev_eq'
    change (-((r : ℤ) + 2), (m : ℤ) + (r + 2) - 1) +
      (((r : ℤ) + 2, 1 - ((r : ℤ) + 2)) : ℤ × ℤ) = (0, (m : ℤ))
    ext <;> dsimp <;> omega
  -- Use the canonical inclusion and projection to construct the survival maps.
  let i (r : ℕ) := (E.page ((r : ℤ) + 2)).iCyclesIso (0, m) _ (hnext r) (hout r)
  let j (r : ℕ) := (E.page ((r : ℤ) + 2)).isoHomologyπ _ (0, m) (hprev r) (hin r)
  let s (r : ℕ) := (i r).symm ≪≫ j r ≪≫
    E.iso ((r : ℤ) + 2) (((r + 1 : ℕ) : ℤ) + 2) (0, m)
  let a : ∀ r : ℕ, (E.page 2).X (0, m) ≅
      (E.page ((r : ℤ) + 2)).X (0, m) := by
    intro r
    induction r with
    | zero => exact Iso.refl _
    | succ r ar => exact ar ≪≫ s r
  let b (r : ℕ) := (a r).hom ≫ (i r).inv
  have ha (r : ℕ) : a (r + 1) = a r ≪≫ s r := rfl
  -- The other graded pieces in total degree m vanish; descend from the last step.
  have hgr (p : ℕ) (hp : 0 < p) (hpm : p ≤ m) : IsZero ((F m).gr p) := by
    exact (conv m p (m - p) (by omega)).isZero_iff.mpr
      (hzero m p ((m - p : ℕ) : ℤ) (Or.inr (by omega)))
  have heq (p : ℕ) (hp : 0 < p) (hpm : p ≤ m) :
      (F m).F ((p : ℤ) + 1) = (F m).F p := by
    let f := Subobject.ofLE _ _ ((F m).F_succ_le p)
    have : Epi f := Preadditive.epi_of_isZero_cokernel f (hgr p hp hpm)
    have : IsIso f := isIso_of_mono_of_epi f
    exact Subobject.eq_of_comm (asIso f) (Subobject.ofLE_arrow _)
  have hF : (F m).F 1 = ⊥ := by
    have hd (k : ℕ) (hk : k ≤ m) : (F m).F ((m : ℤ) + 1 - k) = ⊥ := by
      induction k with
      | zero => simpa using hbottom m
      | succ k ih =>
        have hp : 0 < m - k := by omega
        have hcast : ((m - k : ℕ) : ℤ) = (m : ℤ) - k := by omega
        rw [show (m : ℤ) + 1 - (k + 1 : ℕ) = (m - k : ℕ) by omega,
          ← heq (m - k) hp (by omega), hcast]
        convert ih (by omega) using 1
        congr 1
        omega
    simpa using hd m le_rfl
  -- The edge is the quotient map transported through the two specified comparisons.
  let f := Subobject.ofLE _ _ ((F m).F_succ_le 0)
  have hf : f = 0 := by
    apply (cancel_mono ((F m).F 0).arrow).mp
    simp only [f, Subobject.ofLE_arrow, zero_comp]
    exact (Subobject.mk_eq_bot_iff_zero (f := ((F m).F 1).arrow)).mp
      (by simpa only [Subobject.mk_arrow] using hF)
  have : IsIso (cokernel.π f) := cokernel.π_of_zero hf
  have : IsIso ((F m).F 0).arrow := by rw [htop m]; infer_instance
  let edge := inv ((F m).F 0).arrow ≫ cokernel.π f ≫
    (conv m 0 m (by omega)).hom ≫ (a m).inv
  refine ⟨a, b, rfl, ?_, hF, edge, ?_, inferInstance⟩
  · intro r
    constructor
    · simp [b, i]
    · rw [ha]
      simp [b, s, j, Category.assoc]
      rfl
  · simp [edge, Category.assoc]
    rfl

end CategoryTheory
