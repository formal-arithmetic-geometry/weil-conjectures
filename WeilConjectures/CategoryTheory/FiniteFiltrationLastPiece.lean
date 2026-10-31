/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import WeilConjectures.CategoryTheory.Abelian.Filtration
import Mathlib.CategoryTheory.Preadditive.Basic

/-! # The last graded piece of a collapsed finite filtration

Source: Stacks Project, Homology, Tag 0121 (definition-filtered) and Tag 012W
(lemma-biregular-ss-converges), proof of (4); used in Tag 0A4C (lemma-sandwich).
(blueprint: lem-weil-pbc-finite-filtration-last-piece)
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- A finite decreasing filtration whose earlier graded pieces vanish identifies its last
step and its last graded piece with the original object, through the canonical maps.
The comparison with any two isomorphic objects has the specified unique lift and inverse.

Source: Stacks Project, Homology, Tags 0121 and 012W, proof of (4), single surviving
piece case, used in Tag 0A4C.
(blueprint: lem-weil-pbc-finite-filtration-last-piece)

Proof: For `0 ≤ p < n`, the inclusion of step `p + 1` into step `p` has zero cokernel.
By `Preadditive.epi_iff_isZero_cokernel'` it is epi, and it is mono. In an abelian
category a mono is a kernel; epimorphy forces the map it kernels to be zero.
The kernel universal property gives a right inverse, and monicity gives a left inverse.
Thus the two steps agree as subobjects. Induction from `F.F 0 = ⊤` proves that every
step through `n` is the full subobject, so its representing inclusion is an isomorphism.
The last quotient is a cokernel of the inclusion of the zero step `n + 1`.
The cokernel universal property applied to the identity provides its inverse;
uniqueness gives the other inverse identity. Define the comparison lift by composing
`a.hom`, `c.inv` and the inverse quotient. Cancellation proves its equation and
uniqueness. Compose this lift with the inclusion; its inverse is the inverse inclusion,
the quotient, `c.hom`, and `a.inv`, in that order. Cancelling adjacent inverse pairs
proves both inverse identities. If `V` is zero, transporting its zero identity through
this isomorphism shows that the identity of `A` is zero, hence `A` is zero.
For `n = 0`, the induction has only its base case and the vanishing range is empty. -/
theorem finite_filtration_last_piece {C : Type u} [Category.{v} C] [Abelian C]
    {V : C} (F : DecreasingFiltration V) (n : ℤ) (hn : 0 ≤ n)
    (h₀ : F.F 0 = ⊤) (h₁ : F.F (n + 1) = ⊥)
    (hgr : ∀ p : ℤ, 0 ≤ p → p < n → IsZero (F.gr p)) :
    (∀ p : ℤ, 0 ≤ p → p ≤ n → F.F p = ⊤) ∧
      ∃ (j : (F.F n : C) ≅ V) (ρ : (F.F n : C) ≅ F.gr n),
        j.hom = (F.F n).arrow ∧
        ρ.hom = cokernel.π (Subobject.ofLE _ _ (F.F_succ_le n)) ∧
        ∀ (A B : C) (a : A ≅ B) (c : F.gr n ≅ B),
          (∃! f : A ⟶ (F.F n : C), f ≫ ρ.hom = a.hom ≫ c.inv) ∧
          ∀ (f : A ⟶ (F.F n : C)), f ≫ ρ.hom = a.hom ≫ c.inv →
            f = a.hom ≫ c.inv ≫ ρ.inv ∧
            ∃ e : A ≅ V, e.hom = f ≫ j.hom ∧
              e.inv = j.inv ≫ ρ.hom ≫ c.hom ≫ a.inv ∧
              (IsZero V → IsZero A) := by
  have hstep (p : ℤ) (hp : 0 ≤ p) (hpn : p < n) : F.F (p + 1) = F.F p := by
    have : Epi (Subobject.ofLE _ _ (F.F_succ_le p)) :=
      (Preadditive.epi_iff_isZero_cokernel _).2 (hgr p hp hpn)
    have : IsIso (Subobject.ofLE _ _ (F.F_succ_le p)) := isIso_of_mono_of_epi _
    exact le_antisymm (F.F_succ_le p)
      (Subobject.le_of_comm (inv (Subobject.ofLE _ _ (F.F_succ_le p))) (by simp))
  have htop : ∀ p : ℤ, 0 ≤ p → p ≤ n → F.F p = ⊤ := by
    intro p hp
    induction p, hp using Int.leInduction with
    | base => exact fun _ ↦ h₀
    | succ k hk ih =>
      intro hkn
      rw [hstep k hk (by omega)]
      exact ih (by omega)
  have : IsIso (F.F n).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 (htop n hn le_rfl)
  have hz : Subobject.ofLE _ _ (F.F_succ_le n) = 0 := by
    have hzero : IsZero (F.F (n + 1) : C) := by
      rw [h₁]
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
    exact hzero.eq_of_src _ _
  have : IsIso (cokernel.π (Subobject.ofLE _ _ (F.F_succ_le n))) :=
    cokernel.π_of_zero hz
  let j : (F.F n : C) ≅ V := asIso (F.F n).arrow
  let ρ : (F.F n : C) ≅ F.gr n :=
    asIso (cokernel.π (Subobject.ofLE _ _ (F.F_succ_le n)))
  refine ⟨htop, j, ρ, rfl, rfl, ?_⟩
  intro A B a c
  have huniq (f : A ⟶ (F.F n : C))
      (hf : f ≫ ρ.hom = a.hom ≫ c.inv) : f = a.hom ≫ c.inv ≫ ρ.inv := by
    apply (cancel_mono ρ.hom).1
    simpa using hf
  constructor
  · refine ⟨a.hom ≫ c.inv ≫ ρ.inv, ?_, ?_⟩
    · simp
    · exact huniq
  · intro f hf
    refine ⟨huniq f hf, ?_⟩
    let e : A ≅ V := a ≪≫ c.symm ≪≫ ρ.symm ≪≫ j
    refine ⟨e, ?_, ?_, fun hV ↦ hV.of_iso e⟩
    · simp [e, huniq f hf]
    · simp [e]

end CategoryTheory.DecreasingFiltration
