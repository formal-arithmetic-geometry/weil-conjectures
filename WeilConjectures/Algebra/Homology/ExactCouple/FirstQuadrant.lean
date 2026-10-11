/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.EdgeCollapse
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# First quadrant exact couples

Consider an exact couple `X` indexed by `ℤ × ℤ` whose map `α` has degree `(-1, 0)`, `f` has
degree `(1, 1)` and `g` has degree `0`, such as the exact couple of a filtered complex
(`CategoryTheory.DecreasingFiltration.exactCouple`). An index `(p, n)` is a filtration degree `p`
and a total degree `n`, and the differential of the `N`-th derived couple has degree
`(N + 1, 1)`. Writing `n = p + q`, this is the differential of degree `(r, 1 - r)` in `(p, q)`
on the page `r = N + 1`.

If the `E`-objects vanish outside the first quadrant `0 ≤ p ≤ n`, the pages from the `E₂`-page
on, reindexed by `(p, q) ↦ (p, p + q)`, form a first quadrant cohomological spectral sequence
in the sense of Mathlib (`CategoryTheory.ExactCouple.firstQuadrantSpectralSequence`), and the
convergence of the couple to a filtration with `F⁰ = ⊤` and `Fⁿ⁺¹ = ⊥` in degree `n` gives an
abutment of this spectral sequence (`CategoryTheory.ExactCouple.firstQuadrantAbutment`).

## Main definitions

- `CategoryTheory.ExactCouple.IsFirstQuadrant`: couples whose `E`-objects vanish outside the
  first quadrant.
- `CategoryTheory.ExactCouple.firstQuadrantSpectralSequence`: the associated
  `E₂CohomologicalSpectralSequenceNat`.
- `CategoryTheory.ExactCouple.firstQuadrantAbutment`: its abutment.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ShortComplex

variable {S₁ S₂ : ShortComplex C}

/-- In an abelian category, the morphism induced in homology by a morphism of short complexes
only depends on its middle component. -/
lemma homologyMap_congr_τ₂ (φ φ' : S₁ ⟶ S₂) (h : φ.τ₂ = φ'.τ₂) :
    homologyMap φ = homologyMap φ' := by
  rw [← cancel_epi S₁.homologyπ, homologyπ_naturality, homologyπ_naturality]
  congr 1
  rw [← cancel_mono S₂.iCycles, cyclesMap_i, cyclesMap_i, h]

/-- Two morphisms of short complexes `S₁ ⟶ S₂` and `S₂ ⟶ S₁` whose middle components are
inverse isomorphisms induce inverse isomorphisms in homology. -/
@[simps]
noncomputable def homologyIsoOfτ₂ (φ : S₁ ⟶ S₂) (ψ : S₂ ⟶ S₁) (h₁ : φ.τ₂ ≫ ψ.τ₂ = 𝟙 _)
    (h₂ : ψ.τ₂ ≫ φ.τ₂ = 𝟙 _) : S₁.homology ≅ S₂.homology where
  hom := homologyMap φ
  inv := homologyMap ψ
  hom_inv_id := by
    rw [← homologyMap_comp, homologyMap_congr_τ₂ (φ ≫ ψ) (𝟙 _) (by simpa using h₁),
      homologyMap_id]
  inv_hom_id := by
    rw [← homologyMap_comp, homologyMap_congr_τ₂ (ψ ≫ φ) (𝟙 _) (by simpa using h₂),
      homologyMap_id]

end ShortComplex

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (Y : HomologicalComplex C c) (Z : HomologicalComplex C c') (f : ι' → ι)
  (e : ∀ k, Z.X k ≅ Y.X (f k))
  (hd : ∀ k k', c'.Rel k k' → Z.d k k' ≫ (e k').hom = (e k).hom ≫ Y.d (f k) (f k'))
  (hrel : ∀ k k', c'.Rel k k' → c.Rel (f k) (f k')) (j : ι')
  (hprev : ¬ c'.Rel (c'.prev j) j → IsZero (Y.X (c.prev (f j))))
  (hnext : ¬ c'.Rel j (c'.next j) → IsZero (Y.X (c.next (f j))))

include hd in
lemma inv_comp_d_of_comm (k k' : ι') (h : c'.Rel k k') :
    (e k).inv ≫ Z.d k k' = Y.d (f k) (f k') ≫ (e k').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hd k k' h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

include hd hnext in
open Classical in
/-- The morphism `Z.sc j ⟶ Y.sc (f j)` used in `homologyIsoOfComponents`. -/
noncomputable def scMapOfComponents :
    ShortComplex.mk _ _ (Z.d_comp_d (c'.prev j) j (c'.next j)) ⟶
      ShortComplex.mk _ _ (Y.d_comp_d (c.prev (f j)) (f j) (c.next (f j))) where
  τ₁ := if h : c'.Rel (c'.prev j) j then
      (e (c'.prev j)).hom ≫ (Y.XIsoOfEq (c.prev_eq' (hrel _ _ h)).symm).hom else 0
  τ₂ := (e j).hom
  τ₃ := if h : c'.Rel j (c'.next j) then
      (e (c'.next j)).hom ≫ (Y.XIsoOfEq (c.next_eq' (hrel _ _ h)).symm).hom else 0
  comm₁₂ := by
    dsimp
    split_ifs with h
    · rw [Category.assoc, XIsoOfEq_hom_comp_d, hd _ _ h]
    · rw [zero_comp, Z.shape _ _ h, zero_comp]
  comm₂₃ := by
    dsimp
    split_ifs with h
    · rw [← Category.assoc, hd _ _ h, Category.assoc, d_comp_XIsoOfEq_hom]
    · rw [comp_zero, (hnext h).eq_of_tgt (Y.d _ _) 0, comp_zero]

include hd hprev in
open Classical in
/-- The morphism `Y.sc (f j) ⟶ Z.sc j` used in `homologyIsoOfComponents`. -/
noncomputable def scMapOfComponents' :
    ShortComplex.mk _ _ (Y.d_comp_d (c.prev (f j)) (f j) (c.next (f j))) ⟶
      ShortComplex.mk _ _ (Z.d_comp_d (c'.prev j) j (c'.next j)) where
  τ₁ := if h : c'.Rel (c'.prev j) j then
      (Y.XIsoOfEq (c.prev_eq' (hrel _ _ h))).hom ≫ (e (c'.prev j)).inv else 0
  τ₂ := (e j).inv
  τ₃ := if h : c'.Rel j (c'.next j) then
      (Y.XIsoOfEq (c.next_eq' (hrel _ _ h))).hom ≫ (e (c'.next j)).inv else 0
  comm₁₂ := by
    dsimp
    split_ifs with h
    · rw [Category.assoc, inv_comp_d_of_comm Y Z f e hd _ _ h, XIsoOfEq_hom_comp_d_assoc]
    · rw [zero_comp, (hprev h).eq_of_src (Y.d _ _) 0, zero_comp]
  comm₂₃ := by
    dsimp
    split_ifs with h
    · rw [inv_comp_d_of_comm Y Z f e hd _ _ h, d_comp_XIsoOfEq_hom_assoc]
    · rw [comp_zero, Z.shape _ _ h, comp_zero]

/-- Let `Z` be a complex whose objects and differentials are identified, through `f : ι' ⟶ ι`,
with those of a complex `Y`. At an index `j` such that the objects of `Y` before and after
`f j` vanish whenever there is no corresponding index before and after `j`, the homology of `Z`
at `j` is the homology of `Y` at `f j`. -/
noncomputable def homologyIsoOfComponents : Z.homology j ≅ Y.homology (f j) :=
  ShortComplex.homologyIsoOfτ₂ (scMapOfComponents Y Z f e hd hrel j hnext)
    (scMapOfComponents' Y Z f e hd hrel j hprev) (by simp [scMapOfComponents,
      scMapOfComponents']) (by simp [scMapOfComponents, scMapOfComponents'])

end HomologicalComplex

namespace ExactCouple

variable (X : ExactCouple C ((-1, 0) : ℤ × ℤ) ((1, 1) : ℤ × ℤ) 0)

/-- An exact couple (with `α` of degree `(-1, 0)` and `g` of degree `0`) is *first quadrant* if
its `E`-objects `E^{p, n}` vanish unless `0 ≤ p ≤ n`, that is, in the bigrading
`(p, q) = (p, n - p)`, unless `p ≥ 0` and `q ≥ 0`. -/
def IsFirstQuadrant : Prop :=
  ∀ i : ℤ × ℤ, i.1 < 0 ∨ i.2 < i.1 → IsZero (X.E i)

variable {X}

lemma IsFirstQuadrant.isZero (hX : X.IsFirstQuadrant) (N : ℕ) (i : ℤ × ℤ)
    (h : i.1 < 0 ∨ i.2 < i.1) : IsZero ((X.derivedIter N).E i) :=
  X.isZero_derivedIter_E 0 N (Nat.zero_le _) i (hX i h)

variable (X)

lemma degree_derivedIter (N : ℕ) :
    ((1, 1) : ℤ × ℤ) + degIter ((-1, 0) : ℤ × ℤ) (0 : ℤ × ℤ) N = ((N : ℤ) + 1, 1) := by
  rw [degIter_eq']
  ext <;> simp [add_comm]

lemma toNat_sub_one (r : ℤ) (hr : 1 ≤ r) : (((r - 1).toNat : ℕ) : ℤ) = r - 1 :=
  Int.toNat_of_nonneg (by omega)

/-- The `r`-th page (`1 ≤ r`) of the spectral sequence of an exact couple, reindexed by
`(p, q) ↦ (p, p + q)` and restricted to the first quadrant: the complex of shape
`ComplexShape.spectralSequenceNat (r, 1 - r)` formed by the objects `E^{p, p + q}` of the
`(r - 1)`-th derived couple. -/
noncomputable def firstQuadrantPage (r : ℤ) (hr : 1 ≤ r) :
    HomologicalComplex C (ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩) where
  X pq := (X.derivedIter (r - 1).toNat).E (pq.1, pq.1 + pq.2)
  d pq pq' := (X.derivedIter (r - 1).toNat).d (pq.1, pq.1 + pq.2) (pq'.1, pq'.1 + pq'.2)
  shape pq pq' h := by
    apply shape_d
    rw [degree_derivedIter, toNat_sub_one r hr]
    intro h'
    apply h
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at h'
    simp only [ComplexShape.spectralSequenceNat_rel_iff]
    omega
  d_comp_d' _ _ _ _ _ := d_d _ _ _ _

lemma rel_of_rel (r : ℤ) (hr : 1 ≤ r) (k k' : ℕ × ℕ)
    (h : (ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩).Rel k k') :
    (ComplexShape.up' (((1, 1) : ℤ × ℤ) + degIter ((-1, 0) : ℤ × ℤ) (0 : ℤ × ℤ)
      (r - 1).toNat)).Rel ((k.1 : ℤ), (k.1 : ℤ) + k.2) (k'.1, k'.1 + k'.2) := by
  simp only [ComplexShape.spectralSequenceNat_rel_iff] at h
  change _ + _ = _
  rw [degree_derivedIter, toNat_sub_one r hr]
  ext <;> simp <;> omega

/-- The homology of the reindexed `r`-th page at `(p, q)` is the homology of the complex
`(E, d)` of the `(r - 1)`-th derived couple at `(p, p + q)`. -/
noncomputable def firstQuadrantPageHomologyIso (hX : X.IsFirstQuadrant) (r : ℤ) (hr : 1 ≤ r)
    (pq : ℕ × ℕ) :
    (X.firstQuadrantPage r hr).homology pq ≅
      (X.derivedIter (r - 1).toNat).dComplex.homology (pq.1, pq.1 + pq.2) :=
  HomologicalComplex.homologyIsoOfComponents (X.derivedIter (r - 1).toNat).dComplex
    (X.firstQuadrantPage r hr) (fun pq ↦ ((pq.1 : ℤ), (pq.1 : ℤ) + pq.2)) (fun _ ↦ Iso.refl _)
    (fun _ _ _ ↦ by simp [firstQuadrantPage]) (X.rel_of_rel r hr) pq
    (fun h ↦ by
      rw [dComplex_prev]
      apply hX.isZero
      rw [degree_derivedIter, toNat_sub_one r hr]
      simp only [Prod.mk_sub_mk]
      by_contra! h'
      apply h
      have hrel : (ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩).Rel
          ((pq.1 - r).toNat, (pq.2 + r - 1).toNat) pq := by
        simp only [ComplexShape.spectralSequenceNat_rel_iff]
        omega
      rwa [(ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩).prev_eq' hrel])
    (fun h ↦ by
      rw [dComplex_next]
      apply hX.isZero
      rw [degree_derivedIter, toNat_sub_one r hr]
      simp only [Prod.mk_add_mk]
      by_contra! h'
      apply h
      have hrel : (ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩).Rel
          pq ((pq.1 + r).toNat, (pq.2 + 1 - r).toNat) := by
        simp only [ComplexShape.spectralSequenceNat_rel_iff]
        omega
      rwa [(ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩).next_eq' hrel])

/-- **The first quadrant spectral sequence of an exact couple.** If the exact couple `X` (with
`α` of degree `(-1, 0)`, `f` of degree `(1, 1)` and `g` of degree `0`) is first quadrant, the
pages `r ≥ 2` of its spectral sequence, reindexed by `(p, q) ↦ (p, p + q)`, form a first
quadrant cohomological spectral sequence: the `r`-th page is the complex `(E, d)` of the
`(r - 1)`-th derived couple, with differential of degree `(r, 1 - r)` in `(p, q)`. -/
noncomputable def firstQuadrantSpectralSequence (hX : X.IsFirstQuadrant) :
    E₂CohomologicalSpectralSequenceNat C where
  page r hr := X.firstQuadrantPage r (by omega)
  iso r r' pq hrr' hr := X.firstQuadrantPageHomologyIso hX r (by omega) pq ≪≫
    eqToIso (X.homology_dComplex_derivedIter _ _ (by omega) _)

lemma firstQuadrantSpectralSequence_page_X (hX : X.IsFirstQuadrant) (r : ℤ) (hr : 2 ≤ r)
    (pq : ℕ × ℕ) :
    ((X.firstQuadrantSpectralSequence hX).page r).X pq =
      (X.derivedIter (r - 1).toNat).E (pq.1, pq.1 + pq.2) :=
  rfl

/-- The `E₂`-page of the first quadrant spectral sequence of an exact couple is the homology of
the complex `(E, d)` of the couple. -/
lemma firstQuadrantSpectralSequence_page_two_X (hX : X.IsFirstQuadrant) (pq : ℕ × ℕ) :
    ((X.firstQuadrantSpectralSequence hX).page 2).X pq =
      X.dComplex.homology (pq.1, pq.1 + pq.2) :=
  rfl

/-- In a first quadrant couple, the entry `E^{p, n}` of the `N`-th derived couple is stable for
`N ≥ max p (n - p + 1)`. -/
lemma nonempty_derivedIter_E_iso_of_isFirstQuadrant (hX : X.IsFirstQuadrant) (p n : ℤ)
    (N₀ : ℕ) (h₁ : p ≤ N₀) (h₂ : n - p < N₀) (N : ℕ) (hN : N₀ ≤ N) :
    Nonempty ((X.derivedIter N).E (p, n) ≅ (X.derivedIter N₀).E (p, n)) := by
  induction N, hN using Nat.le_induction with
  | base => exact ⟨Iso.refl _⟩
  | succ N hN ih =>
    obtain ⟨e⟩ := X.nonempty_derivedIter_E_iso N (p, n)
      ((hX.isZero N _ (by rw [degree_derivedIter]; simp; omega)).eq_of_tgt _ _)
      ((hX.isZero N _ (by rw [degree_derivedIter]; simp; omega)).eq_of_src _ _)
    exact ⟨e ≪≫ ih.some⟩

lemma nonempty_cokernel_ofLE_congr {A : C} {P P' Q : Subobject A} (h : P = P') (hP : P ≤ Q)
    (hP' : P' ≤ Q) :
    Nonempty (cokernel (Subobject.ofLE P Q hP) ≅ cokernel (Subobject.ofLE P' Q hP')) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- **The abutment of a first quadrant couple.** If the spectral sequence of the first quadrant
couple `X` converges to the filtrations `F n` of objects `A n` (`n : ℤ`), and the filtration of
`A n` satisfies `F⁰ = ⊤` and `Fⁿ⁺¹ = ⊥` for `n ≥ 0`, then the first quadrant spectral sequence
of `X` abuts to `(A n)_{n ∈ ℕ}` with the filtrations `F n`. -/
noncomputable def firstQuadrantAbutment (hX : X.IsFirstQuadrant) {A : ℤ → C}
    {F : ∀ n, DecreasingFiltration (A n)} (hc : X.ConvergesTo A F)
    (h₀ : ∀ n : ℕ, (F n).F 0 = ⊤) (h₁ : ∀ n : ℕ, (F n).F (n + 1) = ⊥) :
    (X.firstQuadrantSpectralSequence hX).Abutment (fun n : ℕ ↦ A n) where
  filtration n p := (F n).F p
  filtration_succ_le n p := by
    simpa using (F n).F_succ_le p
  filtration_zero n := by simpa using h₀ n
  filtration_succ_self n := by simpa using h₁ n
  nonempty_gradedIso n p q hpq := by
    subst hpq
    obtain ⟨N₀, hN₀⟩ := hc p ↑(p + q)
    obtain ⟨-, -, ⟨e₁⟩⟩ := hN₀ (max N₀ (p + q + 1)) (le_max_left _ _)
    obtain ⟨e₂⟩ := X.nonempty_derivedIter_E_iso_of_isFirstQuadrant hX p ↑(p + q)
      (p + q + 1) (by omega) (by omega) _ (le_max_right _ _)
    obtain ⟨e₃⟩ := nonempty_cokernel_ofLE_congr (A := A ↑(p + q))
      (Q := (F ↑(p + q)).F p) (P := (F ↑(p + q)).F ↑(p + 1)) (P' := (F ↑(p + q)).F (↑p + 1))
      (by simp) (by simpa using (F ↑(p + q)).F_succ_le p) ((F ↑(p + q)).F_succ_le p)
    have e₄ : (X.derivedIter (p + q + 1)).E (↑p, ↑(p + q)) =
        (X.firstQuadrantSpectralSequence hX).pageInfinity (p, q) := by
      rw [SpectralSequence.pageInfinity, firstQuadrantSpectralSequence_page_X _ _ _ (by omega)]
      congr 2
      · omega
      · simp
    exact ⟨e₃ ≪≫ e₁.symm ≪≫ e₂ ≪≫ eqToIso e₄⟩

/-- The first quadrant spectral sequence of a convergent first quadrant couple abuts to the
limit of the couple. -/
lemma firstQuadrantSpectralSequence_abutsTo (hX : X.IsFirstQuadrant) {A : ℤ → C}
    {F : ∀ n, DecreasingFiltration (A n)} (hc : X.ConvergesTo A F)
    (h₀ : ∀ n : ℕ, (F n).F 0 = ⊤) (h₁ : ∀ n : ℕ, (F n).F (n + 1) = ⊥) :
    (X.firstQuadrantSpectralSequence hX).AbutsTo (fun n : ℕ ↦ A n) :=
  ⟨X.firstQuadrantAbutment hX hc h₀ h₁⟩

end ExactCouple

end CategoryTheory
