/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyCoupleData

/-!
# Exactness of the explicit filtered homology maps

Source: Stacks Project, Tags 012K and 011Q, the homology long exact sequence.
(blueprint: lem-sp-filtered-homology-couple-exactness).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem connecting_inclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n a b m : ℤ) (ha : p + 1 = a) (hb : p = b) (hm : n + 1 = m)
    (hle : b ≤ a) (Z : C) (e : (F.step b : CochainComplex C ℤ).homology m = Z) :
    let f := (filteredStep_shortExact K F p).δ n (n + 1) rfl ≫
      eqToHom (congrArg₂ (fun p n ↦ (F.step p : CochainComplex C ℤ).homology n) ha hm)
    let g := HomologicalComplex.homologyMap
      (Subobject.ofLE (F.step a) (F.step b) (F.antitone_step hle)) m ≫ eqToHom e
    f ≫ g = 0 ∧ imageSubobject f = kernelSubobject g := by
  subst a b m Z
  dsimp only
  simp (config := { congrConsts := false }) only [eqToHom_refl]
  simp (config := { congrConsts := false }) only [Category.comp_id]
  exact ⟨(filteredStep_shortExact K F p).δ_comp n (n + 1) rfl,
    (ShortComplex.exact_iff_image_eq_kernel _).mp
      ((filteredStep_shortExact K F p).homology_exact₁ n (n + 1) rfl)⟩

private theorem inclusion_projection
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n a m : ℤ) (ha : p + 1 = a) (hm : n = m)
    (hle : p ≤ a) (Z : C)
    (e : (F.complexQuotient p (p + 1) (by omega)).homology m = Z) :
    let f := HomologicalComplex.homologyMap
      (Subobject.ofLE (F.step a) (F.step p) (F.antitone_step hle)) n ≫
      eqToHom (congrArg (fun n ↦ (F.step p : CochainComplex C ℤ).homology n) hm)
    let g := HomologicalComplex.homologyMap
      (F.complexQuotientπ p (p + 1) (by omega)) m ≫ eqToHom e
    f ≫ g = 0 ∧ imageSubobject f = kernelSubobject g := by
  subst a m Z
  dsimp only
  simp (config := { congrConsts := false }) only [eqToHom_refl]
  simp (config := { congrConsts := false }) only [Category.comp_id]
  have h := (filteredStep_shortExact K F p).homology_exact₂ n
  constructor
  · change HomologicalComplex.homologyMap
      (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step hle)) n ≫
        HomologicalComplex.homologyMap (F.complexQuotientπ p (p + 1) (by omega)) n = 0
    rw [← HomologicalComplex.homologyMap_comp]
    simp [DecreasingFiltration.complexQuotientπ]
  · exact (ShortComplex.exact_iff_image_eq_kernel _).mp h

private theorem projection_connecting
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n r s : ℤ) (hp : p = r) (hn : n = s)
    (e : (F.complexQuotient p (p + 1) (by omega)).homology n =
      (F.complexQuotient r (r + 1) (by omega)).homology s)
    (Z : C) (e' : (F.step (r + 1) : CochainComplex C ℤ).homology (s + 1) = Z) :
    let g := HomologicalComplex.homologyMap
      (F.complexQuotientπ p (p + 1) (by omega)) n ≫ eqToHom e
    let f := (filteredStep_shortExact K F r).δ s (s + 1) rfl ≫ eqToHom e'
    g ≫ f = 0 ∧ imageSubobject g = kernelSubobject f := by
  subst r s Z
  dsimp only
  simp only [eqToHom_refl, Category.comp_id]
  exact ⟨(filteredStep_shortExact K F p).comp_δ n (n + 1) rfl,
    (ShortComplex.exact_iff_image_eq_kernel _).mp
      ((filteredStep_shortExact K F p).homology_exact₃ n (n + 1) rfl)⟩

/-- The explicitly constructed inclusion, connecting map, and projection are exact.
Source: Stacks Project, Tags 012K and 011Q; Mathlib HomologySequence.
(blueprint: lem-sp-filtered-homology-couple-exactness).

Proof. For each p the complex F^(p+1) -> F^p -> gr^p is short exact:
its first map is mono and the second is its cokernel projection. Apply its
long exact homology sequence. At p=-Q and degree P+Q, comp_delta and
homology_exact3 give the projection/connecting zero and exactness at E.
At p=-Q and degrees P+Q, P+Q+1, delta_comp and homology_exact1 give the
connecting/inclusion zero and exactness at the next D. At p=-(Q+1) and
degree P+Q, the zero composite of the two original complex maps and
homology_exact2 give the inclusion/projection zero and exactness at D.
The equalities -(Q-1)=-Q+1, -(Q+1)+1=-Q, P+2+(Q-1)=P+Q+1 and
P-1+(Q+1)=P+Q identify the indices. Transport each short complex by the
corresponding eqToIso; exactness is invariant under this isomorphism.
Convert its exactness to the imageSubobject=kernelSubobject equation.
This proves the six assertions for these maps without constructing or
comparing any derived page. -/
theorem filteredHomologyCouple_exact (C : Type u) [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    (∀ P Q, filteredHomologyF K F P Q ≫
      filteredHomologyAlpha K F (P + 2) (Q - 1) = 0) ∧
    (∀ P Q, filteredHomologyG K F P Q ≫
      filteredHomologyF K F (P + (0 : ℕ)) (Q - (0 : ℕ)) = 0) ∧
    (∀ P Q, filteredHomologyAlpha K F P Q ≫
      filteredHomologyG K F (P - 1) (Q + 1) = 0) ∧
    (∀ P Q, imageSubobject (filteredHomologyF K F P Q) =
      kernelSubobject (filteredHomologyAlpha K F (P + 2) (Q - 1))) ∧
    (∀ P Q, imageSubobject (filteredHomologyG K F P Q) =
      kernelSubobject (filteredHomologyF K F (P + (0 : ℕ)) (Q - (0 : ℕ)))) ∧
    (∀ P Q, imageSubobject (filteredHomologyAlpha K F P Q) =
      kernelSubobject (filteredHomologyG K F (P - 1) (Q + 1))) := by
  have h₁ (P Q : ℤ) := connecting_inclusion K F (-Q) (P + Q)
    (-(Q - 1)) (-(Q - 1 + 1)) (P + 2 + (Q - 1))
    (by omega) (by omega) (by omega) (by omega)
    (filteredHomologyD K F (P + 2 - 1) (Q - 1 + 1))
    (congrArg (fun n ↦ (F.step (-(Q - 1 + 1)) : CochainComplex C ℤ).homology n)
      (by omega))
  have h₃ (P Q : ℤ) := inclusion_projection K F (-(Q + 1)) (P + Q)
    (-Q) (P - 1 + (Q + 1)) (by omega) (by omega) (by omega)
    (filteredHomologyE K F (P - 1 + (0 : ℕ)) (Q + 1 - (0 : ℕ)))
    (by
      change (F.gradedPiece (-(Q + 1))).homology (P - 1 + (Q + 1)) =
        (F.gradedPiece (-(Q + 1 - (0 : ℕ)))).homology
          (P - 1 + (0 : ℕ) + (Q + 1 - (0 : ℕ)))
      exact congrArg₂ (fun p n ↦ (F.gradedPiece p).homology n) (by omega) (by omega))
  have h₂ (P Q : ℤ) := projection_connecting K F (-Q) (P + Q)
    (-(Q - (0 : ℕ))) (P + (0 : ℕ) + (Q - (0 : ℕ))) (by omega) (by omega)
    (by
      change (F.gradedPiece (-Q)).homology (P + Q) =
        (F.gradedPiece (-(Q - (0 : ℕ)))).homology
          (P + (0 : ℕ) + (Q - (0 : ℕ)))
      exact congrArg₂ (fun p n ↦ (F.gradedPiece p).homology n) (by omega) (by omega))
    (filteredHomologyD K F (P + (0 : ℕ) + 2) (Q - (0 : ℕ) - 1))
    (congrArg₂ (fun p n ↦ (F.step p : CochainComplex C ℤ).homology n)
      (by omega) (by omega))
  exact ⟨fun P Q ↦ (h₁ P Q).1, fun P Q ↦ (h₂ P Q).1,
    fun P Q ↦ (h₃ P Q).1, fun P Q ↦ (h₁ P Q).2,
    fun P Q ↦ (h₂ P Q).2, fun P Q ↦ (h₃ P Q).2⟩

end CategoryTheory
