/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Fine saturated face localizations of commutative monoids

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.1--3.1.2,
printed pp. 98--99 (blueprint: lem-trf-face-localization-fs).
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace Algebra

/-- The localization of a commutative monoid at a submonoid, realized inside its
Grothendieck group by fractions `q * f⁻¹`. Source: ILO VIII, 3.1.1--3.1.2
(blueprint: lem-trf-face-localization-fs). -/
def faceLocalization (Q : Type u) [CommMonoid Q] (F : Submonoid Q) :
    Submonoid (Algebra.GrothendieckGroup Q) where
  carrier := {x | ∃ (q : Q) (f : F), x = Algebra.GrothendieckGroup.of q *
    (Algebra.GrothendieckGroup.of f.1)⁻¹}
  one_mem' := by
    refine ⟨1, ⟨1, F.one_mem⟩, ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨q₁, f₁, rfl⟩ ⟨q₂, f₂, rfl⟩
    refine ⟨q₁ * q₂, ⟨f₁.1 * f₂.1, F.mul_mem f₁.2 f₂.2⟩, ?_⟩
    simp [mul_assoc, mul_left_comm, mul_comm]

/-- The canonical homomorphism from the group completion of a face localization
into the group completion of the ambient monoid. Source: ILO VIII, 3.1.2
(blueprint: lem-trf-face-localization-fs). -/
noncomputable def faceLocalizationGroupMap {Q : Type u} [CommMonoid Q]
    (F : Submonoid Q) :
    Algebra.GrothendieckGroup (faceLocalization Q F) →* Algebra.GrothendieckGroup Q :=
  Algebra.GrothendieckGroup.lift
    { toFun := fun x => x.1
      map_one' := rfl
      map_mul' := by intro x y; rfl }

end Algebra

namespace AlgebraicGeometry

/-- If `Q` is a fine saturated commutative monoid and `F` is a face, then the
localization `Q_F = {q f⁻¹}` inside `Q^gp` is fine saturated, and its canonical
map on group completions is an isomorphism. Source: Illusie--Laszlo--Orgogozo,
Exposé VIII, 3.1.1--3.1.2, printed pp. 98--99 (blueprint: lem-trf-face-localization-fs).

Proof: Regard the fine saturated monoid as an integral submonoid of its
Grothendieck group. A finite generating set for `Q`, together with inverses of
face generators, generates `Q_F`, so it is finitely generated; its inclusion in
`Q^gp` gives integrality. Every element of `Q^gp` is a difference of elements of
`Q`, hence the induced map on group completions is surjective and injectivity
follows from the inclusion. Finally, if `n g` lies in `Q_F` for `n > 0`, write
`n g = q f⁻¹`; then `n(g f) = q f^(n-1)` lies in `Q`, so saturation of `Q` gives
`g f ∈ Q`, and therefore `g = (g f) f⁻¹ ∈ Q_F`.
-/
theorem faceLocalization_fineSaturated {Q : Type u} [CommMonoid Q]
    (hQ : IsFineSaturatedMonoid Q) (F : Submonoid Q)
    (hF : ∀ a b : Q, a * b ∈ F → a ∈ F ∧ b ∈ F) :
    IsFineSaturatedMonoid (Algebra.faceLocalization Q F) ∧
      Function.Bijective (Algebra.faceLocalizationGroupMap F) := by
  sorry

end AlgebraicGeometry
