/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Conservative

/-!
# The comparison `f_! ⟶ f_*` is an isomorphism for a proper morphism

For a proper morphism `f : X ⟶ Y` admitting a compactification, the canonical comparison
`ι_f : f_! ⟶ f_*` of `WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison` is an isomorphism.
It is deduced from the case of an open immersion with closed range, applied to the open
immersion of a compactification of `f`.

Properness of `f` enters only through
`AlgebraicGeometry.Compactification.isClopen_range_openImmersion`: a proper open immersion has
closed range.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range`: the
  comparison `j_! ⟶ j_*` is an isomorphism for an open immersion `j` with closed range.
- `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`: for a proper `f`, the comparison
  `ι_f : f_! ⟶ f_*` is an isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

section Closed

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

omit [HasSmallSiteSheafify A] in
/-- **The comparison `j_! ⟶ j_*` is an isomorphism for an open immersion `j` with closed
range.** -/
theorem Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (hj : IsClosed (Set.range j.base)) :
    IsIso (Etale.openImmersionLowerShriekToLowerStar A j) := by
  let W : X.Opens := ⟨(Set.range j.base)ᶜ, hj.isOpen_compl⟩
  let g : ∀ i, ![U, (W : Scheme.{u})] i ⟶ X := Fin.cons j (Fin.cons W.ι fun i ↦ i.elim0)
  have : ∀ i, IsOpenImmersion (g i) :=
    Fin.cases (inferInstanceAs (IsOpenImmersion j))
      (Fin.cases (inferInstanceAs (IsOpenImmersion W.ι)) fun i ↦ i.elim0)
  have hW : Set.range W.ι.base = (Set.range j.base)ᶜ := W.range_ι
  have hcover : ⋃ i, Set.range (g i).base = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ?_
    by_cases hx : x ∈ Set.range j.base
    · exact ⟨0, hx⟩
    · exact ⟨1, hW.ge hx⟩
  have hjk : Disjoint (Set.range j.base) (Set.range W.ι.base) := by
    rw [hW]
    exact disjoint_compl_right
  have happ : ∀ F, IsIso ((Etale.openImmersionLowerShriekToLowerStar A j).app F) := fun F ↦ by
    refine Etale.isIso_of_isIso_localizationRestriction A _ g hcover
      (Fin.cases ?_ (Fin.cases ?_ fun i ↦ i.elim0))
    · exact Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar A j F
    · exact Etale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar A j W.ι hjk F
  exact NatIso.isIso_of_isIso_app _

end Closed

section Proper

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [IsProper f]

/-- **For a proper morphism `f`, the canonical comparison `ι_f : f_! ⟶ f_*` is an
isomorphism.** -/
instance Etale.isIso_lowerShriekToLowerStar :
    IsIso (Etale.lowerShriekToLowerStar A f) :=
  Etale.isIso_lowerShriekToLowerStar_of_isIso A f
    (Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A
      (HasCompactification.compactification f).i
      ((HasCompactification.compactification f).isClopen_range_openImmersion
        inferInstance).isClosed)

end Proper

end AlgebraicGeometry
