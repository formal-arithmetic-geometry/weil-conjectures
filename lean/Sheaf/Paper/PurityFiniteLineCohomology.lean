/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneSectionData
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer

import Sheaf.Paper.PurityFiniteLineHighCohomology
import Sheaf.Paper.PurityFiniteLineLowCohomology
import Sheaf.Paper.PurityFiniteLineZeroRestriction

/-!
# Finite-module Kummer cohomology of the two geometric lines

Source: Milne, Lectures on Etale Cohomology, Sections 14--16; blueprint
sk-prop-a1-kummer, Coefficients and Degrees 0 and 1.
(blueprint: lem-pur-finite-line-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

/-- Combine the low-degree Kummer calculation with affine-curve cohomological dimension.
Source: Milne, Sections 14--16; blueprint sk-prop-a1-kummer, Coefficients and Degrees 0 and 1.
(blueprint: lem-pur-finite-line-cohomology).

Proof: the low-degree calculation supplies the normalized isomorphism, the vanishing in
degree one on the affine line. The constant-sheaf calculation gives degree-zero restriction.
For every higher degree apply
the affine-curve torsion vanishing theorem to the given coefficient sheaf. A positive degree
on the affine line is either one or at least two. -/
theorem finite_line_cohomology (A : Type (u + 1)) [CommRing A] [Finite A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hℓΩ : IsUnit (ℓ : Ω)) (hN : 1 ≤ N)
    (hA : ((ℓ ^ N : ℕ) : A) = 0)
    (hm : IsUnit ((ℓ ^ N : ℕ) : Γ(Line (Spec (CommRingCat.of Ω)), ⊤))) :
    let S := Spec (CommRingCat.of Ω)
    let X := Line S
    let F := Scheme.finiteEtaleTateSheaf A (ℓ ^ N) X hA 1
    let H := ((sections X.smallEtaleTopology A (openObject S)).rightDerived 1).obj F
    ∃ e : H ≅ ModuleCat.of A A,
      e.hom (kummerClass A X (openObject S) F (ℓ ^ N) hm
        (Etale.ordinaryFiniteRootMap A (ℓ ^ N) hA X) (coordinateUnit S)) = 1 ∧
      (∀ q : ℕ, 0 < q → IsZero (((sections X.smallEtaleTopology A
        (Scheme.Etale.mk (𝟙 X))).rightDerived q).obj F)) ∧
      (∀ q : ℕ, 2 ≤ q → IsZero (((sections X.smallEtaleTopology A
        (openObject S)).rightDerived q).obj F)) ∧
      IsIso ((NatTrans.rightDerived
        (F := sections X.smallEtaleTopology A (Scheme.Etale.mk (𝟙 X)))
        (G := sections X.smallEtaleTopology A (openObject S))
        ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
          (restriction S).op) 0).app F) := by
  obtain ⟨e, he, hX⟩ :=
    finite_line_low_cohomology A Ω ℓ N hℓ hℓΩ hN hA hm
  let S := Spec (CommRingCat.of Ω)
  let X := Line S
  let F := Scheme.finiteEtaleTateSheaf A (ℓ ^ N) X hA 1
  have hpos : 0 < ℓ ^ N := pow_pos hℓ.pos N
  refine ⟨e, he, ?_, ?_, finite_line_zero_restriction A Ω ℓ N hℓ hℓΩ hA⟩
  · intro q hq
    by_cases hq1 : q = 1
    · subst q
      exact hX
    · exact (finite_line_high_cohomology A (ℓ ^ N) hpos hA Ω F q (by omega)).1
  · intro q hq
    exact (finite_line_high_cohomology A (ℓ ^ N) hpos hA Ω F q hq).2

end WeilConjectures.PurityFiniteSetting.RankOne
