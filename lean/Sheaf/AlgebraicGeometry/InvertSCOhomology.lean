/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.CohomologyFractionPresentation
import Sheaf.AlgebraicGeometry.AffineCohomologyLocalization
import Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluing
import Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction

/-! # Localization of graded cohomology at a section

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR
(blueprint: lem-sc-invert-s-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical degree-zero localization comparison is an isomorphism.
The displayed equation specifies the canonical map: multiplying the image of ξ/s^n
by the trivializing section s^n gives the restriction of ξ. Since s trivializes L
on U, this equation determines the map uniquely; an arbitrary isomorphism does not suffice.

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR
(blueprint: lem-sc-invert-s-cohomology).

1. On an affine open, positive cohomology vanishes on both sides and degree zero is
   localization of sections (lem-sc-invert-s-cohomology-affine-case).
2. The restriction-and-division maps form a map of Mayer--Vietoris exact sequences.
   Principal opens commute with intersections and unions; localization and passage to
   degree zero are exact. The five-lemma proves gluing from U, V and U ∩ V
   (lem-sc-invert-s-cohomology-gluing).
3. Apply induction over quasi-compact opens to the property that all these comparisons
   are isomorphisms (lem-sc-invert-s-cohomology-induction), and take the whole space.
-/
theorem invertS_cohomology
    (X : Scheme.{u}) (L F : X.Modules) [L.IsInvertible]
    [F.IsQuasicoherent] [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(L, ⊤)) (p : ℕ) :
    ∃ U : X.Opens, (U : Set X) = nonvanishingLocus L s ∧
      ∃ e : CohomologyFractionPresentation L F s p ⊤ ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F,
        ∀ (n : ℕ) (ξ :
          (RingedSpace.openModuleCohomology X.toRingedSpace p ⊤).obj
            (F ⊗ L.tensorPow n : X.Modules)),
          (RingedSpace.openModuleCohomology X.toRingedSpace p U).map
              (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
                F ⟶ (F ⊗ L.tensorPow n : X.Modules))
              (e (cohomologyFraction L F s p ⊤ n ξ)) =
            (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
              (homOfLE (le_top : U ≤ ⊤))).app (F ⊗ L.tensorPow n : X.Modules) ξ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
