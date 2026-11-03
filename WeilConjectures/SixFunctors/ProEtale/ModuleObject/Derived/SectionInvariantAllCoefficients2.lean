/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible

/-!
# Condensed section invariant for arbitrary finite purity coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-thm-dnc/sk-lem-geometry/
`def-pur-section-invariant.md` (blueprint: def-pur-section-invariant).

The section invariant is formed in the fixed purity setting from the recorded restricted Brown
exceptional inverse image `ctfExceptionalInverseImage`, applied to the literal coefficient unit,
and then pulled back along the closed section.  The definition uses no ambient right adjoint and
no arbitrary exceptional functor.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/--
The fixed four-coefficient convention supplies localizing admissibility.  This is a proposition-only
interface used to type the recorded `ctfExceptionalInverseImage`; its coefficient alternatives
are exactly the purity convention.

Proof: each branch of `hcoeff` is a disjunct of
`IsLocalizingAdmissibleCoefficient`. The `O_E`, `E` and `Q̄_ell` branches are its
`padicIntegersRingObj`, `continuousMapRingObj E` and `padicAlgClRingObj` disjuncts verbatim.
The finite branch is exactly its finite discrete ell-primary disjunct, with no DVR quotient
restriction (Wei Yang #1423/#1441). Finite rings have representatives in Type 0.

Source: the coefficient list in literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors/sec-n-change/sk-prop-qlbar-two-colimit/`def-pur-conventions.md` and the
localizing coefficient interface in `Sheaf.Paper.LocalizingAdmissibleCoefficients`
(blueprint: def-pur-section-invariant).
-/
theorem sectionInvariantAll_admissible
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hcoeff :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    IsLocalizingAdmissibleCoefficient ell Λ := by
  rcases hcoeff with hA | hO | hE | hQ
  · exact Or.inl hA
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hO⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ))))

end AlgebraicGeometry.ProEtale.CondensedRing
