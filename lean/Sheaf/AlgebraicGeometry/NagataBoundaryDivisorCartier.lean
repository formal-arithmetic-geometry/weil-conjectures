/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.Blowup.BlowupUniversal
import Sheaf.AlgebraicGeometry.CartierDivisorNowhereDense
import WeilConjectures.Blowup.Principalization

/-!
# Cartier boundary and dense interior after blowing up a boundary ideal

Source: the blueprint of the Weil conjectures, chapter
`sec-nagata-compactification`, node `det-nagata-boundary-divisor-cartier`,
order None (blueprint: det-nagata-boundary-divisor-cartier).

## Main statement

The theorem below records the admissibility, Cartier-boundary, density, and
persistence clauses for the blow-up of a finite-type ideal supported on the
complement of a quasi-compact open.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/--
For a qcqs scheme `T`, a quasi-compact open `U`, and a finite-type ideal `I`
supported on the complement of `U`, the blow-up of `I` is `U`-admissible. Its
comap ideal is invertible, has support the complement of the inverse image of
`U`, and that inverse image is scheme-theoretically dominant. These properties
persist after every further admissible blow-up.

Source: the blueprint proof of `det-nagata-boundary-divisor-cartier`, paragraphs
“Admissibility”, “Cartier boundary”, “Density”, and “Persistence”
(blueprint: det-nagata-boundary-divisor-cartier). The proof proceeds in four steps.
First,
the support hypothesis makes `I` the unit ideal on `U`, so the blow-up is
admissible. Second, principalization makes the comap of `I` invertible and the
support calculation identifies its support with the boundary. Third, the
complement of an invertible ideal is scheme-theoretically dense. Fourth, the
Cartier total-transform result and the same support and density arguments apply
to every further admissible blow-up.
-/
theorem exists_admissibleBlowup_cartierBoundary_of_coe_support_eq_compl_with_density
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (U : T.Opens) (hU : IsCompact (U : Set T))
    (I : T.IdealSheafData) (hI : I.ofFiniteType)
    (hI_support : (I.support : Set T) = (U : Set T)ᶜ) :
    ∃ (B : IsAdmissible T U),
      B.I = I ∧
        IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ U).ι ∧
          (I.comap B.I.blowupMap).IsInvertible ∧
            (I.comap B.I.blowupMap).support =
              ((B.I.blowupMap ⁻¹ᵁ U : B.I.blowup.Opens) : Set B.I.blowup)ᶜ ∧
              ∀ (C : IsAdmissible B.I.blowup (B.I.blowupMap ⁻¹ᵁ U)),
                ((I.comap B.I.blowupMap).comap C.I.blowupMap).IsInvertible ∧
                  ((I.comap B.I.blowupMap).comap C.I.blowupMap).support =
                    (((C.I.blowupMap ≫ B.I.blowupMap) ⁻¹ᵁ U :
                      C.I.blowup.Opens) : Set C.I.blowup)ᶜ ∧
                    IsSchemeTheoreticallyDominant
                      ((C.I.blowupMap ≫ B.I.blowupMap) ⁻¹ᵁ U).ι := by
  have : QuasiCompact U.ι := U.quasiCompact_ι hU
  have hdisj : Disjoint (U : Set T) (I.support : Set T) := by
    rw [hI_support]
    exact disjoint_compl_right
  refine ⟨⟨I, hI, hdisj⟩, rfl, ?_⟩
  change IsSchemeTheoreticallyDominant (I.blowupMap ⁻¹ᵁ U).ι ∧ _
  have hInv := I.isInvertible_comap_blowupMap
  have hsupport : ((I.comap I.blowupMap).support : Set I.blowup) =
      ((I.blowupMap ⁻¹ᵁ U : I.blowup.Opens) : Set I.blowup)ᶜ := by
    rw [Scheme.IdealSheafData.coe_support_comap, hI_support, Set.preimage_compl]
    rfl
  have hopen : (I.comap I.blowupMap).support.compl = I.blowupMap ⁻¹ᵁ U := by
    apply TopologicalSpace.Opens.ext
    change (((I.comap I.blowupMap).support : Set I.blowup)ᶜ) = _
    rw [hsupport, compl_compl]
  have hdense : IsSchemeTheoreticallyDominant (I.blowupMap ⁻¹ᵁ U).ι := by
    rw [← hopen]
    exact hInv.compl_support_dense.2.1
  refine ⟨hdense, hInv, hsupport, ?_⟩
  intro C
  have hInvC := hInv.comap_blowupMap C.I
  have hsupportC :
      (((I.comap I.blowupMap).comap C.I.blowupMap).support : Set C.I.blowup) =
        (((C.I.blowupMap ≫ I.blowupMap) ⁻¹ᵁ U : C.I.blowup.Opens) :
          Set C.I.blowup)ᶜ := by
    rw [Scheme.IdealSheafData.coe_support_comap, hsupport, Set.preimage_compl]
    rfl
  have hopenC : ((I.comap I.blowupMap).comap C.I.blowupMap).support.compl =
      (C.I.blowupMap ≫ I.blowupMap) ⁻¹ᵁ U := by
    apply TopologicalSpace.Opens.ext
    change ((((I.comap I.blowupMap).comap C.I.blowupMap).support :
      Set C.I.blowup)ᶜ) = _
    rw [hsupportC, compl_compl]
  refine ⟨hInvC, hsupportC, ?_⟩
  rw [← hopenC]
  exact hInvC.compl_support_dense.2.1

end AlgebraicGeometry
