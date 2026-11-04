/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionReductionPresentation
public import WeilConjectures.Algebra.Homology.System.SystemSequenceFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSiteIso
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients

/-! # Ordinary reduction of flat representatives has flat terms

Source: current blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, (2)--(3)
(blueprint: def-sp-projection-reduction-presentation); Stacks 05V4, 08FC.

Each level of the ordinary simultaneous quotient reduction is the scalar extension of the
section presentation, and scalar extension of a flat module is flat. A strict system with
flat levels is flat on the coefficient sequence site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary simultaneous quotient reduction of a flat representative has flat terms on the
coefficient sequence site.
Source: Stacks 05V4, 08FC (blueprint: def-sp-projection-reduction-presentation).
Proof: each level of the reduction of a term is isomorphic to its scalar extension, which is
flat because the section presentation has flat terms; a strict system with flat levels is
flat on the sequence site. -/
theorem flatTerms_ordinaryReduction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (P : CochainComplex (Modules l E T) ℤ)
    (hP : FlatRepresentative l E T P) :
    flatTerms.{u + 1, u, u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (systemRing (Scheme.ProEt.topology T) (VaryingRing.coefficients (rings l E) T)
        (VaryingRing.coefficientTransition (rings l E) (transitions l E) T))
      (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj P) := by
  intro p
  let S := ((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P
  refine SheafOfModules.strictSystemToSequence_isFlatOnSite (spCoefficientCommRings l E T)
    (D.equivalence.functor.obj (R.ordinary.obj (S.X p))) fun n ↦ ?_
  let F := (D.scalar (spIntegralReductionScalar l E T R.coefficient n)).model
  have := F.additive
  have hK := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (spIntegralReductionScalar l E T R.coefficient n) S F.E F.obj_eq F.map_eq hP.1
    fun i ↦ (SheafOfModules.isFlatOnSite_iff_exactFunctor_tensorRight (S.X i)).1 (hP.2 i)
  refine SheafOfModules.IsFlatOnSite.of_iso.{u + 1, u, u + 1} ((R.level n).app (S.X p)).symm ?_
  exact (SheafOfModules.isFlatOnSite_iff_exactFunctor_tensorRight (F.E.obj (S.X p))).2 (hK.2 p)

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
