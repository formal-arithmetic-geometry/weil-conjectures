/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices

import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted

/-! # Uniform cohomological bounds on actual quotient representatives

Source: blueprint order 1459 and Stacks Project, Tags 06YL and 06YV.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The uniform interval of the integral constructible category also bounds the
actual quotient complexes of any flat-term K-flat representative.
Source: blueprint order 1459; Stacks Project, Tags 06YL and 06YV
(blueprint: lem-trf-integral-quotient-cohomological-bounds).

Proof: choose the single interval [p,r] in sfIntegralConstructible. The ordinary
extension of scalars applied termwise to P computes derived reduction because P
is K-flat with flat terms. Its localization counit is therefore an isomorphism,
naturally with respect to the given representative isomorphism q. Transport the
cohomological support bound across this derived isomorphism. Scalar restriction
is exact, so the same bound holds for the unrestricted quotient complex. Vanishing
of homology below p and above r is exactly IsGE p and IsLE r. This uses only
cohomological bounds; no termwise bound or finite Tor amplitude is asserted. -/
theorem integralQuotientCohomologicalBounds
    (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)]
    (M : DerivedCategory (integralTowerModules l E T))
    (hM : sfIntegralConstructible l E T M)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory)
    (q : DerivedCategory.Q.obj P.obj ≅ M) :
    ∃ p r : ℤ, p ≤ r ∧ ∀ n : ℕ,
      CochainComplex.IsGE ((unrestrictedIntegralComplexFunctor l E T n).obj P.obj) p ∧
        CochainComplex.IsLE ((unrestrictedIntegralComplexFunctor l E T n).obj P.obj) r := by
  classical
  obtain ⟨p, r, hpr, hbound⟩ := hM.2
  refine ⟨p, r, hpr, ?_⟩
  intro n
  let K := (unrestrictedIntegralFiniteComplex.{u, u} l E T n).obj P.obj
  let N := (scalarReductionDerivedExtension.{u, u} l E T n).obj M
  let G := scalarReductionRestriction.{u, u} l E T n
  let e : N ≅ DerivedCategory.Q.obj K :=
    (scalarReductionDerivedExtension.{u, u} l E T n).mapIso q.symm ≪≫
      unrestrictedTowerResolutionIso.{u, u} l E T n (𝟙 P.obj)
        ⟨inferInstance, P.property.1⟩
  have hz (i : ℤ) (hi : i < p ∨ r < i) : IsZero (K.homology i) := by
    have hn : IsZero ((DerivedCategory.homologyFunctor _ i).obj N) := by
      by_contra hh
      have hb := (hbound n).2 hh
      rcases hi with hi | hi
      · exact (not_le_of_gt hi) hb.1
      · exact (not_le_of_gt hi) hb.2
    exact hn.of_iso
      (((DerivedCategory.homologyFunctor _ i).mapIso e) ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app K).symm
  have hex (i : ℤ) (hi : i < p ∨ r < i) :
      HomologicalComplex.ExactAt ((unrestrictedIntegralComplexFunctor.{u, u}
        l E T n).obj P.obj) i := by
    have hK : K.ExactAt i :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hz i hi)
    change ((K.sc i).map G).Exact
    exact hK.map G
  exact ⟨(CochainComplex.isGE_iff _ _).2 (fun i hi ↦ hex i (Or.inl hi)),
    (CochainComplex.isLE_iff _ _).2 (fun i hi ↦ hex i (Or.inr hi))⟩

end WeilConjectures
