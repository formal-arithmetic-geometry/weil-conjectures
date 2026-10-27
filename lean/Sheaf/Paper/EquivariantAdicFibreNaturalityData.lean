/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.EquivariantAdicFibreRealizationData

/-! # Naturality data for normalized equivariant adic fibre realizations

Source: Bhatt--Scholze Proposition 6.8.4(1), equivariant expansion, steps 10--11
(blueprint: def-sfb-equivariant-adic-fibre-naturality-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.EquivariantAdicFibre
open ContinuousModule

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {l E}

/-- The naturality squares for the two actual sheaf comparisons.
Source: BS Proposition 6.8.4(1), steps 10--11
(blueprint: def-sfb-equivariant-adic-fibre-naturality-data). -/
structure Naturality {B X X' : Scheme.{u}} {u : X ⟶ B} {u' : X' ⟶ B}
    [WeaklyEtale u] [WeaklyEtale u']
    {G G' : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    [Group G'] [IsTopologicalGroup G']
    {a : ProfiniteCoefficientAction X G} {a' : ProfiniteCoefficientAction X' G'}
    {hu : a.act ≫ u = coefficientParameterProjection X G ≫ u}
    {hu' : a'.act ≫ u' = coefficientParameterProjection X' G' ≫ u'}
    {D : FiniteData l E G} {D' : FiniteData l E G'}
    {P : Data B X u G a hu D} {P' : Data B X' u' G' a' hu' D'}
    {r : X' ⟶ X} [WeaklyEtale r] {hr : r ≫ u = u'} {γ : G' →ₜ* G}
    (F : Morphism P P' r hr γ) (R : Realization P) (R' : Realization P')
    extends FibreNaturality F R.algebraic R'.algebraic where
  integralSheafMap : R.integral.object ⟶ R'.integral.object
  integralSheafMap_formula : RepresentsMap R.integral R'.integral
    integralMap integralSheafMap
  rationalSheafMap : R.rational.object ⟶ R'.rational.object
  rationalSheafMap_formula : RepresentsMap R.rational R'.rational rationalMap rationalSheafMap
  integral_square :
    ((cartesianCoefficientLift (ring (Integers l E)).X r).map R.integralIso.hom).hom ≫
      (pullIso (ring (Integers l E)).X R.integral.object r).hom ≫
      ((pull (Integers l E) X').map integralSheafMap).hom =
    refinementArrow (ring (Integers l E)).X r hr F.moduleMap ≫ R'.integralIso.hom.hom
  rational_square :
    ((cartesianCoefficientLift (ring E).X r).map R.rationalIso.hom).hom ≫
      (pullIso (ring E).X R.rational.object r).hom ≫ ((pull E X').map rationalSheafMap).hom =
    refinementArrow (ring E).X r hr ((localize (l := l) (E := E) B).map F.moduleMap) ≫
      R'.rationalIso.hom.hom



end AlgebraicGeometry.ProEtale.EquivariantAdicFibre
