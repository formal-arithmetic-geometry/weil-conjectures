/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.EquivariantAdicFibreCoordinates

/-! # Normalized equivariant adic realization and naturality data

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(1), equivariant expansion
(blueprint: def-sfb-equivariant-adic-fibre-realization-data).
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

/-- Integral and rational reconstruction, with the given finite projections and actual descent.
The comparison on integral sections is fixed by the actual localization unit.
Source: BS Proposition 6.8.4(1), expansion steps 6--9
(blueprint: def-sfb-equivariant-adic-fibre-realization-data). -/
structure Comparison {B X : Scheme.{u}} {u : X ⟶ B} [WeaklyEtale u]
    {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    {a : ProfiniteCoefficientAction X G}
    {hu : a.act ≫ u = coefficientParameterProjection X G ≫ u}
    {D : FiniteData l E G} (P : Data B X u G a hu D) where
  algebraic : Algebraic D
  integral : Model (Integers l E) (Fibre D)
  rational : Model E (Rational D)
  integralIso : (cartesianCoefficientLift (ring (Integers l E)).X u).obj P.module ≅
    (pull (Integers l E) X).obj integral.object
  rationalIso : (cartesianCoefficientLift (ring E).X u).obj
    ((localize (l := l) (E := E) B).obj P.module) ≅ (pull E X).obj rational.object
  reduction : ∀ n, integral.object ⟶ (P.finiteModel n).object
  reduction_formula : ∀ n, RepresentsMap integral (P.finiteModel n)
    (projection D n) (reduction n)
  reduction_normalization : ∀ n,
    integralIso.hom ≫ (pull (Integers l E) X).map (reduction n) =
      (cartesianCoefficientLift (ring (Integers l E)).X u).map (P.quotientMap n) ≫
        (P.phi n).hom

/-- The normalized comparisons, full descent actions, and actual localization unit square.
Source: BS Proposition 6.8.4(1), steps 6--9
(blueprint: def-sfb-equivariant-adic-fibre-realization-data). -/
structure Realization {B X : Scheme.{u}} {u : X ⟶ B} [WeaklyEtale u]
    {G : Profinite.{u}} [Group G] [IsTopologicalGroup G]
    {a : ProfiniteCoefficientAction X G}
    {hu : a.act ≫ u = coefficientParameterProjection X G ≫ u}
    {D : FiniteData l E G} (P : Data B X u G a hu D) extends Comparison P where
  integral_action : HasDescentAction (ring (Integers l E)).X a.act u hu P.module
    integral.object (integral.scheme _) integralIso
    (fun g q ↦ algebraic.action g q)
  rational_action : HasDescentAction (ring E).X a.act u hu
    ((localize (l := l) (E := E) B).obj P.module)
    rational.object (rational.scheme _) rationalIso (fun g m ↦ algebraic.rho g m)
  inclusion : integral.object.X ⟶ rational.object.X
  inclusion_formula : ∀ (S : Profinite.{u})
    (v : integral.object.X.obj.obj (op S)) (s : S),
    (rational.point.hom.app (op S) (inclusion.hom.app (op S) v)).down s =
      (1 : E) ⊗ₜ[Integers l E] (integral.point.hom.app (op S) v).down s
  localization_normalization :
    integralIso.hom.hom ≫
      (pointUnderlying (ring (Integers l E)).X integral.object X).hom ≫
      (upperStarFromPoint X).map inclusion =
    (liftUnderlying (ring (Integers l E)).X u P.module).hom ≫
      (upperStar Ab.{u + 1} u).map
        (Mod.extendUnitHom (schemeCoefficientMap (l := l) (E := E) B) P.module) ≫
      (liftUnderlying (ring E).X u ((localize (l := l) (E := E) B).obj P.module)).inv ≫
      rationalIso.hom.hom ≫ (pointUnderlying (ring E).X rational.object X).hom


end AlgebraicGeometry.ProEtale.EquivariantAdicFibre
