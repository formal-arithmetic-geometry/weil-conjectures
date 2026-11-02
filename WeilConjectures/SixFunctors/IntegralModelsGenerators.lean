/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralTransport
public import WeilConjectures.AlgebraicGeometry.SequenceSiteCompletionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Integral generators and their finite reductions

(1)--(3) (blueprint: det-lem-integral-models-generators).

The generator classes use the existing canonical scalar extension and locally closed
extension by zero. Finite reductions use the total left derived extension of scalars.
Their etale origin is tested through the existing intrinsic finite-coefficient comparison,
after the explicit restriction to constant scalars.
-/

@[expose] public section

set_option autoImplicit false
-- Preserve shared coefficient terms during proof cleanup.
set_option cleanup.letToHave false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale

universe u

namespace AlgebraicGeometry.ProEtale

/-- Convert a condensed ring sheaf to its existing ring object, then pull back to `X`.
Source: blueprint comparison with completed coefficients, notation `Λ_X`
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedCoefficient (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  coefficientRing X
    (Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.SixFunctors

open scoped CategoryTheory.Functor

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

/-- Canonical coefficient specialization used in the integral generator statement.
(1)--(3)
(blueprint: det-lem-integral-models-generators). -/
noncomputable instance integralModel_coefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) :=
  Functor.monObjObj (F := upperStarFromPoint X) Λ

/-- The pulled-back continuous quotient ring retains its commutative ring structure.
Source: blueprint integral generators (3), the finite coefficient identification
(blueprint: det-lem-integral-models-generators). -/
noncomputable instance integralModelFiniteCoefficient_isComm (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsCommMonObj (completedCoefficient X (Profinite.continuousMapRingSheaf A)).X := by
  exact Functor.isCommMonObj_obj (F := upperStarFromPoint X)

end WeilConjectures.SixFunctors
