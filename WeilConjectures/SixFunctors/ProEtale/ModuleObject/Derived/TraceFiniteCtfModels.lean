/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel

/-! # Intrinsic and constant-model Dctf for finite coefficients

Source: latest blueprint, section calculation in Step 3(d) of
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/
lem-trf-trace-class-diagonal-pairing.proof.md,
and the finite-coefficient constructibility convention.
(blueprint: lem-trf-finite-ctf-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The intrinsic Dctf test and the supplied constant-model Dctf test agree for a finite ring.
Source: finite-coefficient constructibility convention used in the section calculation,
Step 3(d) (blueprint: lem-trf-finite-ctf-models).

Proof: the coefficient ring pulled back from the point is the constant finite ring sheaf.
On a local finite presentation, finitely many matrix entries are sections of this constant
ring; refine the pro-etale cover so all those entries are constant. Its cokernel is then
the scalar extension of a finitely presented A-module. Conversely scalar extension of a
finite presentation is locally finitely presented. Apply this equivalence on each stratum
of a finite constructible stratification. The Noetherian hypothesis supplies qcqs, so the
finite-stratification branch is the one used by the constant-model predicate. Thus the
two sheaf constructibility tests agree. Apply the equivalence to every cohomology sheaf,
retaining the identical boundedness test and the identical ordinary finite-Tor test.
-/
theorem finite_ctf_models
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] (X : Scheme.{u}) [IsNoetherian X] :
    condensedConstructibleFiniteTor (Profinite.continuousMapRingObj.{u} A) X =
      constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} A) X ⊓
        _root_.DerivedCategory.finiteTorAmplitude _ := by
  sorry

/-- The identity-on-objects and identity-on-morphisms inclusion into constant-model Dctf.
Source: the same finite coefficient comparison (blueprint: lem-trf-finite-ctf-models). -/
def finiteCtfToConstantModels
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
    [DiscreteTopology A] [IsTopologicalRing A] (X : Scheme.{u}) [IsNoetherian X] :
    CondensedConstructibleFiniteTor (Profinite.continuousMapRingObj.{u} A) X ⥤
      ConstantModelConstructibleFiniteTor (Profinite.continuousMapRingObj.{u} A) X :=
  ObjectProperty.ιOfLE (le_of_eq (finite_ctf_models A X))

end AlgebraicGeometry.ProEtale.CondensedRing
