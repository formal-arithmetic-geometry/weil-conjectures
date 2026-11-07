/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import Submission.WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Finite proper base change with canonical ring-sheaf coefficients

Source: blueprint theorem 1325; Stacks Project, Pro-etale Cohomology, Section 09C8,
and the finite etale-origin step of Theorem 09C9
(blueprint: thm-weil-pbc-finite-level-proetale).
This is the recorded finite theorem in the normalized ring-sheaf presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (Λ : Type (t + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

variable {X' X Y' Y : Scheme.{t}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

end AlgebraicGeometry.Scheme
