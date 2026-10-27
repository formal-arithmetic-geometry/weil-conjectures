/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.ComponentLiftSectionDefs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Paper.CondensedFiniteFreeTensorExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-! # Finite-free duality for component-lift coefficients

Source: Hemo--Richarz--Scholbach, Definition 3.3, Lemma 4.1 and Proposition 4.3(3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite locally free modules have locally finite free duals, K-flat single complexes,
and the induced derived duality pairing.

Source: HRS Definition 3.3; Stacks 08JJ, lemma-dual-perfect-complex
(blueprint: lem-sfb-component-lift-finite-free-duality).

Proof: take the internal module Hom from L to the regular coefficient module. On a
finite-free trivializing slice it is the coordinate dual of the same finite rank,
hence is lisse. Evaluation sends phi tensor x to phi(x). Coevaluation sends 1 to
sum_i e_i tensor e_i^*. For a change of bases with inverse matrices A,B, the coefficient
of e_i tensor e_k^* in this sum is sum_j A_ij B_jk = delta_ik. The local coevaluations
therefore glue, and the two triangle composites are the usual coordinate expansions
of x and phi. Tensor with either locally free module is exact: finite-limit preservation
is condensed_locally_free_tensor_preservesFiniteLimits and tensor preserves cokernels.
Consequently tensor with an acyclic complex is acyclic, which gives K-flatness of the
two single complexes. Their terms are flat, so K-flat tensor descent computes derived
tensor by these single complexes and transports the two triangle identities. The zero
rank case has empty sums, and varying ranks are handled separately on each slice. -/
theorem component_lift_finite_free_duality
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (T : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
    (hL : IsLisseCoefficientModule Λ.X L) : ComponentLiftLisseFacts Λ T L := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
