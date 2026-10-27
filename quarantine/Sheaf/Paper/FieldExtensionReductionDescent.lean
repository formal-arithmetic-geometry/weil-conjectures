/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.FieldExtensionReductionLimits

/-! # Canonical scalar comparison in reduction coordinates

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
/-- The canonical reduction identity is unchanged by the chosen presentations of
completed coefficient rings and strict systems. It applies to any scheme.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (1),
the displayed reduction identity and its quotient transitions
(blueprint: lem-sp-field-extension-reduction-descent).

Proof: identify each presented completed ring with the inverse limit of its finite
quotients by the coefficient projection equations. For the inclusion E to F the
map on sections is the inverse limit of the quotient inclusions. The two scalar
functors are identified on pure tensors by multiplication; the inverse inserts one.
Use these maps for IntegralCoordinates and conjugate by the section-preserving
system equivalences for SystemCoordinates. Finite-free completed comparison identifies
ordinary extension with integralScalarExtension on complete inputs. Composing its
inverse with the ordinary derived comparison gives integral; cancellation gives
integral_normalized. Apply reduction and compose with the multiplication comparison
of entire systems and the coordinate comparison. This gives reduction and exactly
reduction_normalized. Multiplication and insertion of one commute with each quotient
map on a single K-flat representative, so these are arrows of whole systems. -/
theorem field_extension_reduction_descent (P : PurityFiniteSetting.{u})
    (D : FieldShriekSystem.Models P) (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (T : Scheme.{u})
    (RA : SpReductionTower P.coefficients.l E.val T ((D.coordinates E).abelian T))
    (RB : SpReductionTower P.coefficients.l F.val T ((D.coordinates F).abelian T)) :
    Nonempty (Reduction P D E F h T RA RB) := by sorry

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
