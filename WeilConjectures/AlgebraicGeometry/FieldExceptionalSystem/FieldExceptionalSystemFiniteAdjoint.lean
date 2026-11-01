/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.FieldExceptionalSystemDomains

/-! # Exceptional coefficient comparison on whole systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), counit transpose
(blueprint: def-sp-field-exceptional-system-finite-adjoint).

Natural-number level n means exponent n+1. All morphisms are in ordinary derived
categories of strict systems, in the dependency's section-preserving coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExceptionalSystem

open FieldShriekSystem
variable (P : PurityFiniteSetting.{u})

/-- Finite exceptional adjunction, with its actual ordinary-etale counit realization.
Source: blueprint (2), det-sp-reduction-exceptional
(blueprint: def-sp-field-exceptional-system-finite-adjoint). -/
structure FiniteAdjoint {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (E : Index P) (n : ℕ) where
  closed : ∀ M : spFiniteConstructibleTorCategory X (SpTowerShriek.R P.coefficients.l E.val n),
    spFiniteConstructibleTor Y (SpTowerShriek.R P.coefficients.l E.val n)
      ((reductionCompactSupport (SpTowerShriek.R P.coefficients.l E.val n) c.i c.g).obj M.obj)
  right : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n) ⥤
    spFiniteConstructibleTorCategory X (SpTowerShriek.R P.coefficients.l E.val n)
  adj : reductionCtfCompactSupport (SpTowerShriek.R P.coefficients.l E.val n) c.i c.g closed ⊣
    right
  realization : ReductionExceptionalRealization (SpTowerShriek.R P.coefficients.l E.val n)
    c.i c.g closed right adj


end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
