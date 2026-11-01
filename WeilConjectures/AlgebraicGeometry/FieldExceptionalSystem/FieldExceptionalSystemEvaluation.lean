/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.FieldExceptionalSystemFiniteComposite

/-! # Exceptional coefficient comparison on whole systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), counit transpose
(blueprint: def-sp-field-exceptional-system-evaluation).

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

/-- Evaluation of the source of c, with the actual scalar and right-adjoint coordinates.
Source: blueprint (2), finite evaluation
(blueprint: def-sp-field-exceptional-system-evaluation). -/
def sourceEvaluation (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)
    {E F : Index P} (h : E ≤ F) (n : ℕ) (K : N P D E Y) :=
  (b.scalarEvaluation E F h X n).iso.app ((A.right E).obj K).obj ≪≫
    (scalarExtensionFunctor ((D.coefficients E F h).quotient n) X).mapIso
      ((spFiniteConstructibleTor X (SpTowerShriek.R P.coefficients.l E.val n)).ι.mapIso
        ((A.evaluation E n).app K))

/-- Evaluation of the target of c, with the actual scalar and right-adjoint coordinates.
Source: blueprint (2), finite evaluation
(blueprint: def-sp-field-exceptional-system-evaluation). -/
def targetEvaluation (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)
    {E F : Index P} (h : E ≤ F) (n : ℕ) (K : N P D E Y) :=
  (spFiniteConstructibleTor X (SpTowerShriek.R P.coefficients.l F.val n)).ι.mapIso
      ((A.evaluation F n).app ((scalar P D a h Y).obj K)) ≪≫
    (spFiniteConstructibleTor X (SpTowerShriek.R P.coefficients.l F.val n)).ι.mapIso
      ((A.finite F n).right.mapIso (ObjectProperty.isoMk _
        (Y := (reductionCtfScalar ((D.coefficients E F h).quotient n) Y
          (a.finiteScalar E F n n ((D.coefficients E F h).quotient n) Y (.inr rfl))).obj
            ((level P D a E Y n).obj K))
        ((b.scalarEvaluation E F h Y n).iso.app K.obj)))


end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
