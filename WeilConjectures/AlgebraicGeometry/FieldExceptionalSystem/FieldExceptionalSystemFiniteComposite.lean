/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.FieldExceptionalSystemComponents

/-! # Exceptional coefficient comparison on whole systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), counit transpose
(blueprint: def-sp-field-exceptional-system-finite-composite).

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

/-- The two finite exceptional mates pasted using the canonical balanced associator.
Source: blueprint (2), both mixed paths
(blueprint: def-sp-field-exceptional-system-finite-composite). -/
def finiteComposite (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)
    {E F L : Index P} {n m r : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (ψ : SpTowerShriek.R P.coefficients.l F.val m →+*
      SpTowerShriek.R P.coefficients.l L.val r)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)) :=
  (scalarExtensionFunctor_composition φ ψ X).inv.app ((A.finite E n).right.obj K).obj ≫
    (scalarExtensionFunctor ψ X).map (finiteComponent P D c b a A φ K).hom ≫
    (finiteComponent P D c b a A ψ
      ((reductionCtfScalar φ Y (a.finiteScalar E F n m φ Y (.inr rfl))).obj K)).hom ≫
    ((A.finite L r).right.map (ObjectProperty.homMk
      (Y := (reductionCtfScalar (ψ.comp φ) Y
        (a.finiteScalar E L n r (ψ.comp φ) Y (.inr rfl))).obj K)
      ((scalarExtensionFunctor_composition φ ψ Y).hom.app K.obj))).hom


end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
