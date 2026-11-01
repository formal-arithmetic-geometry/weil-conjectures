/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.Adjoints.FieldExceptionalSystemAdjoints

/-! # Exceptional coefficient comparison on whole systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), counit transpose
(blueprint: def-sp-field-exceptional-system-components).

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

/-- The specified whole-system exceptional comparison is literally the adjunction
transpose of scalar extension of the tower counit composed with b inverse.
Source: blueprint (2), defining transpose
(blueprint: def-sp-field-exceptional-system-components). -/
def component (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)
    {E F : Index P} (h : E ≤ F) (K : N P D E Y) :
    (scalar P D a h X).obj ((A.right E).obj K) ⟶
      (A.right F).obj ((scalar P D a h Y).obj K) :=
  (A.adj F).homEquiv _ _ (ObjectProperty.homMk
    ((FieldShriekSystem.iso P D c b h).inv.app ((A.right E).obj K) ≫
      (D.scalars E F h Y).T.map ((A.adj E).counit.app K).hom))

/-- Finite c is the same specified finite counit transpose, including mixed indices.
Source: blueprint (2), det-sp-reduction-exceptional
(blueprint: def-sp-field-exceptional-system-components). -/
def finiteComponent (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)
    {E F : Index P} {n m : ℕ}
    (φ : SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val m)
    (K : spFiniteConstructibleTorCategory Y (SpTowerShriek.R P.coefficients.l E.val n)) :
    (reductionCtfScalar φ X (a.finiteScalar E F n m φ X (.inl rfl))).obj
        ((A.finite E n).right.obj K) ⟶
      (A.finite F m).right.obj
        ((reductionCtfScalar φ Y (a.finiteScalar E F n m φ Y (.inr rfl))).obj K) :=
  (A.finite F m).adj.homEquiv _ _ (ObjectProperty.homMk
    (@inv _ _ _ _ ((reductionDirectImageComparison φ c.i c.g).app
        ((A.finite E n).right.obj K).obj) (A.finiteIso E F n m φ K) ≫
      (scalarExtensionFunctor φ Y).map ((A.finite E n).adj.counit.app K).hom))


end AlgebraicGeometry.ProEtale.FieldExceptionalSystem
