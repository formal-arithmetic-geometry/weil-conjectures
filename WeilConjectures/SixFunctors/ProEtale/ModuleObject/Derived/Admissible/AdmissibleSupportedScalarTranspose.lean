/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleSupportedHom

/-! # Faithfulness of the supported integral scalar transpose

Source: current blueprint lem-pur-divisor-class.proof.md (b), coefficient-extension
paragraph; signed-divisor-coefficient-change proof Step 1.
(blueprint: lem-pur-supported-scalar-transpose-injective). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open AlgebraicGeometry
attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj

namespace AlgebraicGeometry.ProEtale.CondensedRing.Admissible

/-- Evaluation at supported integral one detects module Ext classes with any target.
Source: the free/forgetful scalar adjunction and closed tensor projection in
signed-divisor-coefficient-change Step 1; current blueprint divisor-class proof (b).
(blueprint: lem-pur-supported-scalar-transpose-injective).
Proof: write Q = i_* Z_D. Closed tensor projection identifies the derived free
Lambda-module on Q with i_* Lambda_D. The integral sheaf Q is flat: inverse
image to D gives Z_D and inverse image to its open complement gives zero;
exact monoidal inverse images jointly detect flatness. The derived free-module
comparison is therefore computed on the single complex Q[0]. Its ordinary
unit is exactly supportedGenerator, since the closed projection is normalized
by the tensor unit and counit and hence sends one to one. The derived
free/forgetful Hom equivalence consequently sends an Ext class c to the
forgetful image of c precomposed with that generator. This is a bijection, in
particular injective, in every degree. This argument includes empty support,
torsion coefficients and the zero ring and assumes no flatness of Lambda over Z. -/
theorem supportedScalarTranspose_injective
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D X : Scheme.{u}} [IsLocallyNoetherian X]
    (i : D ⟶ X) [IsClosedImmersion i] (M : Modules Λ X) (n : ℕ) :
    letI : HasExt.{u + 2} (Modules Λ X) := HasExt.standard _
    Function.Injective (fun c : Abelian.Ext.{u + 2} (source Λ i) M n ↦
      ((Ext.mk₀ (supportedGenerator Λ i)).comp
        (c.mapExactFunctor (Mod.forget (condensedRingObj Λ.X X))) (zero_add n) :
        Abelian.Ext.{u + 1} _ M.X n)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.Admissible
