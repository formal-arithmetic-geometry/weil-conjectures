/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Coefficient dual on the geometric fibre

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
`def-pod-coefficient-dual-on-x.md` (blueprint: def-pod-coefficient-dual-on-x).

The coefficient ring is a commutative condensed ring, pulled back to the small
pro-etale site of the fixed geometric fibre. Both constructions use the ambient
ordinary derived category of internal modules over that ring object. In particular,
no assertion that the dual remains bounded constructible or of finite Tor amplitude
is part of this definition. The formulas apply to each of the four coefficient
rings in the Poincare conventions.

## Main definitions

* `CondensedPoincareDualityConventions.coefficientDualOnX`: internal Hom into the unit.
* `CondensedPoincareDualityConventions.coefficientEvaluationOnX`: the tensor-Hom counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.ProEtale Opposite

namespace WeilConjectures.CondensedPoincareDualityConventions

/-- The coefficient dual `K^vee = RHom_{Λ_X}(K, Λ_X)` of a bounded constructible
finite-Tor complex. The unit is the pulled-back coefficient ring as a module over
itself, placed in degree zero. The internal Hom is that of the relative derived
tensor structure, with no closure assertion about its value.
Source: blueprint part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
def-pod-coefficient-dual-on-x.md,
coefficient-dual formula (blueprint: def-pod-coefficient-dual-on-x). -/
def coefficientDualOnX (P : CondensedPoincareDualityConventions.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : ConstantModelConstructibleFiniteTor Λ P.X) :
    DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology P.X) Ab.{u + 1})
      (condensedRingObj Λ P.X)) :=
  ((CondensedRing.derivedHom Λ P.X).obj (op K.obj)).obj (𝟙_ _)

/-- The canonical evaluation `K ⊗^L_{Λ_X} K^vee → Λ_X`, in the displayed factor
order. This is the counit at the coefficient unit of the existing adjunction
`K ⊗^L_{Λ_X} -` left adjoint to `RHom_{Λ_X}(K, -)`.
Source: blueprint part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/sk-thm-sf-package/
def-pod-coefficient-dual-on-x.md,
evaluation formula (blueprint: def-pod-coefficient-dual-on-x). -/
def coefficientEvaluationOnX (P : CondensedPoincareDualityConventions.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (K : ConstantModelConstructibleFiniteTor Λ P.X) :
    ((CondensedRing.derivedTensor Λ P.X).obj K.obj).obj (P.coefficientDualOnX Λ K) ⟶
      𝟙_ (DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology P.X) Ab.{u + 1})
        (condensedRingObj Λ P.X))) :=
  (CondensedRing.derivedTensorHomAdjunction Λ K.obj).counit.app (𝟙_ _)

end WeilConjectures.CondensedPoincareDualityConventions
