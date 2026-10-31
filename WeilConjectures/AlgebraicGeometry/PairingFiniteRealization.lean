/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-! # Normalized finite tensor coordinates for the pairing

Source: main-20261015, sec-poincare-duality/sk-def-pairing-data/_section.md,
first displayed composite; Stacks Tags 00YV, 0GMW and 06YN.
(blueprint: def-pod-pairing-tensor-generators).
The comparison is determined on every K-flat representative by its value on
local pure tensors, including the signed total differential.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m : ℕ)

/-- The recorded realization equivalence at the positive coefficient level.
Source: Stacks 00YV (blueprint: def-pod-pairing-tensor-generators). -/
def pairingRealizationEquivalence :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))
  sfIntrinsicModuleEquivalence X (Padic.coefficientExtensionRing l E (m + 1))

/-- Additivity of the specified realization, inherited from its exact equivalence.
Source: Stacks 00YV (blueprint: def-pod-pairing-tensor-generators). -/
instance pairingRealization_additive :
    (pairingRealizationEquivalence l E X m).functor.Additive :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))
  inferInstanceAs (sfIntrinsicModuleEquivalence X
    (Padic.coefficientExtensionRing l E (m + 1))).functor.Additive

/-- Additivity of the inverse equivalence.
Source: Stacks 00YV (blueprint: def-pod-pairing-tensor-generators). -/
instance pairingRealization_inverse_additive :
    (pairingRealizationEquivalence l E X m).inverse.Additive :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))
  inferInstanceAs (sfIntrinsicModuleEquivalence X
    (Padic.coefficientExtensionRing l E (m + 1))).inverse.Additive

/-- Its exact derived equivalence, with the coefficient finiteness supplied.
Source: Stacks 00YV (blueprint: def-pod-pairing-tensor-generators). -/
def pairingDerivedRealization := (pairingRealizationEquivalence l E X m).mapDerivedCategory

/-- The scalar-unit section of the same realization.
Source: Stacks 00YV (blueprint: def-pod-pairing-tensor-generators). -/
def pairingRealizationSection
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))))
    (U : X.ProEtᵒᵖ) (x : M.obj.obj U) :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))
  sfIntrinsicRealizationUnit X (Padic.coefficientExtensionRing l E (m + 1)) M U x

/-- Fixed-scalar complexes before the canonical intrinsic realization.
Source: the finite coefficient convention
(blueprint: def-pod-pairing-tensor-generators). -/
abbrev pairingFixedComplex := CochainComplex (Sheaf (ProEt.topology X)
  (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))))) ℤ

/-- The exact ordinary realization applied termwise, with no chosen tensor data.
Source: Stacks 00YV (blueprint: def-pod-pairing-tensor-generators). -/
def pairingRealizationComplex :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))
  ((pairingRealizationEquivalence l E X m).functor).mapHomologicalComplex (.up ℤ)

end WeilConjectures

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m : ℕ)

/-- Countable coproducts in the fixed-scalar sheaf category, obtained by shrinking
its Grothendieck coproducts. Source: Stacks 06YN
(blueprint: def-pod-pairing-tensor-generators). -/
instance pairingFixedCountableColimits : HasColimitsOfSize.{0, 0}
    (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (m + 1))))) := by
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (m + 1))))) :=
    IsGrothendieckAbelian.hasColimits _
  exact hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _

/-- Total tensor exists in each degree by the countable coproduct just fixed.
Source: Stacks 06YN (blueprint: def-pod-pairing-tensor-generators). -/
instance pairingFixedTensorTotal (P Q : pairingFixedComplex l E X m) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor _) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (pairingFixedCountableColimits l E X m) _ _) _

set_option maxHeartbeats 200000 in
-- Tensor-total section evaluation uses both sheaf monoidal structures.
/-- A fixed-scalar pure tensor in one summand of the signed total complex.
Source: Stacks 06YN (blueprint: def-pod-pairing-tensor-generators). -/
def pairingFixedTensorGenerator (P Q : pairingFixedComplex l E X m)
    (p q k : ℤ) (h : p + q = k) (U : X.ProEtᵒᵖ)
    (x : (P.X p).obj.obj U) (y : (Q.X q).obj.obj U) :
    ((P ⊗ Q).X k).obj.obj U :=
  (HomologicalComplex.ιTensorObj P Q p q k h).hom.app U
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (m + 1))))) (P.X p) (Q.X q)).app U
      (x ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1))] y))

end WeilConjectures
