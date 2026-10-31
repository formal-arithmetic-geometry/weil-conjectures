/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralHeartLocalModelData
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Flatness of integral continuous sections over constant scalars

Source: the integral-heart proof and the torsion-free flatness criterion over a PID.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.InternalAbelianSheafModule
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

private theorem integralHeartSection_mul (S : Profinite.{u}ᵒᵖ)
    (a b : (integralHeartPointRing.{u} ℓ E).obj.obj S) :
    let := SmallAdicCompletion.Coefficients.fieldNorm.{u} ℓ E
    (show ULift.{u + 1} C(S.unop, SmallAdicCompletion.Coefficients.integers.{u} ℓ E)
      from a * b) =
    (show ULift.{u + 1} C(S.unop, SmallAdicCompletion.Coefficients.integers.{u} ℓ E)
      from a) *
    (show ULift.{u + 1} C(S.unop, SmallAdicCompletion.Coefficients.integers.{u} ℓ E)
      from b) := by
  let := SmallAdicCompletion.Coefficients.fieldNorm.{u} ℓ E
  let J := coherentTopology Profinite.{u}
  let R := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let P := Profinite.continuousCoefficientRingSheaf
    (SmallAdicCompletion.Coefficients.integers.{u} ℓ E)
  have hmon : (sheafToPresheaf J AddCommGrpCat.{u + 1}).monObjObj R =
      P.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj R.obj := P.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul R
  change (((sheafToPresheaf J AddCommGrpCat.{u + 1}).monObjObj R).mul.app S).hom
    (a ⊗ₜ[ℤ] b) = _
  have hm := congrArg (fun m : MonObj R.obj ↦ m.mul) hmon
  rw [hm]
  rfl

/-- Every continuous integral section ring is flat over the lifted coefficient DVR.

Source: blueprint integral-heart local-model proof, first paragraph; Serre, Local Fields,
Chapter II, §2, Proposition 3, and Mathlib's torsion-free flatness criterion over a PID.
(blueprint: lem-integral-heart-section-flat).

Proof: the coefficient-integers theorem supplies a principal ideal domain, and its
ring equivalence with its lift transports that property. The reconstructed section
multiplication is the original pointwise multiplication, by compatibility of the
sheafification tensor comparison with multiplication. Consequently the scalar action
is multiplication by the constant function. If a nonzero scalar annihilates a section,
evaluate at each point and cancel in the integral domain of coefficients. Thus the
section module is torsion-free and hence flat over the PID. On an empty test space
the same pointwise argument proves equality of the unique functions. -/
theorem integralHeartConstantMap_flat (S : Profinite.{u}ᵒᵖ) :
    ((integralHeartConstantMap.{u} ℓ E).app S).hom.Flat := by
  let := SmallAdicCompletion.Coefficients.fieldNorm.{u} ℓ E
  let O := SmallAdicCompletion.Coefficients.integers.{u} ℓ E
  let A := integralHeartScalars.{u} ℓ E
  let B := (sectionRingSheaf (coherentTopology Profinite.{u})
    (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)).obj.obj S
  let : CommRing B := CommRingCat.commRing B
  let f : A →+* B := ((integralHeartConstantMap.{u} ℓ E).app S).hom
  have hpid : IsPrincipalIdealRing O :=
    (Padic.extension_integers_dvr ℓ (SmallAdicCompletion.Coefficients.field.{u} ℓ E)
      (Padic.coefficientExtensionAbsoluteValue ℓ
        (SmallAdicCompletion.Coefficients.field.{u} ℓ E))
      (spectralNorm_extends (K := Padic ℓ)
        (L := SmallAdicCompletion.Coefficients.field.{u} ℓ E))).choose_spec.choose_spec
          |>.2.2.2.2.2.2.2.2.1
  let := hpid
  let : IsPrincipalIdealRing A :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv.symm : O ≃+* A).toRingHom
      ULift.ringEquiv.symm.surjective
  let : IsDomain A := (ULift.ringEquiv : A ≃+* O).toMulEquiv.isDomain O
  let : Module A B := Module.compHom B f
  have hs (a : A) (s : B) (x : S.unop) :
      (show ULift.{u + 1} C(S.unop, O) from a • s).down x = a.down * s.down x := by
    change (show ULift.{u + 1} C(S.unop, O) from f a * s).down x = _
    rw [integralHeartSection_mul]
    rfl
  have : Module.IsTorsionFree A B := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a s h
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      apply ULift.ext
      apply ContinuousMap.ext
      intro x
      have hx : a.down * s.down x = 0 := by
        rw [← hs]
        exact congrArg (fun t : B ↦ t.down x) h
      have ha' : a.down ≠ 0 := by
        intro hz
        exact ha (ULift.ext a 0 hz)
      exact (mul_eq_zero.mp hx).resolve_left ha'
  change @Module.Flat A B _ _ (Module.compHom B f)
  infer_instance

end AlgebraicGeometry.ProEtale
