/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FourierAdicArtinSchreier
public import Mathlib.FieldTheory.Finite.Trace

/-! # The degree-q Artin--Schreier sheaf with adic coefficients

Source: main-20261015, sec-fourier-transform/sk-def-as/_section.md
(blueprint: sk-def-as).
The general discrete idempotent-image definition is reexported unchanged. Its integral
realization below uses the specified degree-q cover, including on the empty scheme.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- Enumerate the already fixed finite field, without changing it.
Source: sk-def-as, degree q (blueprint: sk-def-as). -/
@[instance_reducible]
def fourierBaseFintype (F : FourierSetting.{u}) : Fintype F.field.k₀ := Fintype.ofFinite _

/-- The canonical prime-field algebra on the fixed base field.
Source: sk-def-as and sk-def-fourier-set (blueprint: sk-def-as). -/
@[instance_reducible]
def fourierPrimeAlgebra (F : FourierSetting.{u}) : Algebra (ZMod F.field.p) F.field.k₀ :=
  letI := fourierBaseFintype F
  letI : CharP F.field.k₀ F.field.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := F.field.k₀)).symm.trans
      (F.field.card_base.trans F.field.cardinality_eq))
  (ZMod.castHom (dvd_refl F.field.p) F.field.k₀).toAlgebra

/-- The integral trace character, using the dependency's actual integral lift.
Source: sk-def-as, psi=Psi composed with trace (blueprint: sk-def-as). -/
def fourierIntegralTraceCharacter (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) :=
  letI := fourierPrimeAlgebra F
  (fourierIntegralCharacter F Ψ).compAddMonoidHom
    (Algebra.trace (ZMod F.field.p) F.field.k₀).toAddMonoidHom

/-- The canonical inverse of q=p^r in the integral coefficients.
Source: sk-def-as, coefficient 1/q (blueprint: sk-def-as). -/
@[instance_reducible]
def fourierIntegerCardInvertible (F : FourierSetting.{u}) :
    Invertible (@Fintype.card F.field.k₀ (fourierBaseFintype F) : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers F.coefficients.l (fourierCoefficient F))) :=
  letI := fourierBaseFintype F
  Eq.mp (congrArg (fun n : ℕ ↦ Invertible (n : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers F.coefficients.l (fourierCoefficient F))))
    ((F.field.cardinality_eq.symm.trans F.field.card_base.symm).trans
      (Nat.card_eq_fintype_card (α := F.field.k₀))))
    (Eq.mp (congrArg Invertible (Nat.cast_pow F.field.p F.field.a).symm)
      (@invertiblePow _ _ _ (fourierIntegerPrimeInvertible F) F.field.a))

/-- The degree-q idempotent-image sheaf with integral trace character.
No condition on the characteristic of the ring of global sections is imposed.
Source: sk-def-as, pullback of the universal degree-q summand (blueprint: sk-def-as). -/
def fourierEtaleCharacterOf (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X, ⊤)) :=
  letI := fourierBaseFintype F
  letI := fourierIntegerCardInvertible F
  Etale.artinSchreierSheafOf X (fourierIntegralTraceCharacter F Ψ) f

/-- Completed integral degree-q realization, in sheaf degree zero.
Source: sk-def-as with the standing adic convention (blueprint: sk-def-as). -/
def fourierIntegralCharacterOf (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X, ⊤)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (fourierCompletedRealization F.coefficients.l (fourierCoefficient F) X
      (fourierEtaleCharacterOf F X Ψ f))

/-- This explicit completed integral character belongs to the adic constructible category.
Source: sk-def-as and sk-def-fourier-set (blueprint: sk-def-as).
Proof: the degree-q finite etale torsor trivializes the idempotent image by evaluation
at a root. At each coefficient quotient this is free of rank one, compatibly with
transition maps. Completion is the completed free line on this cover, is derived
complete, and has constructible reductions uniformly in degree zero. These properties
descend along the finite etale cover; the empty scheme is the empty-cover case. -/
theorem fourierIntegralCharacterOf_mem (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))] [IsNoetherian X]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X, ⊤)) :
    sfIntegralConstructible F.coefficients.l (fourierCoefficient F) X
      (fourierIntegralCharacterOf F X Ψ f) := by
  sorry

/-- The actual degree-q character sheaf at the specified finite coefficient stage.
It is completed, rationalized, and included in the common-stage adic category.
Source: sk-def-as and its coefficient convention (blueprint: sk-def-as). -/
def fourierCharacterOf (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of F.field.k₀))] [IsNoetherian X]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (f : Γ(X, ⊤)) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar X :=
  ⟨fourierCoefficientStage F,
    (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F) X).obj
      ⟨fourierIntegralCharacterOf F X Ψ f, fourierIntegralCharacterOf_mem F X Ψ f⟩⟩

end WeilConjectures
