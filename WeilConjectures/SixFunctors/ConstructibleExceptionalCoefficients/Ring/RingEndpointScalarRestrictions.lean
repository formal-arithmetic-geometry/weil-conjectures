/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientAssemblyData

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.ExceptionalRingTransportFamily
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.RingEndpointScalarIdentityTransfer

/-! # Endpoint ring scalar restrictions

## Implementation details

The restrictions are constructed at the canonical proper compactification of the identity
of `W`, so they depend only on `W` and not on any operation or compactification supplied by
a caller.

## References

* Zheng, Lemma 5.22 and Propositions 5.24 and 5.26
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
  AlgebraicGeometry.Scheme.completedAdicChange AlgebraicGeometry.Scheme.reductionChange
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.presheafToSheaf
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

attribute [local instance] constructionInclusionShift

private theorem isAlgClosedOfEquiv
    {K L : Type*} [Field K] [Field L] [IsAlgClosed K] (e : K ≃+* L) :
    IsAlgClosed L := by
  refine ⟨fun p ↦ ?_⟩
  have h := (IsAlgClosed.splits (p.map e.symm.toRingHom)).map e.toRingHom
  have he : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    ext n
    simp
  rwa [he] at h

private theorem scalarAtClosure_shift
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) :
    ∀ {s t : RingStage.{max u v} l}
      {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
      (S : Scalar.{max u v, max u v} l Ψ a W),
      (letI := ExceptionalIntegralScalar.inclusionShift l Ψ W s
       letI := ExceptionalIntegralScalar.inclusionShift l Ψ W t
       (Scalar.realization.{max u v, max u v} S).hom.CommShift ℤ) →
      (scalarAtClosure.{u, v} l Ω Ψ W S).realization.hom.CommShift ℤ := by
  intro s t
  cases s <;> cases t <;> intro a S h <;> exact h

private theorem scalarAtClosure_finiteEq
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) :
    ∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      {a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l)}
      (S : Scalar.{max u v, max u v} l Ψ a W),
      (Scalar.functor.{max u v, max u v} S) ⋙
          RingStage.inclusion.{max u v, max u v} l Ψ W (.finite E n) =
        RingStage.inclusion.{max u v, max u v} l Ψ W s ⋙ pbcDerivedExtend (a.map W) →
      (scalarAtClosure.{u, v} l Ω Ψ W S).functor ⋙ RingStage.inclusion.{u, v} l Ω W (.finite E n) =
        RingStage.inclusion.{u, v} l Ω W s ⋙ pbcDerivedExtend (a.map W) := by
  intro s
  cases s <;> intro E n a S h <;> exact h

private theorem scalarAtClosure_finiteNormalized
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) :
    ∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      {a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l)}
      (S : Scalar.{max u v, max u v} l Ψ a W)
      (h : (Scalar.functor.{max u v, max u v} S) ⋙
          RingStage.inclusion.{max u v, max u v} l Ψ W (.finite E n) =
        RingStage.inclusion.{max u v, max u v} l Ψ W s ⋙ pbcDerivedExtend (a.map W)),
      (Scalar.realization.{max u v, max u v} S) = eqToIso h →
      (scalarAtClosure.{u, v} l Ω Ψ W S).realization =
        eqToIso (scalarAtClosure_finiteEq.{u, v} l Ω Ψ W E n S h) := by
  intro s
  cases s <;> intro E n a S h hn <;> exact hn

/-- Endpoint restrictions of allowed derived coefficient extensions, independently of
compactifications and exceptional adjunctions. -/
theorem exists_ring_endpoint_scalar_restrictions
    (D : FiniteFieldDatum.{max u v}) (_hl : l ≠ D.p) (W : Scheme.{max u v})
    [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))] :
    ∃ scalar : ∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)),
      Allowed l a → Scalar.{u, v} l Ω a W,
    ∃ finiteScalar_eq : ∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).functor ⋙ RingStage.inclusion.{u, v} l Ω W (.finite E n) =
        RingStage.inclusion.{u, v} l Ω W s ⋙ pbcDerivedExtend (a.map W),
    (∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).realization = eqToIso (finiteScalar_eq E n a ha)) ∧
    (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier),
      (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).functor ⋙
          RingStage.inclusion.{u, v} l Ω W (.integral L) =
        RingStage.inclusion.{u, v} l Ω W (.integral E) ⋙
          integralScalarExtensionOfUniverses l E.carrier L.carrier i W) ∧
    (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u, v} l Ω W (.integral E)),
      HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).realization.inv.app K)
        ((completedScalarComparison l E.carrier L.carrier i W).app K.obj)) ∧
    (∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a), (scalar a ha).realization.hom.CommShift ℤ) ∧
    (∀ {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a),
      Nonempty (ScalarIdentity.{u, v} l Ω h W (scalar a ha))) := by
  classical
  let Ω' := ULift.{u} Ω
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (Padic l)
  have : IsAlgClosure (Padic l) Ω' :=
    { isAlgClosed := isAlgClosedOfEquiv (ULift.ringEquiv.symm : Ω ≃+* Ω')
      isAlgebraic := Algebra.IsAlgebraic.of_injective
        (ULift.algEquiv (R := Padic l)).toAlgHom ULift.down_injective }
  let c := Compactification.ofIsProper (𝟙 W)
  obtain ⟨operation, left, ⟨tr⟩⟩ :=
    exists_exceptional_ring_transport_family l Ω' D _hl (𝟙 W) c
  obtain ⟨d, _, _⟩ := ExceptionalIntegralScalar.exceptionalIntegralScalarMates_core
    l Ω' D _hl c operation left tr
  let scalar : ∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)),
      Allowed l a → Scalar.{u, v} l Ω a W := fun a ha ↦
    scalarAtClosure.{u, v} l Ω Ω' W (d.scalar a ha true)
  have finite_eq : ∀ {s : RingStage.{max u v} l}
      (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).functor ⋙ RingStage.inclusion.{u, v} l Ω W (.finite E n) =
        RingStage.inclusion.{u, v} l Ω W s ⋙ pbcDerivedExtend (a.map W) := by
    intro s E n a ha
    exact scalarAtClosure_finiteEq.{u, v} l Ω Ω' W E n (d.scalar a ha true)
      (d.finiteScalar_eq E n a ha true)
  refine ⟨scalar, finite_eq, ?_, ?_, ?_, ?_, ?_⟩
  · intro s E n a ha
    exact scalarAtClosure_finiteNormalized.{u, v} l Ω Ω' W E n (d.scalar a ha true)
      (d.finiteScalar_eq E n a ha true) (d.finiteScalar_normalized E n a ha true)
  · intro E L i
    exact d.integralScalar_eq E L i true
  · intro E L i K
    exact d.integralScalar_normalized E L i true K
  · intro s t a ha
    exact scalarAtClosure_shift.{u, v} l Ω Ω' W (d.scalar a ha true) (d.scalarShift a ha true)
  · intro s a h ha
    exact scalarIdentityAtClosure.{u, v} l Ω Ω' W h (d.scalar a ha true)
      (d.scalarIdentity a h ha true)

end WeilConjectures.ConstructibleExceptionalCoefficients
