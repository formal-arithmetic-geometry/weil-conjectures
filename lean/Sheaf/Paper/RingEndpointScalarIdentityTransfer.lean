/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

/-! # Universe transfer for endpoint scalar identities -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
attribute [local instance] constructionInclusionShift

def scalarFunctorAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    (S : Scalar.{max u v, max u v} l Ψ a W) :
    C.{u, v} l Ω W (s.stage l) ⥤ C.{u, v} l Ω W (t.stage l) := by
  cases s <;> cases t <;> exact Scalar.functor.{max u v, max u v} S

def scalarRealizationAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    (S : Scalar.{max u v, max u v} l Ψ a W) :
    scalarFunctorAtClosure.{u, v} l Ω Ψ W S ⋙ RingStage.inclusion.{u, v} l Ω W t ≅
      RingStage.inclusion.{u, v} l Ω W s ⋙ pbcDerivedExtend (a.map W) := by
  cases s <;> cases t <;> exact Scalar.realization.{max u v, max u v} S

@[instance_reducible] def scalarCommShiftAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    (S : Scalar.{max u v, max u v} l Ψ a W) :
    (scalarFunctorAtClosure.{u, v} l Ω Ψ W S).CommShift ℤ := by
  cases s <;> cases t <;> exact Scalar.commShift.{max u v, max u v} S

theorem scalarAdditiveAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    (S : Scalar.{max u v, max u v} l Ψ a W) :
    (scalarFunctorAtClosure.{u, v} l Ω Ψ W S).Additive := by
  cases s <;> cases t <;> exact Scalar.additive.{max u v, max u v} S

theorem scalarExactAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    (S : Scalar.{max u v, max u v} l Ψ a W) :
    letI := scalarCommShiftAtClosure.{u, v} l Ω Ψ W S
    (scalarFunctorAtClosure.{u, v} l Ω Ψ W S).IsTriangulated := by
  cases s <;> cases t <;> exact Scalar.exact.{max u v, max u v} S

def scalarAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s t : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    (S : Scalar.{max u v, max u v} l Ψ a W) : Scalar.{u, v} l Ω a W :=
  { functor := scalarFunctorAtClosure.{u, v} l Ω Ψ W S
    realization := scalarRealizationAtClosure.{u, v} l Ω Ψ W S
    commShift := scalarCommShiftAtClosure.{u, v} l Ω Ψ W S
    additive := scalarAdditiveAtClosure.{u, v} l Ω Ψ W S
    exact := scalarExactAtClosure.{u, v} l Ω Ψ W S }

/-- Transfers the multiplication-normalized identity certificate from an equal-universe
closure to the original coefficient universes. This is the normalization substep of
endpoint scalar restriction assembly.
Source: Zheng, Lemma 5.22 and Proposition 5.26
(blueprint: lem-sf-ring-endpoint-scalar-identity-transfer).
-/
theorem scalarIdentityAtClosure
    (Ψ : Type (max u v)) [Field Ψ] [Algebra (Padic l) Ψ] [IsAlgClosure (Padic l) Ψ]
    (W : Scheme.{max u v}) {s : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l)}
    (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _)
    (S : Scalar.{max u v, max u v} l Ψ a W)
    (I : ScalarIdentity.{max u v, max u v} l Ψ h W S) :
    Nonempty (ScalarIdentity.{u, v} l Ω h W (scalarAtClosure.{u, v} l Ω Ψ W S)) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
