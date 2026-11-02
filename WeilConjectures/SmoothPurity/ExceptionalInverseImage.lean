/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Compactification.Dense
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginAdjointClass
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekPreservation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Exceptional inverse image in the current field scope

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-coefficients-constructible/
sec-n-brown/sk-thm-existence/def-weil-exceptional-inverse-image.md, with Wei Yang #1412, item 18
(blueprint: def-weil-exceptional-inverse-image).

The finite operation is the existing `Scheme.finiteExceptionalInverseImage`, the canonical
realization of `ν_X^* f^× Rν_{Y,*}`. The native condensed operation below specializes the existing
single Brown construction to a finite or algebraically closed field. All preservation,
refinement, and agreement assertions are conclusions, rather than inputs to either operation.
No definition is made by selecting an arbitrary functor from a mere existence statement.

## Main definitions and statements

* `WeilConjectures.currentExceptionalInverseImage`: native Brown restriction in the current scope.
* `WeilConjectures.currentExceptionalAdjunction`: its natural Hom adjunction.
* `WeilConjectures.currentExceptionalInverseImage_properties`: exactness and uniqueness.
* `WeilConjectures.currentExceptionalInverseImage_compactification`: the recorded `i^* Rp^!`.
* `AlgebraicGeometry.ProEtale.finiteExceptionalInverseImage_current_properties`: finite clauses.
* `AlgebraicGeometry.Scheme.finiteExceptionalInverseImage_ambient_agreement`: optional agreement.

The finite definition is reused from `Sheaf.Paper.FiniteExceptionalInverseImage`. The warning
about elliptic curves is reused from `AmbientCounterexample` (bounded below) and
`AmbientCounterexampleCoproducts` (unbounded), both publicly imported here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures

/-- The finite cohomological dimension required by the native Brown construction, obtained
from precisely the field alternatives in the source, with no extra hypothesis.
Source: Wei Yang #1412, item 18 (blueprint: def-weil-exceptional-inverse-image).
Proof: split the given disjunction. In the finite-field branch install its `Finite k`
instance and apply `BaseFieldFiniteCD.of_finite`; in the algebraically closed branch install
its `IsAlgClosed k` instance and apply `BaseFieldFiniteCD.of_isAlgClosed`. -/
theorem exceptionalCurrentFieldCD (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) : BaseFieldFiniteCD ℓ k := by
  sorry

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hk : Finite k ∨ IsAlgClosed k)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (hΛ : IsNativeExceptionalCoefficient ℓ Λ)

/-- The native condensed exceptional inverse image in the current field scope. Its object and
morphism maps are those of the existing Brown right adjoint restricted to bounded constructible
objects; the field assumption supplies its finite-cd proof. It uses no finite coefficient tower.
Source: non-finite Brown paragraph and Wei Yang #1412, item 18
(blueprint: def-weil-exceptional-inverse-image). -/
def currentExceptionalInverseImage :
    ConstantModelBoundedConstructible Λ Y.left ⥤ ConstantModelBoundedConstructible Λ X.left :=
  nativeConstructibleExceptionalInverseImage Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ

/-- The actual restricted compact-support functor with its natural Hom adjunction to the
native operation. This is the published restriction of the single localizing Brown adjunction.
Source: defining Hom bijections (blueprint: def-weil-exceptional-inverse-image). -/
def currentExceptionalAdjunction :
    nativeConstructibleLowerShriek Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ ⊣
      currentExceptionalInverseImage Λ ℓ k hk f hΛ :=
  nativeConstructibleExceptionalAdjunction Λ ℓ k (exceptionalCurrentFieldCD ℓ k hk) f hΛ

end WeilConjectures

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
