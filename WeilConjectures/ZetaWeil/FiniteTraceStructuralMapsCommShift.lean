/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteTraceGlobalOperator
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-! # Shift compatibility of the structural arrows of the global operator

Source: latest blueprint, sec-trace-formula/sk-i-additivity,
lem-trf-global-operator-triangulated.proof.md, sentence 'Each of these constructions is a
natural transformation of exact functors in the coefficient object'
(blueprint: lem-trf-finite-structural-maps-commshift).

The four structural arrows are exactly those of `finiteTrfGlobalOperatorAmbient`
(def-trf-global-operator): `H_X(η_{c₂})`, `α_{c₂}` (inverse proper coincidence followed by
the compact-support composition `W.comp` for `a_X c₂ = a_C`), `γ_{c₁}⁻¹` (inverse
compact-support composition for `a_X c₁ = a_C`) and `H_X(ε_{c₁})` (counit of
`traceFormulaCtfShriekAdjunction`). The components below are copied verbatim from that
definition, with the coefficient object `K` now varying.

Shifts. Dctf is stable under shifts (cohomology reindexing and finite Tor amplitude), so it
carries the inherited shift and its inclusion `ι` the canonical comparison. Every total
right derived functor carries the canonical K-injective shift
(`Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt`, pinned locally, so that the
adjunction-transported instance `commShift_rightDerivedLowerStar` is not used); derived
pullback carries `moduleObjectDerivedPullbackCommShift`; `D(j_!)` and exact scalar
restriction carry their termwise shifts. Hence `Fib_s`, `H_Z = Fib_s ∘ Ra_{Z!}` and the
restricted `Rc₁!` get the composite canonical shifts, and `Rc₁^!` gets the unique shift
compatible with the specified adjunction (`Adjunction.rightAdjointCommShift`).
All these are sorry-free definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local instance 30000]
  CategoryTheory.Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- Bounded constant-model constructible complexes of finite Tor amplitude are stable under
all integer shifts: cohomology is reindexed and finite Tor amplitude is shift stable.
Source: latest blueprint def-weil-finite-tor-amplitude and def-weil-triangulated-category
(blueprint: lem-trf-finite-structural-maps-commshift).

Proof: boundedness is shift stable for the canonical t-structure; `H^q(K[n]) ≅ H^{q+n}(K)`
and constructibility is closed under isomorphisms; finite Tor amplitude is a triangulated
property by `constantModelConstructibleFiniteTor_wellDefined`. -/
instance finiteTrfDctf_isStableUnderShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u}) :
    (constantModelBoundedConstructible Λ Y ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).IsStableUnderShift ℤ := by
  let C := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
  have hcons := (constantModelConstructibleFiniteTor_wellDefined Λ Y).1
  have htor : (_root_.DerivedCategory.finiteTorAmplitude C).IsTriangulated :=
    (constantModelConstructibleFiniteTor_wellDefined Λ Y).2.2.2.2.2.2.2.1
  refine ⟨fun n ↦ ⟨fun K hK ↦ ?_⟩⟩
  refine ⟨⟨_root_.DerivedCategory.TStructure.t.bounded.le_shift n K hK.1.1, ?_⟩,
    (_root_.DerivedCategory.finiteTorAmplitude C).le_shift n K hK.2⟩
  intro q
  exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ Y)
    (((_root_.DerivedCategory.homologyFunctor C 0).shiftIso n q (q + n)
      (by omega)).app K).symm (hK.1.2 (q + n))

/-- The full inclusion of Dctf into the ambient derived category of module objects.
Source: def-weil-finite-tor-amplitude, full subcategory
(blueprint: lem-trf-finite-structural-maps-commshift). -/
abbrev finiteTrfDctfι (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Λ Y ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
  ObjectProperty.ι _

/-- The discrete topology on the shrunk coefficient ring, exactly the `⊥` of
`FiniteTraceFormulaConventions.coefficients`.
Source: def-trf-coefficient-conventions, A discrete
(blueprint: def-trf-coefficient-conventions). -/
@[reducible] def finiteTrfShrinkTopology (T : FiniteTraceFormulaConventions.{u}) :
    TopologicalSpace (Shrink.{0} T.A) := ⊥

attribute [local instance] finiteTrfShrinkTopology

/-- The shrunk coefficient ring is discrete.
Source: def-trf-coefficient-conventions (blueprint: def-trf-coefficient-conventions). -/
theorem finiteTrfShrinkDiscrete (T : FiniteTraceFormulaConventions.{u}) :
    DiscreteTopology (Shrink.{0} T.A) := ⟨rfl⟩

attribute [local instance] finiteTrfShrinkDiscrete

/-- The shrunk discrete coefficient ring is a topological ring.
Source: def-trf-coefficient-conventions (blueprint: def-trf-coefficient-conventions). -/
theorem finiteTrfShrinkTopologicalRing (T : FiniteTraceFormulaConventions.{u}) :
    IsTopologicalRing (Shrink.{0} T.A) := DiscreteTopology.topologicalRing

attribute [local instance] finiteTrfShrinkTopologicalRing

/-- The canonical shift of `Fib_s`: the K-injective shift of the derived point sections
followed by the termwise shift of exact scalar restriction.
Source: def-trf-coefficient-conventions, Fib_s; def-weil-finite-coefficient-point
(blueprint: lem-trf-finite-structural-maps-commshift). -/
instance finiteTrfPointFiberCommShift (T : FiniteTraceFormulaConventions.{u}) :
    T.pointFiber.CommShift ℤ := by
  unfold FiniteTraceFormulaConventions.pointFiber
  infer_instance

/-- The canonical composite shift of `H_Y = Fib_s ∘ Ra_{Y!}` for a compactification of the
structure map: termwise shift of `D(j_!)`, K-injective shift of `Rp_*`, then `Fib_s`.
Source: lem-compact-support-direct-image-triangulated and def-trf-coefficient-conventions
(blueprint: lem-trf-finite-structural-maps-commshift). -/
instance finiteTrfOperatorCompactSupportCommShift (T : FiniteTraceFormulaConventions.{u})
    {Y : Scheme.{u}} {a : Y ⟶ Spec (.of T.datum.k)} (d : Compactification a) :
    (T.operatorCompactSupport d).CommShift ℤ :=
  inferInstanceAs
    ((rightDerivedLowerShriekOfCompactification T.coefficients d ⋙ T.pointFiber).CommShift ℤ)

section Legs

variable (F : FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
  [DiscreteTopology A] [IsTopologicalRing A]

end Legs

set_option maxHeartbeats 2000000 in
-- The verbatim global-operator components elaborate several derived-functor composites.
set_option maxHeartbeats 2000000 in
-- The verbatim global-operator components elaborate several derived-functor composites.
set_option maxHeartbeats 4000000 in
-- The verbatim global-operator components elaborate several derived-functor composites.
end WeilConjectures
