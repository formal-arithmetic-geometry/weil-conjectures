/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousLocallyFreePullback
public import Sheaf.Paper.ContinuousLatticeIntersection
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Locally free integral images under finite etale trace

Source: blueprint main-20261015, stratified lattice proof, Pushing down by the trace.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The finite etale trace is epic and its integral image is locally free.
Source: Bhatt--Scholze, Section 6.8; blueprint main-20261015,
stratified lattice proof, Pushing down by the trace.
(blueprint: lem-sfb-continuous-finite-etale-trace-lattice).

Proof. Split the finite etale surjection etale locally. On a split chart define trace
by summing the sheet counits. Permutation invariance and sheaf descent glue this map.
On any nonempty chart surjectivity supplies a sheet; insertion into that sheet gives
a local right inverse, hence trace is epic. The integral image restricts to the sum
of the sheet lattices, by the local sum formula of finite_etale_trace_image.
Trivialize P pro-etale locally. The lattice-class sheaf is the constant coset sheaf,
so the finitely many sheet lattices are constant on a common refinement, with equality
of their embedded images. Their finite sum is an algebraic free full lattice.
The continuous lattice sum theorem gives a continuous linear section of the sum map
and a restriction-compatible free presentation of its continuous-function sheaf.
Therefore the sheaf image is that free sheaf on the refinement. Transport back through
the continuous coefficient module equivalence and compose the covers to obtain local
freeness of the actual categorical image below. This argument includes empty schemes
and zero rank and does not divide by the covering degree. No rationalization of the
image inclusion is asserted here. -/
theorem continuousFiniteEtaleTrace_lattice
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : LocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (hM : LocallyFree (condensedRingObj (integralCoeff l E) U) M)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    ∃ τ : (lowerStar (Profinite.continuousMapRingObj E) p).obj
        ((upperStar (Profinite.continuousMapRingObj E) p).obj P) ⟶ P,
      Epi τ ∧ LocallyFree (condensedRingObj (integralCoeff l E) X)
        (image (latticePushedEmbedding (integralScalarMap l E) X P p M e ≫
          (Mod.comap (coefficientMap (integralScalarMap l E) X)).map τ)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
