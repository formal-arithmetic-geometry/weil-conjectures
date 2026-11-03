/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalRefinement.ExceptionalRefinementSystemData

/-! # Strict-system realization of a normalized refinement -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalRefinement
open WeilConjectures.ConstructibleExceptionalCoefficients
open WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  {c d : Compactification f}

/-- The strict-system lift of an already normalized refinement comparison.
Source: Zheng 5.13--5.15, 5.20, 5.22 and 5.24; retained refinement steps 2--4
(blueprint: lem-sf-exceptional-refinement-system-realization).

Proof: On the given reduced input form the intrinsic system proper/open refinement
word using R.properOpen and R.compositors. Integral reconstruction makes that input
Good; system transport and finite operations give Good open intermediates and common
finite cohomological and Tor bounds. Its finite evaluations are the invertible
proper/open comparisons, so conservative evaluation proves this actual system word
invertible. Take its inverse, naturally in the input, to obtain alpha; its inverse is
exactly the word, without inferring equality from evaluations. For each compactification
compose the prescribed proper realization with proper image of R.openRealization and
then image of the inverse reconstruction unit. Each factor is a natural isomorphism
on this Good domain, giving realization and realizationNormalized. The proper/open
realization and proper compositor equation identify the total-limit image of alpha
with the inverse ambient proper/open refinement. P.normalized at the integral stage
identifies that very map with P.comparison.left, giving integralMap by cancellation
of the two endpoint realizations. Open/clopen system shifts, adjoint shifts, inversion
and whiskering give alpha.hom.CommShift. The same realization shift coherence applied
to the two proper/open expressions gives realizationShift, using the prescribed Roos
limit shift. The construction uses only P's integral left map and its normalization;
its right maps and coefficient descent equations are irrelevant. Identity refinements
and zero inputs use the same word and units; no Cartesian refinement square or absolute
separatedness is required. -/
theorem exceptional_refinement_system_realization
    (A : Transport.{u, v} l Ω D hl c) (B : Transport.{u, v} l Ω D hl d)
    (r : c.Refinement d) (P : Mates.{u, v} l Ω D hl A B r)
    (E : FieldStage.{max u v} l) (o : Operations l E.carrier)
    (R : Realizations l E.carrier D o) :
    Nonempty (SystemRealization.{u, v} l Ω D hl A B r P E o R) := by sorry

end WeilConjectures.ExceptionalRefinement
