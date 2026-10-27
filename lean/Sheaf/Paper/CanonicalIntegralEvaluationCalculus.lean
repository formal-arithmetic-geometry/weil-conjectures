/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus

/-! # Coherent reduction with the fixed integral closed tensor

Source: Stacks 06YS, 07A4, 08JD and 0941, and step 1 of the compatible
open-tensor context construction. This is the presentation-normalization refinement
of the coherent coefficient calculus, on a single scheme.
(blueprint: lem-pur-canonical-integral-evaluation-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Choose the coherent reduction calculus with its integral closed structure literally
equal to the fixed normalized duality structure. No open immersion, ordinary reduction
model, completion model, completion comparison or open comparison occurs here.

Source: Stacks 06YS, 07A4, 08JD and 0941; the coefficient-calculus construction
and step 1 of lem-pur-completed-open-tensor-context.
(blueprint: lem-pur-canonical-integral-evaluation-calculus).

Proof: start with the coherent coefficient calculus and keep its reduction functor,
reduction/limit adjunction, reduction evaluations, strict quotient presentations,
fiber Hom and global-section data. Fix IntegralOnSlice.duality as the integral
closed model. Choose normalized ringed-site duality models on the sequence site
and the finite coefficient sites as well. In each coefficient category the old
and new tensors are left adjoints to the same internal Hom. The parametric
left-adjoint comparison therefore preserves evaluation and every transpose.
On K-flat representatives, its composite with the new tensor presentation equals
the old presentation: transpose into a fixed K-injective Hom representative;
both maps send a pure tensor x tensor y to phi(x)(y). Generator uniqueness and
fully faithful whiskering along the K-flat localization prove this equation.

Replace the three closed fields by these fixed models, using their tensor models.
If a is the integral old-to-new tensor comparison and b the system old-to-new
comparison, replace the reduction tensor map mu by
R(a inverse); mu; b. Use the identical formula for finite scalar extension,
evaluation and quotient tensor comparisons, with the appropriate pair of old/new
comparisons. Keep all non-tensor quotient and adjunction fields. In the finite,
evaluation and strict-system representative squares the adjacent comparison and
inverse comparison cancel by the preceding K-flat equation; hence the same
ordinary pure-tensor and strict quotient maps verify those squares.

Uncurrying the new base-change map cancels a and b against their evaluation
identities, so it is the old base-change map. This proves its naturality,
transpose formula, fiber formula and enriched invertibility, and leaves the
global gamma, its projection, H-zero and naturality equations unchanged.
For internal composition use the new normalized associators on all three sites:
on three K-flat representatives both composites reassociate x tensor y tensor z
and evaluate phi(psi(x)). The differential signs are those of the same total
complex. Generator uniqueness and localization give the composition equation;
this does not assert that an arbitrary adjoint comparison is monoidal.
The mapping-composition square follows directly by transposing the reduction
adjunction and using naturality of the new tensor comparison. All remaining
resolution, scalar, fiber and global-limit coherence fields are unchanged.
Assemble the records with the integral closed field set to the fixed duality
field; its displayed equality is reflexivity. The construction uses unbounded
K-flat resolutions, so zero objects and the empty scheme require no exception,
and no invertibility assumption on l on the scheme is needed. -/
theorem canonicalIntegralEvaluationCalculus :
    ∃ (S : CoefficientDerivedSystemCalculus l E W)
      (_coherence : CoefficientDerivedSystemCoherence l E W S),
      (IntegralOnSlice.duality l E W none).closed = S.integralClosed := by sorry

end WeilConjectures
