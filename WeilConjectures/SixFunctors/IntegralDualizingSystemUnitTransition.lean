/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemUnitComparison
public import WeilConjectures.SixFunctors.IntegralDualizingFiniteUnitQuotient

/-! # The quotient transition on the coefficient system unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})

/-- The regular coefficient system has the genuine quotient maps in the normalized
finite etale unit coordinates.
Source: Stacks 07A4 and 0941; finite counit compatibility, proof step 2.
(blueprint: lem-coef-finite-unit-quotient).
Proof: coefficientSequenceTransition is the horizontal restriction of the module
presheaf. On its regular module this is the coefficient sheaf quotient. Evaluate the
single complex and use the canonical exact-functor single comparison to identify the
derived transition with that quotient in degree zero. The scalar-adjunction unit on
the etale regular unit sends a to 1 tensor a; the normalized scalar-unit comparison
sends this to the quotient of a. Comparison pullback preserves these generators.
The generator-normalized finiteDualizingIntrinsicUnit and section-normalized
finiteDualizingRealizationRestriction therefore carry the same quotient map to the
intrinsic regular module. Equality on local constant scalar generators gives equality
of sheaf maps, and exact localization gives the displayed equality. The argument
applies to every scheme W, to equal levels, and at the first quotient. -/
theorem integralDualizingRegularUnit_transition {m n : ℕ} (h : n ≤ m) :
    (coefficientSequenceDerivedTransition l E W h).app
        ((DerivedCategory.singleFunctor (coefficientSequenceModules l E W) 0).obj
          (SheafOfModules.unit
            ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                (coefficientSequenceCommRingSheaf l E W)))) ≫
      (normalizedDVRRes l E W h).map
        (integralDualizingRegularUnitEvaluation l E W n).hom =
    (integralDualizingRegularUnitEvaluation l E W m).hom ≫
      integralDualizingFiniteUnitQuotient l E W h := by sorry

end WeilConjectures
