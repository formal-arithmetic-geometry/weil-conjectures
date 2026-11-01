/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedRefinement.RingedRefinementData

/-!
# Shift compatibility of the ringed scalar pullback comparison

(blueprint: new-ringed-refinement-pull-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.RingedRefinement

/-- The normalized inverse-image comparison commutes with integer shifts.
Proof route: instantiate `coefficientPullbackShifts` on the operation's inverse
image; `ScalarComparisons.insertion` identifies its ordinary comparison and
`ordinary_mate` transports the generic derived comparison to `sc.pull`.  The
computation-counit normalization is exactly the hypothesis used by the generic
shift theorem.
(blueprint: new-ringed-refinement-pull-shift). -/
theorem ringedRefinementPullShift {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) (sc : ScalarComparisons o)
    (s : ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B),
      (o.scalar W a).T.CommShift ℤ)
    (hs : letI := s
      ∀ (W : Over T) {A B : Rings m T} (a : A ⟶ B),
        NatTrans.CommShift (o.scalar W a).ε ℤ) :
    letI := s
    ∀ {U V : Over T} (f : U ⟶ V) {A B : Rings m T} (a : A ⟶ B),
      NatTrans.CommShift (sc.pull f a).hom ℤ := by
  sorry

end SheafOfModules.RingedRefinement
