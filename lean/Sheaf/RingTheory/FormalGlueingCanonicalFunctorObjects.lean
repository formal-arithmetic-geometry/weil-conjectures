/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.FormalGlueingData
import Sheaf.Paper.FormalGlueingCanonicalMaps

@[expose] public section

universe u v w

open CategoryTheory
namespace FormalGlueing

/-- The canonical glueing object of a single module; no morphisms are asserted here.
Source: Stacks Project, More on Algebra, Remark 05EL, construction of `Can`.
(blueprint: lem-weil-pbc-formal-glueing-canonical-functor-objects).
Proof: take the prime module to be S tensor M and chart i to be M localized at f i,
with its canonical module structure over R localized at f i. Restricting the chart
back to R gives the original localized R-module: algebraMap_smul identifies the
actions, and the underlying additive groups coincide. Transport the comparison and
swap maps along these bundled-module equalities. The compare_properties theorem
makes comparison bijective, and swap_properties gives inverse swaps. Use these to
form linear equivalences; compare_smul supplies alpha_smul. For the square, both
paths send a pure tensor fraction with denominators f i and f j to the tensor of
that element with the denominators interchanged. Tensor induction and localization
induction extend this equality to every element. For the cocycle, every element is
a threefold fraction; both paths reverse the order of its three denominators.
The fraction formulas in swap_properties prove equality. Thus these fields satisfy
Data.square and Data.cocycle. All remaining fields are proofs. This works also for
an empty chart family, zero denominators, and the zero module. -/
theorem exists_canonical_functor_objects {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (M : ModuleCat.{max u v w} R) :
    ∃ X : Data.{u, v, max u v w} φ f,
      X.M' = extend φ M ∧
      (∀ i : Fin t, X.M i =
        ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
      (∀ i : Fin t, HEq (X.alpha i).toLinearMap (compare φ (f i) M)) ∧
      (∀ i j : Fin t, HEq (X.alpha_overlap i j).toLinearMap (swap (f i) (f j) M)) := by
  sorry

end FormalGlueing
