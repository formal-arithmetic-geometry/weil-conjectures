/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Full cohomological dimension for constant pro-etale coefficients

Source: Weil blueprint, order 1473 (blueprint: def-weil-full-cohomological-dimension).
The predicate quantifies over every sheaf on the original source, and its restrictions
on the specified pro-etale base changes. It does not assert that any bound exists.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The full cohomological dimension bound: higher direct images of every module sheaf
vanish above `c`, both before base change and on its restriction to each pro-etale base
change. No etale-origin restriction is imposed. The first conjunct is stated explicitly;
the second uses the canonical fiber product, its projection, and tensor inverse image.
This definition makes sense without properness; its blueprint use is for the proper
part of a compactification over a scheme base with the prime invertible.
Source: Weil blueprint order 1473 (blueprint: def-weil-full-cohomological-dimension). -/
def sfFullCohomologicalDimension {X Y : Scheme.{u}} (p : X ⟶ Y)
    (A : Type u) [CommRing A] (c : ℕ) : Prop :=
  (∀ (F : proEtaleRingModules X (proEtaleConstantRing X A)) (r : ℤ),
    (c : ℤ) < r → IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((proEtaleConstantDerivedDirectImage p A).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)))) ∧
  ∀ (V : Y.ProEt) (F : proEtaleRingModules X (proEtaleConstantRing X A)) (r : ℤ),
    (c : ℤ) < r → IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((proEtaleConstantDerivedDirectImage (pullback.snd p V.hom) A).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (proEtaleConstantModulePullback (pullback.fst p V.hom) A F))))

end AlgebraicGeometry.Scheme
