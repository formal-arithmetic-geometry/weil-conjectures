/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Data.ZMod.Basic

/-! # Cohomology of site-perfect duals over a field

Source: blueprint lem-fin-lisse-field-dual, local finite-free calculation.
(blueprint: lem-fin-lisse-field-dual-homology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

/-- The cohomology of a site-perfect coefficient dual over the prime field is the ordinary
sheaf dual of the degree-reversed cohomology.

Source: blueprint lem-fin-lisse-field-dual, local finite-free calculation; Stacks
Project, sites-cohomology.tex, sections on derived internal Hom and perfect complexes.
(blueprint: lem-fin-lisse-field-dual-homology).

Proof: on an etale perfect-model cover, the terms are retracts of finite
constant free sheaves, hence finite locally constant. Refine the cover to
trivialize the finitely many terms and make all differential matrices constant.
The model is then the constant sheaf image of a bounded finite-dimensional module
complex. The constant-sheaf functor is exact and strong monoidal. On this bounded
finite-free model its derived functor preserves the dual: the internal-Hom
comparison of a strong monoidal functor is invertible out of a dualizable object.
Exactness also commutes with homology. Ordinary field linear algebra splits cycles
and boundaries, identifying the cohomology of the module dual with the dual of
opposite-degree cohomology; the constant-sheaf functor gives the asserted local
formula. The global comparison is induced by evaluation on cycles: a Hom cocycle
evaluated on a cycle gives a coefficient cycle, and changing either argument by a
boundary gives a coefficient boundary. Thus evaluation descends through both
homology quotients and is independent of model choices. Exact restriction and
evaluation are natural, so these canonical maps agree on overlaps and descend.
Their local inverses agree as well, making the global comparison invertible. No
arbitrary local isomorphisms are glued. Zero terms, zero ranks and the empty scheme
use the zero-object calculation. -/
theorem sitePerfect_fieldDual_homology
    (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    (C : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T) (hC : DerivedCategory.IsSitePerfect C) :
    ∀ q : ℤ, Nonempty
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) T).obj (op C)).obj
            (constantComplex (ULift.{u + 1} (ZMod ℓ)) T)) ≅
        (ihom ((_root_.DerivedCategory.homologyFunctor _ (-q)).obj C)).obj
          (𝟙_ (Sheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))))) := by sorry

end AlgebraicGeometry.Etale
