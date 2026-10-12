/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap

/-! # Changing the derived-to-ordinary comparison on a single module

Source: Stacks Project, Tags 06YJ and 08HY; the degree-zero truncation argument
in Step 4 of `lem-pc-affine-alternating-cech-base-change-factorization`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Two left-derived counits on a single module differ by an automorphism of its
ordinary pullback. There is no cover, direct image or base-change square in this lemma.
Source: Stacks Project, Tags 06YJ and 08HY; Step 4 of the affine alternating model
factorization proof (the truncation argument is written out here).
(blueprint: lem-pc-module-pullback-comparison-target-automorphism).

Proof: Right Kan extension uniqueness gives an automorphism of the derived pullback
functor relating the two witnessing counits. Derived tensor of a degree-zero module
is nonpositive: resolve it by a bounded-above complex of flat modules in degrees at
most zero. Right exactness identifies degree-zero homology of that tensor complex
with ordinary tensor pullback, and the counit induces this identification. Thus both
counits induce isomorphisms on H0. A map from this nonpositive object to a module in
degree zero factors uniquely through its H0 truncation: in the truncation triangle,
both Hom from the negative truncation and Hom from its shift by one vanish by the
standard t-structure orthogonality. Apply this to both comparisons. Compose the
inverse of H0(c0) with H0(c), and transport through the single-module H0 isomorphism,
to obtain a module automorphism alpha. Full faithfulness of the single functor and
uniqueness of the truncation factorization give c = c0 followed by alpha[0].
This includes the zero module and the empty scheme; no flatness of G is used. -/
theorem modulePullbackComparison_target_automorphism
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [(Scheme.Modules.tensorPullback a).Additive]
    (G : Y.Modules)
    (c₀ c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback a).obj G))
    (hc₀ : IsDerivedModulePullbackComparison a G c₀)
    (hc : IsDerivedModulePullbackComparison a G c) :
    ∃ α : (Scheme.Modules.tensorPullback a).obj G ≅
        (Scheme.Modules.tensorPullback a).obj G,
      c = c₀ ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map α.hom := by sorry

end AlgebraicGeometry
