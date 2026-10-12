/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison

/-! # Single-module comparison and composition of two pullbacks

Source: Stacks Project, Tag 0D5S, and the defining left-derived lift factorization.
(blueprint: lem-pc-canonical-single-pullback-composition).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Compatibility with composition of two morphisms, before comparing square paths.
Source: Stacks Project, Tag 0D5S, and `Functor.leftDerived_fac_app` applied to the
factorization in `exists_derivedPullbackComposition`.
(blueprint: lem-pc-canonical-single-pullback-composition).

Proof: Write ε for the chosen derived counits and t for the unique left-adjoint
isomorphism from tensor pullback to ordinary pullback. Evaluate the defining
leftDerivedLift factorization at the single complex of N. Its right side is
Lf*(ε_g) followed by ε_f at the termwise g-pullback and the termwise tensor
composition isomorphism. Postcompose with the single-complex comparison for f ≫ g
and with the single embedding of t_(f ≫ g). Naturality of ε_f moves the
single-complex comparison for g through ε_f. Compatibility of the single-complex
isomorphisms with mapping a composite functor then identifies this with the two
successive single comparisons and the single embedding of tensor composition.
The remaining underived equation is
T_f(t_g) ≫ t_f ≫ pullbackComp.hom = tensorComp.hom ≫ t_(f ≫ g).
Apply the conjugate-morphism equivalence of the composite adjunctions: the
leftAdjointUniq counit equations make both sides the same pushforward composition
map, while conjugateEquiv_pullbackComp_inv pins its ordinary pullback mate.
Injectivity proves the underived equation, and mapping it by the single functor
finishes. No derived single comparison is inverted, so no flatness is required;
identity morphisms, zero modules, and empty schemes are included. -/
theorem canonicalSinglePullbackComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) f g).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj N) ≫
      canonicalSinglePullbackMap (f ≫ g) N =
    (derivedPullback f).map (canonicalSinglePullbackMap g N) ≫
      canonicalSinglePullbackMap f ((pullback g).obj N) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((pullbackComp f g).hom.app N) := by sorry

end AlgebraicGeometry.Scheme.Modules
