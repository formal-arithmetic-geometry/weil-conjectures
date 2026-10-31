/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementData

/-! # Geometric support and the clopen summand projector

These are geometric statements on the whole module derived category, before any
scalar or proper-refinement comparison is chosen.
(blueprint: new-ringed-refinement-open-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.RingedRefinement

attribute [local irreducible] Calculus.openAdjunction Calculus.shriek
  AlgebraicGeometry.Scheme.ProjectionRestriction.Operation.left
  Spatial.square Spatial.openFactor Spatial.sectionPull


/-- Pullback preserves open support, and the clopen summand has its unique projector.
Source: coefficient supplement Steps 2--4; Stacks 03DI, 04J0, 04TR/04TS and 04VG.

Proof: identify the coefficient rings along opens with literal restriction of the
ambient ring, using the specified inverse-image isomorphisms. The ringed open-slice
adjunction identifies the supplied open extension with extension by zero. In a
cartesian open square, restriction of direct image is direct image on the open
slices: both section functors evaluate on the same fibre product. Uniqueness of
left adjoints gives the corresponding open-exchange isomorphism. Consequently
pullback of an extended module is in the essential image of the other extension,
and its open counit is invertible. Exact termwise localization gives the claimed
counit on every unbounded derived object, using the localization's essential
surjectivity. For a clopen immersion, glue modules on the distinguished open and
its complement. The gluing equivalence has exact coordinate restrictions and
zero insertions. Localize this equivalence and its adjunctions. First-coordinate
projection, transported to the specified open adjunction, gives pi. Its two
restrictions are respectively the specified open unit and zero. Joint faithfulness
of the two coordinate restrictions proves uniqueness. In systems mode construct
the gluing equivalence with the given semilinear horizontal transitions first and
localize the entire module-system category; derived evaluation is not used.
(blueprint: new-ringed-refinement-open-geometry).
-/
theorem ringedRefinementOpenGeometry {m : Mode} {T : Scheme.{u}}
    {c : Coefficients m T} (o : Calculus c) :
    (∀ {V X Y Z : Over T} (b : V ⟶ Y) (q : V ⟶ X) (u : Y ⟶ Z) (j : X ⟶ Z)
      [IsOpenImmersion b.left] [IsOpenImmersion j.left]
      (_sq : IsPullback b q u j) (R : Rings m T) (M : category c X R),
      IsIso ((o.openAdjunction b R).counit.app
        ((o.operation u R).left.obj ((o.shriek j R).obj M)))) ∧
    (∀ {U V : Over T} (s : U ⟶ V) [IsOpenImmersion s.left]
      (hs : IsClopen (Set.range s.left.base)) (R : Rings m T),
      ∃! pi : 𝟭 (category c V R) ⟶ (o.operation s R).left ⋙ o.shriek s R,
        (∀ N : category c V R,
          (o.operation s R).left.map (pi.app N) =
            (o.openAdjunction s R).unit.app ((o.operation s R).left.obj N)) ∧
        (∀ {W : Over T} (t : W ⟶ V) [IsOpenImmersion t.left]
          (_ht : Set.range t.left.base = (Set.range s.left.base)ᶜ) (N : category c V R),
          (o.operation t R).left.map (pi.app N) = 0)) := by
  sorry

end SheafOfModules.RingedRefinement
