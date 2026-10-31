/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceGroupoid
public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.CategoryTheory.SiteStackification

/-! # Presenting an fppf quotient stack by an algebraic-space groupoid

Source: Stacks Project, Groupoids in Spaces, Tags 044Q, 044R and 044T;
Stacks, Tags 02ZP and 0436
(blueprint: def-sfb-space-groupoid-quotient-presentation).

The presentation remembers arrows and composition, not just the orbit sheaf. Objects
lift fppf locally; arrows between lifted objects are exactly the original algebraic-space arrows.
This characterizes the stackification up to equivalence, without choosing its objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The image of an original groupoid arrow, transported along its endpoint equalities.
Source: Stacks, Tags 044Q, 044R and 044T
(blueprint: def-sfb-space-groupoid-quotient-presentation). -/
def spaceGroupoidPresentationArrow {S : Scheme.{u}} {U R : AlgebraicSpace S}
    {F : BasedCategory.{v, w} (Over S)}
    (s t : R.obj.obj ⟶ U.obj.obj) (a : BasedFunctor (discreteModuli U.obj.obj) F)
    (η : ModuliTwoIso ((discreteModuliMap s).comp a)
      ((discreteModuliMap t).comp a))
    {T : Over S} (x y : yoneda.obj T ⟶ U.obj.obj)
    (r : {r : yoneda.obj T ⟶ R.obj.obj //
      r ≫ s = x ∧ r ≫ t = y}) :
    a.obj (CostructuredArrow.mk x) ⟶ a.obj (CostructuredArrow.mk y) :=
  eqToHom (congrArg (fun z : yoneda.obj T ⟶ U.obj.obj ↦
    a.obj (CostructuredArrow.mk z)) r.property.1.symm) ≫
  η.val.hom.app (CostructuredArrow.mk r.val) ≫
  eqToHom (congrArg (fun z : yoneda.obj T ⟶ U.obj.obj ↦
    a.obj (CostructuredArrow.mk z)) r.property.2)

/-- A presentation of the fppf stackification of the specified algebraic-space groupoid.
The target is an fppf stack in the recorded sense `IsFppfModuliStack`.
Full faithfulness is imposed on actual vertical arrows, and the last field identifies
composition with the specified presheaf map `c`. Naturality is built into the two-isomorphism.
Identity and inverse compatibility follow from composition compatibility and bijectivity.

Source: Stacks, Tags 044Q, 044R, 044T, 02ZP and 0436
(blueprint: def-sfb-space-groupoid-quotient-presentation). -/
structure SpaceGroupoidQuotientPresentation {S : Scheme.{u}} {U R : AlgebraicSpace S}
    (s t : R.obj.obj ⟶ U.obj.obj) (e : U.obj.obj ⟶ R.obj.obj) (i : R.obj.obj ⟶ R.obj.obj)
    (c : pullback s t ⟶ R.obj.obj)
    (F : BasedCategory.{v, w} (Over S))
    (a : BasedFunctor (discreteModuli U.obj.obj) F) where
  groupoid : AlgebraicSpace.IsPresheafGroupoid s t e i c
  stack : IsFppfModuliStack F
  arrows : ModuliTwoIso ((discreteModuliMap s).comp a)
    ((discreteModuliMap t).comp a)
  fully_faithful : ∀ (T : Over S) (x y : yoneda.obj T ⟶ U.obj.obj)
    (β : a.obj (CostructuredArrow.mk x) ⟶ a.obj (CostructuredArrow.mk y)),
    F.p.IsHomLift (𝟙 T) β →
      ∃! r : {r : yoneda.obj T ⟶ R.obj.obj //
        r ≫ s = x ∧ r ≫ t = y},
        spaceGroupoidPresentationArrow s t a arrows x y r = β
  locally_surjective : ∀ z : F.obj,
    ∃ V : Sieve (F.p.obj z), V ∈ (Scheme.fppfTopology.over S) (F.p.obj z) ∧
      ∀ (T : Over S) (f : T ⟶ F.p.obj z), V f →
        ∃ (x : yoneda.obj T ⟶ U.obj.obj)
          (β : a.obj (CostructuredArrow.mk x) ⟶ z), F.p.IsHomLift f β
  composition : ∀ (T : Over S) (x y z : yoneda.obj T ⟶ U.obj.obj)
    (r : {r : yoneda.obj T ⟶ R.obj.obj //
      r ≫ s = x ∧ r ≫ t = y})
    (q : {q : yoneda.obj T ⟶ R.obj.obj //
      q ≫ s = y ∧ q ≫ t = z})
    (d : {d : yoneda.obj T ⟶ R.obj.obj //
      d ≫ s = x ∧ d ≫ t = z})
    (p : yoneda.obj T ⟶ pullback s t),
    p ≫ pullback.fst s t = q.val →
    p ≫ pullback.snd s t = r.val →
    p ≫ c = d.val →
      spaceGroupoidPresentationArrow s t a arrows x y r ≫
        spaceGroupoidPresentationArrow s t a arrows y z q =
          spaceGroupoidPresentationArrow s t a arrows x z d

end CategoryTheory
