/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeGroupoidLaws
public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.CategoryTheory.SiteStackification

/-! # Presenting an fppf quotient stack by a scheme groupoid

Source: Stacks Project, Groupoids in Spaces, Tags 044Q, 044R and 044T;
Stacks, Tags 02ZP and 0436
(blueprint: def-sfb-scheme-groupoid-quotient-presentation).

The presentation remembers arrows and composition, not just the orbit sheaf. Objects
lift fppf locally; arrows between lifted objects are exactly the original scheme arrows.
This characterizes the stackification up to equivalence, without choosing its objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The image of an original groupoid arrow, transported along its endpoint equalities.
Source: Stacks, Tags 044Q, 044R and 044T
(blueprint: def-sfb-scheme-groupoid-quotient-presentation). -/
def schemeGroupoidPresentationArrow {S : Scheme.{u}} {U R : Over S}
    {F : BasedCategory.{v, w} (Over S)}
    (s t : R ⟶ U) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (η : ModuliTwoIso ((discreteModuliMap (yoneda.map s)).comp a)
      ((discreteModuliMap (yoneda.map t)).comp a))
    {T : Over S} (x y : yoneda.obj T ⟶ yoneda.obj U)
    (r : {r : yoneda.obj T ⟶ yoneda.obj R //
      r ≫ yoneda.map s = x ∧ r ≫ yoneda.map t = y}) :
    a.obj (CostructuredArrow.mk x) ⟶ a.obj (CostructuredArrow.mk y) :=
  eqToHom (congrArg (fun z : yoneda.obj T ⟶ yoneda.obj U ↦
    a.obj (CostructuredArrow.mk z)) r.property.1.symm) ≫
  η.val.hom.app (CostructuredArrow.mk r.val) ≫
  eqToHom (congrArg (fun z : yoneda.obj T ⟶ yoneda.obj U ↦
    a.obj (CostructuredArrow.mk z)) r.property.2)

/-- A presentation of the fppf stackification of the specified scheme groupoid.
The target is an fppf stack in the recorded sense `IsFppfModuliStack`.
Full faithfulness is imposed on actual vertical arrows, and the last field identifies
composition with the specified scheme map `c`. Naturality is built into the two-isomorphism.
Identity and inverse compatibility follow from composition compatibility and bijectivity.

Source: Stacks, Tags 044Q, 044R, 044T, 02ZP and 0436
(blueprint: def-sfb-scheme-groupoid-quotient-presentation). -/
structure SchemeGroupoidQuotientPresentation {S : Scheme.{u}} {U R : Over S}
    (s t : R ⟶ U) (e : U.left ⟶ R.left) (i : R.left ⟶ R.left)
    (c : pullback s.left t.left ⟶ R.left)
    (F : BasedCategory.{v, w} (Over S))
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) where
  groupoid : Scheme.IsGroupoid s.left t.left e i c
  stack : IsFppfModuliStack F
  arrows : ModuliTwoIso ((discreteModuliMap (yoneda.map s)).comp a)
    ((discreteModuliMap (yoneda.map t)).comp a)
  fully_faithful : ∀ (T : Over S) (x y : yoneda.obj T ⟶ yoneda.obj U)
    (β : a.obj (CostructuredArrow.mk x) ⟶ a.obj (CostructuredArrow.mk y)),
    F.p.IsHomLift (𝟙 T) β →
      ∃! r : {r : yoneda.obj T ⟶ yoneda.obj R //
        r ≫ yoneda.map s = x ∧ r ≫ yoneda.map t = y},
        schemeGroupoidPresentationArrow s t a arrows x y r = β
  locally_surjective : ∀ z : F.obj,
    ∃ V : Sieve (F.p.obj z), V ∈ (Scheme.fppfTopology.over S) (F.p.obj z) ∧
      ∀ (T : Over S) (f : T ⟶ F.p.obj z), V f →
        ∃ (x : yoneda.obj T ⟶ yoneda.obj U)
          (β : a.obj (CostructuredArrow.mk x) ⟶ z), F.p.IsHomLift f β
  composition : ∀ (T : Over S) (x y z : yoneda.obj T ⟶ yoneda.obj U)
    (r : {r : yoneda.obj T ⟶ yoneda.obj R //
      r ≫ yoneda.map s = x ∧ r ≫ yoneda.map t = y})
    (q : {q : yoneda.obj T ⟶ yoneda.obj R //
      q ≫ yoneda.map s = y ∧ q ≫ yoneda.map t = z})
    (d : {d : yoneda.obj T ⟶ yoneda.obj R //
      d ≫ yoneda.map s = x ∧ d ≫ yoneda.map t = z})
    (p : T.left ⟶ pullback s.left t.left),
    p ≫ pullback.fst s.left t.left = (yoneda.preimage q.val).left →
    p ≫ pullback.snd s.left t.left = (yoneda.preimage r.val).left →
    p ≫ c = (yoneda.preimage d.val).left →
      schemeGroupoidPresentationArrow s t a arrows x y r ≫
        schemeGroupoidPresentationArrow s t a arrows y z q =
          schemeGroupoidPresentationArrow s t a arrows x z d

end CategoryTheory
