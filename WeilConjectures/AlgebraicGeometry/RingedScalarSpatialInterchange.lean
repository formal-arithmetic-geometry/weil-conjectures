/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRefinementData
import WeilConjectures.AlgebraicGeometry.RingedScalarSpatialOrdinaryEquation
import WeilConjectures.AlgebraicGeometry.RingedScalarSpatialDescent

/-! # Scalar and spatial inverse-image interchange

Source: Stacks Project, sites-cohomology.tex, Tags 0D6D and 0FPI; the agent
mixed scalar/geometric calculation for the prescribed ringed presentations.
(blueprint: lem-pur-ringed-scalar-spatial-interchange).

The equation holds on the entire ordinary unbounded derived category, in both
ordinary and vertical-sequence-site modes. No evaluation functor is applied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules.RingedRefinement

/-- The prescribed scalar inverse-image comparison commutes with spatial composition,
including transport along a specified equality of composites. Taking `k = f ≫ g`
and `h = rfl` gives the untransported equation. Functor associators are displayed.

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D
(`lemma-derived-pullback-composition`) and Tag 0FPI
(`lemma-adjoints-push-pull-compatibility`); agent mixed ringed-site calculation.

Proof. By equality elimination on `h` take `k = f ≫ g`; both equality transports
become identities (`eqToHom_refl`, `Functor.map_id`, `Category.comp_id`). The ordinary
inverse-image equation `ordinaryScalarSpatialEquation` (sectionwise restriction/direct-image
rectangle and conjugation, blueprint new-ringed-scalar-spatial-ordinary-equation) is the
hypothesis of `ringedScalarSpatialDescent` (normalized K-flat finite-word descent, blueprint
new-ringed-scalar-spatial-descent), whose conclusion is the untransported equation. In
systems mode both run on the vertical sequence site itself; no evaluation functor and no
equation about right-adjunction mates is used.
(blueprint: lem-pur-ringed-scalar-spatial-interchange). -/
theorem scalarSpatialInterchange
    (m : SheafOfModules.OpenTensorNormalization.Mode) (T : Scheme.{u})
    (c : Coefficients m T) (o : Calculus c)
    (p : Spatial o) (sc : ScalarComparisons o)
    {A B : Rings m T} (a : A ⟶ B) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W) (k : U ⟶ W) (h : f ≫ g = k) :
    (Functor.associator (o.scalar W a).T
      (o.operation g B).left (o.operation f B).left).hom ≫
        Functor.whiskerLeft (o.scalar W a).T ((p.pullComp f g B).hom ≫
          eqToHom (congrArg (fun t ↦ (o.operation t B).left) h)) ≫
        (sc.pull k a).hom =
      Functor.whiskerRight (sc.pull g a).hom (o.operation f B).left ≫
        (Functor.associator (o.operation g A).left
          (o.scalar V a).T (o.operation f B).left).hom ≫
        Functor.whiskerLeft (o.operation g A).left (sc.pull f a).hom ≫
        (Functor.associator (o.operation g A).left
          (o.operation f A).left (o.scalar U a).T).inv ≫
        Functor.whiskerRight ((p.pullComp f g A).hom ≫
          eqToHom (congrArg (fun t ↦ (o.operation t A).left) h))
          (o.scalar U a).T := by
  subst k
  simpa only [eqToHom_refl, Functor.map_id, Category.comp_id] using
    ringedScalarSpatialDescent m T c o p sc a f g
      (ordinaryScalarSpatialEquation m T c o p sc a f g)

end SheafOfModules.RingedRefinement
