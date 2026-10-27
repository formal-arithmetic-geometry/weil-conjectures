/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S5
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-! # Germ cocones on an étale scheme chart

Source: Stacks Project, Properties of Spaces, Tags 04KF and 04K2(4).
(blueprint: lem-sfb-space-chart-germ-cocone).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace
open SingleComplex

/-- A cocone on the small affine neighbourhoods extends to the affine pointed
neighbourhoods of a fixed étale scheme chart. Every such neighbourhood admits a
compatible small refinement. No universal property is asserted here.

Source: Stacks Project, Properties of Spaces, Tag 04KF, first equality, and
Tag 04K2(4), direct proof on pointed neighbourhoods
(blueprint: lem-sfb-space-chart-germ-cocone).

Proof: compose an affine pointed T-neighbourhood N with e. Étale composition
makes it a pointed X-neighbourhood. Refine at the geometric point in the existing
small affine basis; this gives M and a with the two displayed compatibility
identities. Define the N-component to be restriction along a followed by the
M-leg of c. Two choices have a common pointed affine refinement over N. The
cocone equations for c identify their restrictions there, so the component is
independent of the choice. Given a pointed transition N' -> N, choose a common
small refinement over N' for its chosen refinement and the pullback of the chosen
refinement of N. Functoriality of regular-function restriction and the cocone
identities then give naturality. The same common-refinement argument compares
this component with every compatible M and a, giving the final formula. This
constructs the required natural transformation and the refinement witnesses.
An empty scheme chart has no given t; no surjectivity of e is used. -/
theorem schemeChart_germCocone
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (T : Over S)
    (e : yoneda.obj T ⟶ X.obj.obj) (he : IsEtale e)
    (t : Over.mk s ⟶ T) (ht : yoneda.map t ≫ e = x)
    (c : Cocone (ringDiagram x)) :
    ∃ γ : Scheme.strictHenselizationDiagram t.left ⟶
        (Functor.const _).obj c.pt,
      (∀ N : Scheme.AffinePointedEtaleNeighborhood t.left,
        ∃ (M : Neighbourhood (Over.mk s) x)
          (a : ((neighbourhoodChart (x := x)).obj M).obj.left ⟶
            Over.mk (N.obj.1.hom ≫ T.hom)),
          (yoneda.map (a ≫ Over.homMk N.obj.1.hom) ≫ e =
            ((neighbourhoodChart (x := x)).obj M).obj.hom) ∧
          M.hom.left.left ≫ a.left = N.obj.2.left) ∧
      (∀ (N : Scheme.AffinePointedEtaleNeighborhood t.left)
        (M : Neighbourhood (Over.mk s) x)
        (a : ((neighbourhoodChart (x := x)).obj M).obj.left ⟶
          Over.mk (N.obj.1.hom ≫ T.hom)),
        yoneda.map (a ≫ Over.homMk N.obj.1.hom) ≫ e =
            ((neighbourhoodChart (x := x)).obj M).obj.hom →
        M.hom.left.left ≫ a.left = N.obj.2.left →
        γ.app (op N) = a.left.appTop ≫ c.ι.app (op M)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
