/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S5
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-! # Universality of the germ cocone on an étale chart

Source: Stacks Project, Properties of Spaces, Tags 04KF and 04K2(4).
(blueprint: lem-sfb-space-chart-germ-cocone-is-colimit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.AlgebraicSpace
open SingleComplex

/-- A germ-compatible cocone on a scheme chart is universal when the original
small affine space cocone is universal. This is the inverse germ construction;
it does not assert existence of a compatible cocone or a ring isomorphism.

Source: Stacks Project, Properties of Spaces, Tag 04K2(4), direct proof of the
stalk comparison, specialized to the structure sheaf as in Tag 04KF
(blueprint: lem-sfb-space-chart-germ-cocone-is-colimit).

Proof: let d be any cocone on the affine pointed T-neighbourhood diagram.
For a small pointed X-neighbourhood M, form M times_X T with its distinguished
geometric point (the point of M, t). The representability in the definition of
the étale map e makes this a scheme, étale over M and T. Choose an affine open
neighbourhood of that point. Pull a regular function on M back to this affine
neighbourhood and apply the corresponding leg of d. Common pointed affine
refinements prove independence of the open, naturality in M, and hence give a
cocone on ringDiagram x. Universality of c gives the induced map from c.pt to
d.pt. On a T-neighbourhood N, the pointed map from N to N times_X T given by
its identity and its structural map to T, followed by affine refinement,
shows that the induced map composes with the N-leg of γ to the N-leg of d.
For uniqueness, pull M back to T as above and refine also in the small basis.
The first projection and the assumed formula for γ show that any factorization
through γ has the stipulated composites with all legs of c. The uniqueness
part of c's universal property makes the two maps equal. Thus these maps,
factorization identities and uniqueness form IsColimit (Cocone.mk c.pt γ).
The construction uses only pointed refinements, and includes nonsurjective e. -/
theorem schemeChart_germCocone_isColimit
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (T : Over S)
    (e : yoneda.obj T ⟶ X.obj.obj) (he : IsEtale e)
    (t : Over.mk s ⟶ T) (ht : yoneda.map t ≫ e = x)
    (c : Cocone (ringDiagram x)) (hc : IsColimit c)
    (γ : Scheme.strictHenselizationDiagram t.left ⟶ (Functor.const _).obj c.pt)
    (hγ :
      ∀ (N : Scheme.AffinePointedEtaleNeighborhood t.left)
        (M : Neighbourhood (Over.mk s) x)
        (a : ((neighbourhoodChart (x := x)).obj M).obj.left ⟶
          Over.mk (N.obj.1.hom ≫ T.hom)),
        yoneda.map (a ≫ Over.homMk N.obj.1.hom) ≫ e =
            ((neighbourhoodChart (x := x)).obj M).obj.hom →
        M.hom.left.left ≫ a.left = N.obj.2.left →
        γ.app (op N) = a.left.appTop ≫ c.ι.app (op M)) :
    Nonempty (IsColimit (Cocone.mk c.pt γ)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
