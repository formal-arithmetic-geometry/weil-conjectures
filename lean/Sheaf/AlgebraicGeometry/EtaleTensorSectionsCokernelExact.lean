/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Local kernel-image comparison for tensor sections

Source: Stacks Project, Tags 070S(2) and 03FH(1).
(blueprint: lem-sc-etale-tensor-sections-cokernel-exact)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- The sheafified tensor-section sequence of a module cokernel is exact in the middle.
Source: Stacks Project, Descent, Tag 070S(2), and Tag 03FH(1).
(blueprint: lem-sc-etale-tensor-sections-cokernel-exact)

Proof: For an etale object U, tensor pullback carries the module cokernel of phi
to the cokernel of its pullback because it is a left adjoint. The module cokernel
is the sheafification of the sectionwise quotient. Therefore a section of the
pullback of G whose image vanishes in the pullback cokernel locally comes from
the pullback of F, on a Zariski covering of U. Open immersions in this covering
are etale over X; their tensor-section restrictions are the usual restrictions
under the unit-normalized open pullback comparison. Hence the kernel presheaf
of beta is locally the image of alpha. Conversely every image section is in
the kernel since phi composed with its cokernel projection is zero. After
universe lift this local kernel-image equality persists. Sheafification is
exact for abelian presheaves: the image sheaf is the sheafification of the
sectionwise image, and the kernel is the sheafification of the sectionwise
kernel. Local equality gives equality of these sheaves, which is the asserted
exactness. This asserts only middle exactness, not surjectivity onto the last
term; local lifting of arbitrary cokernel sections is a separate assertion.
For the empty scheme or zero morphism the same argument applies. -/
theorem etaleTensorSections_cokernel_exact {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G)
    (α : etaleTensorSectionsPresheaf F ⟶ etaleTensorSectionsPresheaf G)
    (β : etaleTensorSectionsPresheaf G ⟶ etaleTensorSectionsPresheaf (cokernel φ))
    (hα : ∀ U : X.Etaleᵒᵖ, α.app U = ((tensorPullback U.unop.hom).map φ).app ⊤)
    (hβ : ∀ U : X.Etaleᵒᵖ,
      β.app U = ((tensorPullback U.unop.hom).map (cokernel.π φ)).app ⊤)
    (w : ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight α AddCommGrpCat.uliftFunctor.{u + 1, u})) ≫
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight β AddCommGrpCat.uliftFunctor.{u + 1, u})) = 0) :
    (ShortComplex.mk
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight α AddCommGrpCat.uliftFunctor.{u + 1, u}))
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (Functor.whiskerRight β AddCommGrpCat.uliftFunctor.{u + 1, u})) w).Exact := by sorry

end
end AlgebraicGeometry.Scheme.Modules
