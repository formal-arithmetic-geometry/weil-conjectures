/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.Sites.AbelianInverseImagePresentation
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects

/-!
# Exactness of geometric inverse image on abelian sheaves and modules

Source: Stacks Project, Modules on Sites, Tags 04JC, 03D2, 03DA and 03DB;
Sites, Proposition 00YV (2)
(blueprint: lem-trf-geometric-inverse-image-exact).
-/

@[expose] public section

universe w uC vC uD vD

open CategoryTheory.Limits

namespace CategoryTheory.GeometricMorphism

/-- Geometric inverse image induces exact functors on abelian sheaves and on modules
with transported scalars. The existence clauses supply the transports; the universal
clauses make exactness available for every normalized presentation of them.
Source: Stacks Project, Modules on Sites, 04JC (first assertion), 03D2, 03DA and 03DB;
Sites, 00YV (2) (blueprint: lem-trf-geometric-inverse-image-exact).

Proof, following the five steps of the node:
1. The adjunction and left exactness are `f.adj` and `f.leftExact`. The right adjoint
preserves limits (lem-weil-pbc-right-adjoint-preserves-limits). Identify abelian sheaves
with commutative group objects (lem-weil-pbc-sheaf-algebraic-structures-objects).
The adjunction lifts to those objects (lem-weil-pbc-adjunction-lifts-abelian-group-objects),
with the transported operations and the underlying set-sheaf adjunction. This gives an
abelian presentation, and applies to any presentation by its operation normalization.
2. Finite abelian-sheaf limits are sectionwise (lem-weil-pbc-sheafification-exact).
Their underlying sets are the same compatible tuples as in set sheaves
(lem-weil-pbc-site-sheaf-sets-limits-sectionwise). Applying `f.inverse` gives a limiting
underlying cone. Its unique factorizations are additive by joint uniqueness of the
projections, applied to addition, zero and negation. Thus abelian inverse image is left exact.
3. The lifted adjunction preserves colimits (lem-weil-pbc-left-adjoint-preserves-colimits),
in particular finite colimits and cokernels. This proves exactness as defined in
`def-galois-exact-functor`. Abelian sheaves are abelian categories
(lem-weil-pbc-site-sheaves-enough-injectives), so preservation of kernels and cokernels
also preserves images and exact sequences. Transported addition makes the functor additive.
4. Apply inverse image to the ring operations and module action through the finite-product
comparisons (03D2). Applying it to each axiom diagram proves all ring and module laws.
Naturality of the action gives linearity on maps. This supplies the algebraic presentation;
its underlying abelian functor is the one of steps 1--3, including its action on maps.
5. Scalar forgetting preserves limits and colimits
(lem-weil-pbc-module-sheaves-colimits-forgetful), and reflects isomorphisms: the inverse of
an invertible linear map is linear, sectionwise. The finite-limit and finite-colimit
comparisons for module inverse image become those of step 2 and step 3 after forgetting,
so they are isomorphisms. Hence module inverse image and its underlying-abelian-sheaf
functor are exact, including preservation of relation-map cokernels. The target ring
throughout is the transported ring itself, with no further change of scalars. -/
theorem geometric_inverse_image_exact
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))) :
    (∃ A : AbelianInverseImagePresentation f.inverse,
      exactFunctor _ _ A.functor) ∧
    (∀ A : AbelianInverseImagePresentation f.inverse,
      exactFunctor _ _ A.functor) ∧
    (∀ B : Sheaf J CommRingCat.{w},
      (∃ (BI : Sheaf K CommRingCat.{w}),
        Nonempty (SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
          f.inverse B BI)) ∧
      ∀ (BI : Sheaf K CommRingCat.{w})
        (I : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w}
          f.inverse B BI),
        exactFunctor _ _ I.modules ∧
        exactFunctor _ _ (I.modules ⋙ SheafOfModules.toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj BI))) := by
  sorry

end CategoryTheory.GeometricMorphism
