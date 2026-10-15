/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Realizing diagrams of module sheaves on a product site

Source: Stacks Project, Sites, Tags 00Z4, 00Z8 and 00XA, and Modules on Sites,
Tags 03CV and 03DA; the explicit product-site construction in
(blueprint: lem-weil-pbc-diagram-site-realization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The product-site realization, including normalization of both equivalences on objects,
restrictions, diagram arrows and morphisms. Commutativity of the coefficient rings is
expressed by `hO`; their underlying rings are used by `ringedSiteModules`.

Source: Stacks Project, Sites, Tags 00Z4, 00Z8 and 00XA, and Modules on Sites,
Tags 03CV and 03DA; explicit agent construction
(blueprint: lem-weil-pbc-diagram-site-realization).

Proof plan:
1. Cover a sieve precisely when its vertical slice covers. Maximality and pullback
stability follow from the site axioms; the slice of a pullback contains the pullback
of the slice. Upward closure follows from local character.
2. Local character follows by testing vertical arrows. The vertical covering sieves
therefore generate exactly this topology.
3. Factor every product-category restriction into its two coordinate restrictions.
Functoriality says these commute, identifying presheaves with diagrams of presheaves.
4. Extend a matching family on a vertical sieve using the diagram arrows; gluing on
this generated sieve shows that each component of a sheaf is a sheaf.
5. Conversely glue the vertical part of a matching family. For any other arrow,
separatedness on the pullback of the vertical covering sieve gives compatibility.
6. These inverse constructions give the set-sheaf equivalence. The constant diagram
on the coefficient sheaf gives the ring sheaf with the stated underlying presheaf.
7. Apply the same constructions to modules, using the definition of sheaves of
modules in def-weil-sheaf-of-modules-category. Horizontal restrictions are linear
and vertical restrictions semilinear. Morphisms and addition are componentwise.
8. Kernels and cokernels of diagrams are componentwise by their universal properties;
thus evaluation is exact and the diagram module category is abelian.
9. The additive equivalence preserves kernel and cokernel universal properties, so
is exact, as is the resulting module evaluation on the product site.
10. Products, terminal objects and equalizers of set sheaves are sectionwise, and
those of diagrams are componentwise; hence evaluation preserves finite limits.
11. The right adjoint to diagram evaluation is `evaluationRightAdjoint`: at `k` its
value is the product over arrows `k ⟶ j`, and maps are induced by precomposition.
12. A map at `j` gives the transformation whose alpha-coordinate is its composite
with the diagram's alpha-map. The inverse takes the identity-coordinate at `j`.
Naturality proves these are inverse, giving the evaluation adjunction.
13. Transfer that adjunction across the set-sheaf equivalence. Together with finite
limit preservation it is the stated morphism of topoi. The coefficient presheaf
identity restricts at every `j` to the original coefficient sheaf. The normalized
module equivalence is the induced module inverse image: extension of scalars along
this identity is canonically the identity, via `a ⊗ x ↦ a • x` and `x ↦ 1 ⊗ x`.
Its exactness is the module-evaluation assertion of step 9. -/
theorem exists_diagramSite_realization
    (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{u})
    (hO : ∀ (U : Cᵒᵖ) (a b : O.obj.obj U), a * b = b * a) :
    ∃ (T : GrothendieckTopology (Jᵒᵖ × C)) (R : Sheaf T RingCat.{u})
      (E : Sheaf T (Type u) ≌ (J ⥤ Sheaf K (Type u)))
      (M : ringedSiteModules.{u} R ≌ (J ⥤ ringedSiteModules.{u} O)),
      (∀ (j : J) (U : C) (S : Sieve (op j, U)),
        S ∈ T (op j, U) ↔ S.functorPullback (Prod.sectR (op j) C) ∈ K U) ∧
      R.obj = (Prod.snd Jᵒᵖ C).op ⋙ O.obj ∧
      (∀ (F : Sheaf T (Type u)) (j : J),
        ((E.functor.obj F).obj j).obj = (Prod.sectR (op j) C).op ⋙ F.obj) ∧
      (∀ (F : Sheaf T (Type u)) (j k : J) (a : j ⟶ k) (U : C),
        HEq (((E.functor.obj F).map a).hom.app (op U))
          (F.obj.map (Prod.mkHom a.op (𝟙 U)).op)) ∧
      (∀ (F G : Sheaf T (Type u)) (f : F ⟶ G) (j : J) (U : C),
        HEq (((E.functor.map f).app j).hom.app (op U))
          (f.hom.app (op (op j, U)))) ∧
      (∀ (F : ringedSiteModules.{u} R) (j : J) (U : Cᵒᵖ),
        HEq (((M.functor.obj F).obj j).val.obj U)
          (F.val.obj ((Prod.sectR (op j) C).op.obj U))) ∧
      (∀ (F : ringedSiteModules.{u} R) (j : J) (U V : Cᵒᵖ) (f : U ⟶ V),
        HEq (((M.functor.obj F).obj j).val.map f)
          (F.val.map ((Prod.sectR (op j) C).op.map f))) ∧
      (∀ (F : ringedSiteModules.{u} R) (j k : J) (a : j ⟶ k) (U : C),
        HEq (((M.functor.obj F).map a).val.app (op U))
          (F.val.map (Prod.mkHom a.op (𝟙 U)).op)) ∧
      (∀ (F G : ringedSiteModules.{u} R) (f : F ⟶ G) (j : J) (U : Cᵒᵖ),
        HEq (((M.functor.map f).app j).val.app U)
          (f.val.app ((Prod.sectR (op j) C).op.obj U))) ∧
      M.functor.Additive ∧ PreservesFiniteLimits M.functor ∧
      PreservesFiniteColimits M.functor ∧
      (∀ j : J,
        Nonempty (E.functor ⋙ (evaluation J (Sheaf K (Type u))).obj j ⊣
          evaluationRightAdjoint (Sheaf K (Type u)) j ⋙ E.inverse) ∧
        PreservesFiniteLimits (E.functor ⋙ (evaluation J (Sheaf K (Type u))).obj j) ∧
        PreservesFiniteLimits
          (M.functor ⋙ (evaluation J (ringedSiteModules.{u} O)).obj j) ∧
        PreservesFiniteColimits
          (M.functor ⋙ (evaluation J (ringedSiteModules.{u} O)).obj j)) := by
  sorry

end CategoryTheory
