/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TotalSiteSheafSystems
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Sites.GrothendieckTopos
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import WeilConjectures.CategoryTheory.Sites.GrothendieckTopos
import WeilConjectures.CategoryTheory.TotalSitePseudofunctor

/-!
# The equalizer direct image of an augmented simplicial topos

Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D70, lemma-augmentation-site
(blueprint: lem-trf-slice-site-augmentation-morphism).

For an order map `[p] → [q]`, the corresponding arrow of the index category is
`[q] → [p]`. Its inverse image goes from degree `p` to degree `q`.
The augmentation comparisons, transitions, and equalizer arrows below use this direction.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory Simplicial

namespace CategoryTheory.CoherentSitePseudofunctor

variable {F : LocallyDiscrete (SimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{w, w}}
  (D : CoherentSitePseudofunctor SimplexCategoryᵒᵖ F)
  (E : Type u) [Category.{v} E]

/-- The component geometric morphisms and coherent inverse-image identifications of
an augmentation. For `α : i ⟶ j` in `Δᵒᵖ`, the comparison is `f_α⁻¹ a_j⁻¹ ≅ a_i⁻¹`.
The last two fields are the unit and composition laws, with the canonical comparisons
of the system dependency inserted. Source: Stacks, Tag 0D70
(blueprint: lem-trf-slice-site-augmentation-morphism). -/
structure ToposAugmentation where
  component : ∀ i : SimplexCategoryᵒᵖ, GeometricMorphism (D.fibreSheaves i) E
  comparison : ∀ {i j : SimplexCategoryᵒᵖ} (α : i ⟶ j),
    (component j).inverse ⋙ D.inverseImage α ≅ (component i).inverse
  comparison_id : ∀ (i : SimplexCategoryᵒᵖ) (G : E),
    (comparison (𝟙 i)).hom.app G =
      (D.inverseImageId i).hom.app ((component i).inverse.obj G)
  comparison_comp : ∀ {i j k : SimplexCategoryᵒᵖ} (α : i ⟶ j) (β : j ⟶ k) (G : E),
    (D.inverseImageComp α β).hom.app ((component k).inverse.obj G) ≫
        (comparison (α ≫ β)).hom.app G =
      (D.inverseImage α).map ((comparison β).hom.app G) ≫ (comparison α).hom.app G

variable {D E}

namespace ToposAugmentation

variable (A : D.ToposAugmentation E)

/-- The canonical compatible system attached to a base object. Its transitions are
the supplied coherent identifications, and its laws are exactly their coherence laws.
Source: Stacks, Tag 0D70 (blueprint: lem-trf-slice-site-augmentation-morphism). -/
def system (G : E) : D.SheafSystem where
  obj i := (A.component i).inverse.obj G
  transition α := (A.comparison α).hom.app G
  transition_id i := A.comparison_id i G
  transition_comp α β := A.comparison_comp α β G

/-- The map of canonical systems induced by a base morphism, using naturality of
the augmentation comparisons. Source: Stacks, Tag 0D70
(blueprint: lem-trf-slice-site-augmentation-morphism). -/
def systemMap {G H : E} (f : G ⟶ H) : D.SheafSystemHom (A.system G) (A.system H) where
  app i := (A.component i).inverse.map f
  comm α := (A.comparison α).hom.naturality f

/-- The canonical direct-image transition, written as its transpose under `a_i⁻¹ ⊣ a_i*`.
It is the comparison inverse, followed by the inverse image of the component counit,
followed by the system transition. Equivalently this inserts the unit of `f_α` and
uses its transition, as in the displayed equalizer construction in Stacks, Tag 0D70
(blueprint: lem-trf-slice-site-augmentation-morphism). -/
noncomputable def pushTransition (S : D.SheafSystem) {i j : SimplexCategoryᵒᵖ} (α : i ⟶ j) :
    (A.component j).direct.obj (S.obj j) ⟶ (A.component i).direct.obj (S.obj i) :=
  (A.component i).adj.homEquiv _ _
    ((A.comparison α).inv.app ((A.component j).direct.obj (S.obj j)) ≫
      (D.inverseImage α).map ((A.component j).adj.counit.app (S.obj j)) ≫ S.transition α)

/-- The complete augmentation conclusion. The fibre isomorphisms specify the inverse
image on objects, morphisms, and transitions. The equalizer projection is the transpose
of the degree-zero counit component, so both its point and its embedding are fixed.
Finally `familyEquiv` identifies maps into that equalizer with all compatible families;
its component formula fixes the bijection as the adjunction bijection followed by fibre
restriction. In particular it is natural in both variables, rather than an unspecified
bijection. Source: Stacks, Tag 0D70
(blueprint: lem-trf-slice-site-augmentation-morphism). -/
structure Result (P : D.SheafSystemPresentation) where
  morphism : GeometricMorphism (Sheaf D.totalTopology (Type w)) E
  fibreIso : ∀ (G : E) (i : SimplexCategoryᵒᵖ),
    (P.system (morphism.inverse.obj G)).obj i ≅ (A.component i).inverse.obj G
  fibreIso_naturality : ∀ {G H : E} (f : G ⟶ H) (i : SimplexCategoryᵒᵖ),
    (P.map (morphism.inverse.map f)).app i ≫ (fibreIso H i).hom =
      (fibreIso G i).hom ≫ (A.component i).inverse.map f
  fibreIso_transition : ∀ (G : E) {i j : SimplexCategoryᵒᵖ} (α : i ⟶ j),
    (D.inverseImage α).map (fibreIso G j).hom ≫ (A.comparison α).hom.app G =
      (P.system (morphism.inverse.obj G)).transition α ≫ (fibreIso G i).hom
  equalizerι : ∀ X : Sheaf D.totalTopology (Type w),
    morphism.direct.obj X ⟶ (A.component (op ⦋0⦌)).direct.obj ((P.system X).obj (op ⦋0⦌))
  equalizerι_eq : ∀ X : Sheaf D.totalTopology (Type w),
    equalizerι X = (A.component (op ⦋0⦌)).adj.homEquiv _ _
      ((fibreIso (morphism.direct.obj X) (op ⦋0⦌)).inv ≫
        (P.map (morphism.adj.counit.app X)).app (op ⦋0⦌))
  equalizer_condition : ∀ X : Sheaf D.totalTopology (Type w),
    equalizerι X ≫ A.pushTransition (P.system X) (SimplexCategory.δ (0 : Fin 2)).op =
      equalizerι X ≫ A.pushTransition (P.system X) (SimplexCategory.δ (1 : Fin 2)).op
  equalizer_isLimit : ∀ X : Sheaf D.totalTopology (Type w),
    IsLimit (Fork.ofι (equalizerι X) (equalizer_condition X))
  familyEquiv : ∀ (G : E) (X : Sheaf D.totalTopology (Type w)),
    (G ⟶ morphism.direct.obj X) ≃ D.SheafSystemHom (A.system G) (P.system X)
  familyEquiv_app : ∀ (G : E) (X : Sheaf D.totalTopology (Type w))
    (f : G ⟶ morphism.direct.obj X) (i : SimplexCategoryᵒᵖ),
    (familyEquiv G X f).app i = (fibreIso G i).inv ≫
      (P.map (morphism.inverse.map f ≫ morphism.adj.counit.app X)).app i

/-- A coherent augmentation of a simplicial diagram of sites induces a geometric
morphism from its total topos. Its inverse image is the canonical system of component
inverse images, and its right adjoint is the degree-zero/degree-one equalizer, with
maps into it exactly the compatible component families.
Source: Stacks Project, Tag 0D70, lemma-augmentation-site and its vertex/edge argument
(blueprint: lem-trf-slice-site-augmentation-morphism).

Proof: (1) Use the total-site systems equivalence to realize the system with components
`a_n⁻¹ G` and the supplied comparison transitions. The unit and cocycle laws give a
system; naturality gives the component maps of the inverse-image functor.
(2) Each component inverse image preserves finite limits. Limits of systems are computed
componentwise, so the resulting total inverse image preserves finite limits.
(3) Transpose the two transitions for `[0] → [1]` with the component adjunctions. These
are `pushTransition` for the two opposite face maps. Their equalizer exists in the base
topos; its construction is functorial in the system.
(4) A map into this equalizer is a degree-zero component map satisfying the edge relation.
Propagate it to degree `n` along any vertex `[0] → [n]`. Any two vertices are joined by
an order map `[1] → [n]`, so the edge relation makes the result independent of the
vertex. Coherence gives compatibility with every simplicial operator, identities and
composition. Conversely any compatible family gives the degree-zero equalizer relation.
The constructions are inverse and natural in the base object and the total sheaf.
(5) These natural bijections give the adjunction. Together with (2) they give the stated
geometric morphism; (3) and (4) give its equalizer and compatible-family specifications. -/
theorem augmentation_morphism
    (h : ∀ (i j : SimplexCategoryᵒᵖ) (α : i ⟶ j),
      PreservesFiniteLimits (D.inverseImage α))
    (hE : IsGrothendieckTopos.{w} E) (P : D.SheafSystemPresentation) :
    Nonempty (A.Result P) := by
  sorry

end ToposAugmentation
end CategoryTheory.CoherentSitePseudofunctor
