/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Exact conservative restriction to a component of a total simplicial site

Source: Stacks Project, `spaces-simplicial.tex`, Tags 09WF, 09WG and 09WH
(blueprint: lem-trf-total-site-component-restriction).

The abstract data below records a family of abelian sheaf categories, the inverse-image
functors of the simplicial site morphisms with their unit and composition coherence, and
the actual compatible families and compatible morphisms. A presentation by a category `T`
is required to be fully faithful and essentially surjective onto these systems. Thus its
component functors are evaluations under an equivalence, as in Tag 09WF, rather than
arbitrary functors with transitions. Both unit laws and the cocycle law are explicit.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A compatible family of component objects, with the identity and composition laws.
Source: Stacks Project, Tag 09WF and the preceding system description
(blueprint: lem-trf-total-site-component-restriction). -/
structure TotalSiteCompatibleSystem
    (A : SimplexCategoryᵒᵖ → Type v) [∀ i, Category.{w} (A i)]
    (pull : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) → A i ⥤ A j)
    (pullId : ∀ i, pull (𝟙 i) ≅ 𝟭 (A i))
    (pullComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      pull (g ≫ f) ≅ pull f ⋙ pull g) where
  obj : ∀ i, A i
  transition : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i), (pull f).obj (obj i) ⟶ obj j
  transition_id : ∀ i, transition (𝟙 i) = (pullId i).hom.app (obj i)
  transition_comp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
    transition (g ≫ f) = (pullComp f g).hom.app (obj i) ≫
      (pull g).map (transition f) ≫ transition g

/-- Morphisms of the actual compatible families are compatible component maps.
Source: Stacks Project, Tag 09WF (blueprint: lem-trf-total-site-component-restriction). -/
structure TotalSiteCompatibleMorphism
    {A : SimplexCategoryᵒᵖ → Type v} [∀ i, Category.{w} (A i)]
    {pull : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) → A i ⥤ A j}
    {pullId : ∀ i, pull (𝟙 i) ≅ 𝟭 (A i)}
    {pullComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      pull (g ≫ f) ≅ pull f ⋙ pull g}
    (X Y : TotalSiteCompatibleSystem A pull pullId pullComp) where
  app : ∀ i, X.obj i ⟶ Y.obj i
  comm : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    (pull f).map (app i) ≫ Y.transition f = X.transition f ≫ app j

/-- A fully faithful, essentially surjective presentation of the compatible-system category.
`map_bijective` identifies each Hom set with ALL compatible component maps;
`essentially_surjective` realizes EVERY compatible family, up to compatible component
isomorphisms. Together these are the equivalence criterion, with evaluation given by
`component`. No arbitrary category with transitions qualifies. `pull_id_left`,
`pull_id_right`, and `pull_assoc` are the two unit laws and the full cocycle identity.
Source: Stacks Project, Tags 09WF and 09WG
(blueprint: lem-trf-total-site-component-restriction). -/
structure TotalSiteSystemData
    (A : SimplexCategoryᵒᵖ → Type v)
    [∀ i, Category.{w} (A i)]
    (pull : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) → A i ⥤ A j)
    (pullId : ∀ i, pull (𝟙 i) ≅ 𝟭 (A i))
    (pullComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      pull (g ≫ f) ≅ pull f ⋙ pull g)
    (T : Type u) [Category.{w} T] [Preadditive T] [∀ i, Preadditive (A i)] where
  pull_id_left : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i) (X : A i),
    (pullComp f (𝟙 j)).hom.app X ≫ (pullId j).hom.app ((pull f).obj X) =
      eqToHom (congrArg (fun q ↦ (pull q).obj X) (Category.id_comp f))
  pull_id_right : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i) (X : A i),
    (pullComp (𝟙 i) f).hom.app X ≫ (pull f).map ((pullId i).hom.app X) =
      eqToHom (congrArg (fun q ↦ (pull q).obj X) (Category.comp_id f))
  pull_assoc : ∀ {i j k l : SimplexCategoryᵒᵖ}
    (f : j ⟶ i) (g : k ⟶ j) (h : l ⟶ k) (X : A i),
    (pullComp f (h ≫ g)).hom.app X ≫ (pullComp g h).hom.app ((pull f).obj X) =
      eqToHom (congrArg (fun q ↦ (pull q).obj X) (Category.assoc h g f)) ≫
        (pullComp (g ≫ f) h).hom.app X ≫ (pull h).map ((pullComp f g).hom.app X)
  component : ∀ i, T ⥤ A i
  component_additive : ∀ i, (component i).Additive
  transition : ∀ (X : T) (i j : SimplexCategoryᵒᵖ) (f : j ⟶ i),
    (pull f).obj ((component i).obj X) ⟶ (component j).obj X
  transition_id : ∀ (X : T) (i : SimplexCategoryᵒᵖ),
    transition X i i (𝟙 i) = (pullId i).hom.app ((component i).obj X)
  transition_comp : ∀ (X : T) (i j k : SimplexCategoryᵒᵖ)
    (f : j ⟶ i) (g : k ⟶ j),
    transition X i k (g ≫ f) =
      (pullComp f g).hom.app ((component i).obj X) ≫
        (pull g).map (transition X i j f) ≫ transition X j k g
  transition_naturality : ∀ {X Y : T} (h : X ⟶ Y)
    (i j : SimplexCategoryᵒᵖ) (f : j ⟶ i),
    (pull f).map ((component i).map h) ≫ transition Y i j f =
      transition X i j f ≫ (component j).map h
  map_bijective : ∀ (X Y : T), Function.Bijective
    (fun h : X ⟶ Y ↦
      (⟨fun i ↦ (component i).map h, fun f ↦ transition_naturality h _ _ f⟩ :
        TotalSiteCompatibleMorphism
          ⟨fun i ↦ (component i).obj X, fun f ↦ transition X _ _ f,
            transition_id X, fun f g ↦ transition_comp X _ _ _ f g⟩
          ⟨fun i ↦ (component i).obj Y, fun f ↦ transition Y _ _ f,
            transition_id Y, fun f g ↦ transition_comp Y _ _ _ f g⟩))
  essentially_surjective : ∀ F : TotalSiteCompatibleSystem A pull pullId pullComp,
    ∃ (X : T) (e : ∀ i, (component i).obj X ≅ F.obj i),
      ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
        (pull f).map (e i).hom ≫ F.transition f = transition X i j f ≫ (e j).hom
  pull_exact : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    PreservesFiniteLimits (pull f) ∧ PreservesFiniteColimits (pull f)

attribute [instance] TotalSiteSystemData.component_additive

/-- For a simplicial site, component evaluation has an exact left adjoint, given by the
finite coproduct of inverse images. The component isomorphisms intertwine the transitions:
on the `φ` summand the transition along `ψ` is `(pullComp φ ψ).inv` followed by the
inclusion of the composite summand. Evaluation is exact, preserves injectives and
K-injectives termwise, and the family is conservative.
Source: Stacks Project, Tags 09WF, 09WG and 09WH
(blueprint: lem-trf-total-site-component-restriction).

Proof (postponed): the fully faithful and essentially surjective presentation identifies
`T` with all compatible systems (09WF). Construct the finite direct-sum system, using
`pullComp.inv` for its transitions. The unit and cocycle laws verify its system identities.
Compatible maps from this system are precisely maps from `G` to the degree-`n` component,
so it is the left adjoint (09WG). Inverse images are exact; finite sums are exact in an
abelian category, and exactness in the system category is componentwise. This proves
exactness of both functors. The adjunction and exactness imply injective preservation
by `lem-exc-rg-right-adjoint-preserves-injectives`; the exact-left-adjoint criterion
`CategoryTheory.Adjunction.preservesKInjectiveComplexes` from
`lem-weil-pbc-right-adjoint-preserves-kinjective` gives K-injective preservation (09WH).
Finally componentwise inverses are compatible, and full faithfulness gives the inverse
in `T`, proving conservativity. -/
theorem totalSiteComponentRestriction
    (A : SimplexCategoryᵒᵖ → Type v)
    [∀ i, Category.{w} (A i)]
    [∀ i, Abelian (A i)]
    (pull : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) → A i ⥤ A j)
    (pullId : ∀ i, pull (𝟙 i) ≅ 𝟭 (A i))
    (pullComp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
      pull (g ≫ f) ≅ pull f ⋙ pull g)
    (T : Type u) [Category.{w} T] [Abelian T]
    (S : TotalSiteSystemData A pull pullId pullComp T) :
    (∀ i, PreservesFiniteLimits (S.component i) ∧
      PreservesFiniteColimits (S.component i)) ∧
    (∀ n : ℕ, ∃ g : A (Opposite.op (SimplexCategory.mk n)) ⥤ T,
      Nonempty (g ⊣ S.component (Opposite.op (SimplexCategory.mk n))) ∧
      PreservesFiniteLimits g ∧ PreservesFiniteColimits g ∧
      (∀ G : A (Opposite.op (SimplexCategory.mk n)),
        ∃ e : ∀ m : SimplexCategoryᵒᵖ,
          (S.component m).obj (g.obj G) ≅
            ∐ fun φ : SimplexCategory.mk n ⟶ m.unop ↦ (pull φ.op).obj G,
          ∀ (m k : SimplexCategoryᵒᵖ) (ψ : k ⟶ m)
            (φ : SimplexCategory.mk n ⟶ m.unop),
            (pull ψ).map (Sigma.ι
                (fun θ : SimplexCategory.mk n ⟶ m.unop ↦ (pull θ.op).obj G) φ) ≫
              (pull ψ).map (e m).inv ≫ S.transition (g.obj G) m k ψ ≫ (e k).hom =
                (pullComp φ.op ψ).inv.app G ≫ Sigma.ι
                  (fun θ : SimplexCategory.mk n ⟶ k.unop ↦ (pull θ.op).obj G)
                  (φ ≫ ψ.unop)) ∧
      (∀ I : T, Injective I →
        Injective ((S.component (Opposite.op (SimplexCategory.mk n))).obj I)) ∧
      (∀ I : CochainComplex T ℤ, CochainComplex.IsKInjective I →
        CochainComplex.IsKInjective
          (((S.component (Opposite.op (SimplexCategory.mk n))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I))) ∧
    (∀ {X Y : T} (f : X ⟶ Y),
      (∀ i, IsIso ((S.component i).map f)) → IsIso f) := by
  sorry

end CategoryTheory
