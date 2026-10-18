/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.TraceFormula.TotalSiteComponentRestriction
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exact injective augmentation on a total simplicial site

Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79, lemma-augmentation-cech-complex
(blueprint: lem-trf-total-site-injective-augmentation-exactness).

The component categories and their coherent inverse-image geometric morphisms are
represented by `TotalSiteSystemData`; `a` gives the component augmentations and their
identity/composition coherences, and `totalInverse` identifies every component inverse
image with the induced total inverse image.  The displayed maps are the adjoint mates of
the component transition maps, and the augmentation is the mate of the degree-zero
counit component.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w x y u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

/-- The direct-image comparison corresponding by adjunction to an identity
inverse-image comparison.  Source: Stacks Project, `spaces-simplicial.tex`,
the identity coherence in the simplicial augmentation (blueprint:
`lem-trf-total-site-injective-augmentation-exactness`). -/
noncomputable def augmentationDirectIdIso {E : Type u₁}
    [Category.{v₁} E] (m : GeometricMorphism E E)
    (h : m.inverse ≅ 𝟭 E) : m.direct ≅ 𝟭 E :=
  (conjugateIsoEquiv m.adj Adjunction.id) h.symm

/-- The direct-image comparison corresponding by adjunction to a composition
inverse-image comparison.  Source: Stacks Project, `spaces-simplicial.tex`,
the composition coherence in the simplicial augmentation (blueprint:
`lem-trf-total-site-injective-augmentation-exactness`). -/
noncomputable def augmentationDirectCompIso {E : Type u₁} {F : Type u₂} {G : Type u₃}
    [Category.{v₁} E] [Category.{v₂} F] [Category.{v₃} G]
    (m : GeometricMorphism E G) (f : GeometricMorphism F G)
    (g : GeometricMorphism E F)
    (h : m.inverse ≅ f.inverse ⋙ g.inverse) :
    m.direct ≅ g.direct ⋙ f.direct :=
  (conjugateIsoEquiv m.adj (f.adj.comp g.adj)) h.symm

/-- Data of a simplicial family of abelian sheaf categories with an augmentation to a
common abelian sheaf category.  The fields are the site morphisms, their identity and
composition coherences, the compatible-system presentation of the total site, the
component augmentation morphisms and their coherences, and the induced total
augmentation.  Source: Stacks Project, Tags 09WF, 09WG and 0D79
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
structure TotalSiteAugmentationData
    (A : SimplexCategoryᵒᵖ → Type v)
    [∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]
    (T : Type u) [Category.{w} T] [Abelian T]
    (D : Type x) [Category.{y} D] [Abelian D] where
  u : ∀ {i j : SimplexCategoryᵒᵖ}, (j ⟶ i) →
    GeometricMorphism (A j) (A i)
  pullId : ∀ i, (u (𝟙 i)).inverse ≅ 𝟭 (A i)
  pullComp : ∀ {_i _j k : SimplexCategoryᵒᵖ} (f : _j ⟶ _i) (g : k ⟶ _j),
    (u (g ≫ f)).inverse ≅ (u f).inverse ⋙ (u g).inverse
  system : TotalSiteSystemData A (fun {_i _j} f ↦ (u f).inverse)
    pullId pullComp T
  a : ∀ i, GeometricMorphism (A i) D
  aComp : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i),
    (a j).direct ≅ ((u f).comp (a i)).direct
  aComp_id : ∀ i,
    (aComp (𝟙 i)).trans
        ((Functor.isoWhiskerRight
            (augmentationDirectIdIso (u (𝟙 i)) (pullId i)) (a i).direct).trans
          (Functor.leftUnitor (a i).direct)) = Iso.refl _
  aComp_comp : ∀ {i j k : SimplexCategoryᵒᵖ} (f : j ⟶ i) (g : k ⟶ j),
    (aComp (g ≫ f)).trans
        ((Functor.isoWhiskerRight
            (augmentationDirectCompIso (m := u (g ≫ f)) (f := u f) (g := u g)
              (pullComp f g)) (a i).direct).trans
          (Functor.associator (u g).direct (u f).direct (a i).direct)) =
      (aComp g).trans (Functor.isoWhiskerLeft (u g).direct (aComp f))
  total : GeometricMorphism T D
  totalInverse : ∀ i, (a i).inverse ≅ total.inverse ⋙ system.component i
  totalInverse_transition : ∀ {i j : SimplexCategoryᵒᵖ} (f : j ⟶ i) (G : D),
    system.transition (total.inverse.obj G) i j f =
      (u f).inverse.map ((totalInverse i).inv.app G) ≫
        (GeometricMorphism.inverseIso (aComp f)).hom.app G ≫
          (totalInverse j).hom.app G

namespace TotalSiteAugmentationData

variable {A : SimplexCategoryᵒᵖ → Type v}
  [∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]
  {T : Type u} [Category.{w} T] [Abelian T]
  {D : Type x} [Category.{y} D] [Abelian D]
  (S : TotalSiteAugmentationData A T D)

/-- The coface map induced by the transition along the `i`-th face, using the
adjunction `(u face).inverse ⊣ (u face).direct` and the coherence `aComp`.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79,
lemma-augmentation-cech-complex, Hom-adjunction construction
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
noncomputable def faceMap (I : T) (p : ℕ) (i : Fin (p + 2)) :
    (S.a (Opposite.op (SimplexCategory.mk p))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk p))).obj I) ⟶
      (S.a (Opposite.op (SimplexCategory.mk (p + 1)))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk (p + 1)))).obj I) := by
  exact
    (S.a (Opposite.op (SimplexCategory.mk p))).direct.map
        ((S.u (SimplexCategory.δ i).op).adj.homEquiv _ _
          (S.system.transition I _ _ (SimplexCategory.δ i).op)) ≫
      (S.aComp (SimplexCategory.δ i).op).inv.app _

/-- The alternating face differential in degree `p`.
Source: Stacks Project, `spaces-simplicial.tex`, Tags 0D78 and 0D79,
lemma-simplicial-resolution-augmentation and lemma-augmentation-cech-complex
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
noncomputable def differential (I : T) (p : ℕ) :
    (S.a (Opposite.op (SimplexCategory.mk p))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk p))).obj I) ⟶
      (S.a (Opposite.op (SimplexCategory.mk (p + 1)))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk (p + 1)))).obj I) :=
  ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • S.faceMap I p i

/-- The augmentation map, mate to the degree-zero component of the counit of the
induced total geometric morphism.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79,
lemma-augmentation-cech-complex, augmentation under the Hom adjunction
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
noncomputable def augmentation (I : T) :
    S.total.direct.obj I ⟶
      (S.a (Opposite.op (SimplexCategory.mk 0))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk 0))).obj I) :=
  (S.a (Opposite.op (SimplexCategory.mk 0))).adj.homEquiv (S.total.direct.obj I)
    ((S.system.component (Opposite.op (SimplexCategory.mk 0))).obj I)
    ((S.totalInverse (Opposite.op (SimplexCategory.mk 0))).hom.app
        (S.total.direct.obj I) ≫
      (S.system.component (Opposite.op (SimplexCategory.mk 0))).map
        (S.total.adj.counit.app I))

end TotalSiteAugmentationData

/-- For an injective abelian sheaf on the total simplicial site, the alternating
component direct-image complex augmented by the total direct image is a complex and is
exact in every degree.  Its augmentation and coface maps are the canonical maps
`TotalSiteAugmentationData.augmentation` and `TotalSiteAugmentationData.faceMap`, and
its differential is their alternating sum.  The result is natural for morphisms of
injective abelian sheaves.  No covering or hypercover condition on the augmentation,
and no cartesian-transition condition on the injective, is assumed.

Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79, lemma-augmentation-cech-complex,
injective case and its Hom-adjunction construction
(blueprint: lem-trf-total-site-injective-augmentation-exactness).

Proof for stage 3: use the exact augmented free simplicial resolution after component
restriction (Tag 0D78 and `lem-trf-total-site-component-restriction`), identify its Hom
complex with the displayed direct-image complex by the two adjunctions, apply the
extension property of `Injective`, and detect exactness by Yoneda.  The simplicial
identities and the explicit augmentation coherences give the complex equations and the
monicity of the initial arrow; the same adjunction identifications are functorial in a
morphism of injectives.
-/
theorem totalSite_injective_augmentation_exact
    {A : SimplexCategoryᵒᵖ → Type v}
    [∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]
    {T : Type u} [Category.{w} T] [Abelian T]
    {D : Type x} [Category.{y} D] [Abelian D]
    (S : TotalSiteAugmentationData A T D)
    (I : T) [Injective I] :
    (∃ h₀ : S.augmentation I ≫ S.differential I 0 = 0,
      Mono (S.augmentation I) ∧
        (ShortComplex.mk (S.augmentation I) (S.differential I 0) h₀).Exact) ∧
    (∀ p : ℕ, ∃ hₚ : S.differential I p ≫ S.differential I (p + 1) = 0,
      (ShortComplex.mk (S.differential I p) (S.differential I (p + 1)) hₚ).Exact) ∧
    ∀ {I' : T} [Injective I'] (f : I ⟶ I'),
      S.total.direct.map f ≫ S.augmentation I' =
        S.augmentation I ≫
          (S.a (Opposite.op (SimplexCategory.mk 0))).direct.map
            ((S.system.component (Opposite.op (SimplexCategory.mk 0))).map f) ∧
      ∀ p : ℕ,
        (S.a (Opposite.op (SimplexCategory.mk p))).direct.map
            ((S.system.component (Opposite.op (SimplexCategory.mk p))).map f) ≫
            S.differential I' p =
          S.differential I p ≫
            (S.a (Opposite.op (SimplexCategory.mk (p + 1)))).direct.map
              ((S.system.component (Opposite.op (SimplexCategory.mk (p + 1)))).map f) := by
  sorry

end CategoryTheory
