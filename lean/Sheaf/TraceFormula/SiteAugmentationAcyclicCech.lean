/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.CategoryTheory.SliceSiteSimplicialAugmentation
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import Sheaf.CategoryTheory.Sites.GeometricMorphism

/-!
# Čech computation for componentwise acyclic sheaves on a total slice site

Source: Stacks Project, `spaces-simplicial.tex`, Tags 0D79 and 0D7A,
including the double-complex proof; `sites.tex`, Tag 09W9
(blueprint: lem-trf-site-augmentation-acyclic-cech).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SimplicialSlice

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

open SimplicialSliceSite

/-- An augmentation as a simplicial object of the slice, with its actual arrows.
Source: Stacks, section-hypercovering
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
abbrev augmentedOver (A : SimplicialObject.Augmented C) : SimplicialObject (Over A.right) where
  obj p := Over.mk (A.hom.app p)
  map α := Over.homMk (A.left.map α) (by simp)
  map_id p := by ext; simp
  map_comp α β := by ext; simp

/-- Augmentation component with explicit endpoints. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
def augmentationMap (A : SimplicialObject.Augmented C) (p : SimplexCategoryᵒᵖ) :
    A.left.obj p ⟶ A.right := A.hom.app p

/-- Abelian sheaves on the recorded total slice site. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
abbrev AbelianSheaf (J : GrothendieckTopology C) (U : SimplicialObject C) :=
  Sheaf (topology J U) AddCommGrpCat.{max u v}

/-- Component restriction on the recorded total site. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
abbrev restriction (J : GrothendieckTopology C) (U : SimplicialObject C)
    (p : SimplexCategoryᵒᵖ) :=
  componentRestriction J U p AddCommGrpCat.{max u v}

/-- Augmentation inverse image from the recorded slice-site construction.
Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
abbrev inverse (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C) :=
  SimplicialSliceSite.inverse J (augmentedOver A) AddCommGrpCat.{max u v}

/-- The right adjoint determined by the recorded augmentation inverse image.
Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def direct (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) :
    AbelianSheaf J A.left ⥤ Sheaf (J.over A.right) AddCommGrpCat.{max u v} :=
  (inverse J A).rightAdjoint

/-- The recorded augmentation adjunction on abelian sheaves. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable abbrev adjunction (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) :=
  abelianAdjunction J (augmentedOver A)

/-- Grothendieck structure on abelian sheaves, transported from the small model.
Source: Stacks, Injectives, Tag 01DP; Mathlib's essentially-small-site theorem
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable instance abelianSheafGrothendieck (J : GrothendieckTopology C) :
    IsGrothendieckAbelian.{max u v} (Sheaf J AddCommGrpCat.{max u v}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall' J AddCommGrpCat.{max u v}


/-- The test object `(T ×ₓ Uₚ → Uₚ)` of the total site, as a functor of `T → X`.
Source: Stacks, Tag 09W9 and Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def test (A : SimplicialObject.Augmented C) (p : SimplexCategoryᵒᵖ) :
    Over A.right ⥤ Total A.left :=
  Over.pullback (augmentationMap A p) ⋙ component A.left p

/-- The map of test objects attached to a simplicial operator, with the canonical
map on the pullbacks. Source: Stacks, Tags 09W9 and 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def testOperatorApp (A : SimplicialObject.Augmented C)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) (T : Over A.right) :
    (test A p).obj T ⟶ (test A q).obj T where
  left := pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ A.left.map α) (by
      have h : A.left.map α ≫ augmentationMap A q = augmentationMap A p := by
        simp [augmentationMap]
      simp [Category.assoc, h, pullback.condition])
  right := α
  w := by simp [test, component]

/-- Naturality of the canonical pullback map. Source: Stacks, Tag 09W9
(blueprint: lem-trf-site-augmentation-acyclic-cech).
Proof: The two composites have the same projection to T and to U_q. The pullback
universal property identifies their left components, and their index maps coincide. -/
theorem testOperator_naturality (A : SimplicialObject.Augmented C)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) {T S : Over A.right} (f : T ⟶ S) :
    (test A p).map f ≫ testOperatorApp A α S =
      testOperatorApp A α T ≫ (test A q).map f := by
  sorry

/-- The natural transformation on test objects induced by a simplicial operator.
Source: Stacks, Tags 09W9 and 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def testOperator (A : SimplicialObject.Augmented C)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) : test A p ⟶ test A q where
  app := testOperatorApp A α
  naturality := fun {_ _} f ↦ testOperator_naturality A α f

/-- Continuity of the test functor, a composite of pullback and component inclusion.
Source: Stacks, Tag 09W9
(blueprint: lem-trf-site-augmentation-acyclic-cech).
Proof: Pullback between slice sites is continuous; the component inclusion is
continuous for the vertical topology. Composition preserves continuity. -/
theorem test_continuous (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) (p : SimplexCategoryᵒᵖ) :
    (test A p).IsContinuous (J.over A.right) (topology J A.left) := by
  sorry

attribute [instance] test_continuous

/-- The p-th direct-image component functor. Its sections on T are literally
`F(T ×ₓ Uₚ → Uₚ)`, so this is b_{p,*}F_p. Source: Stacks, Tag 09W9
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def componentDirect (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) (p : SimplexCategory) :
    AbelianSheaf J A.left ⥤ Sheaf (J.over A.right) AddCommGrpCat.{max u v} :=
  (test A (op p)).sheafPushforwardContinuous _ _ _

/-- The coface or codegeneracy morphism on component direct images is restriction
along the canonical pullback map. By adjunction this is precisely the mate of
`F_p → u_* u⁻¹ F_p → u_* F_q`. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def componentDirectMap (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) {p q : SimplexCategory} (α : p ⟶ q) :
    componentDirect J A p ⟶ componentDirect J A q :=
  Functor.sheafPushforwardContinuousNatTrans (testOperator A α.op) _ _ _

/-- The canonical maps satisfy the cosimplicial identity law. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech).
Proof: Pullback projections identify the test map for an identity with the identity;
restriction of a sheaf along an identity is the identity natural transformation. -/
theorem componentDirectMap_id (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) (p : SimplexCategory) :
    componentDirectMap J A (𝟙 p) = 𝟙 (componentDirect J A p) := by
  sorry

/-- The canonical maps satisfy the cosimplicial composition law. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech).
Proof: The pullback universal property identifies the composite test map with the
map for the composite. Contravariant restriction reverses composition a second time. -/
theorem componentDirectMap_comp (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) {p q r : SimplexCategory}
    (α : p ⟶ q) (β : q ⟶ r) :
    componentDirectMap J A (α ≫ β) = componentDirectMap J A α ≫
      componentDirectMap J A β := by
  sorry

/-- Cosimplicial component direct images, natural in F. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def cosimplicialDirect (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) :
    SimplexCategory ⥤
      (AbelianSheaf J A.left ⥤ Sheaf (J.over A.right) AddCommGrpCat.{max u v}) where
  obj := componentDirect J A
  map := componentDirectMap J A
  map_id := componentDirectMap_id J A
  map_comp := componentDirectMap_comp J A

/-- The alternating coface complex, using Mathlib's alternating complex rather than
an independently chosen differential. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def cechFunctor (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) :
    AbelianSheaf J A.left ⥤
      CochainComplex (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) ℕ :=
  (cosimplicialDirect J A).flip ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

end CategoryTheory.SimplicialSlice

namespace CategoryTheory.SimplicialSlice

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- Component localization direct image, given by pullback on test objects.
Source: Stacks, Tag 09W9
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def localizationDirect (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) (p : SimplexCategoryᵒᵖ) :
    Sheaf (J.over (A.left.obj p)) AddCommGrpCat.{max u v} ⥤
      Sheaf (J.over A.right) AddCommGrpCat.{max u v} :=
  (Over.pullback (augmentationMap A p)).sheafPushforwardContinuous
    AddCommGrpCat.{max u v} (J.over A.right) (J.over (A.left.obj p))

/-- Localization adjunction on abelian sheaves. Source: Stacks, Tag 09W9
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def localizationAdjunction (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) (p : SimplexCategoryᵒᵖ) :
    J.overMapPullback AddCommGrpCat.{max u v} (augmentationMap A p) ⊣
      localizationDirect J A p :=
  (Over.mapPullbackAdj (augmentationMap A p)).sheafPushforwardContinuous
    (J.over (A.left.obj p)) (J.over A.right)

set_option backward.isDefEq.respectTransparency false in
/-- The edge is the adjoint of the degree-zero component of the counit, exactly as
in the node. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def edge (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) (F : AbelianSheaf J A.left) :
    (direct J A).obj F ⟶ ((cechFunctor J A).obj F).X 0 :=
  (localizationAdjunction J A (op (SimplexCategory.mk 0))).homEquiv _ _
    ((restriction J A.left (op (SimplexCategory.mk 0))).map ((adjunction J A).counit.app F))

/-- The adjoint counit edge is killed by the first alternating differential.
Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech).
Proof: Naturality of the counit with respect to the two vertices of [1] gives
equal face maps after e. Their difference is the alternating differential in degree zero. -/
theorem edge_comp_d (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) (F : AbelianSheaf J A.left) :
    edge J A F ≫ ((cechFunctor J A).obj F).d 0 1 = 0 := by
  sorry

/-- The augmentation direct image is additive. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech).
Proof: The right adjoint preserves finite products. In the two abelian sheaf
categories these are biproducts, so this implies additivity. -/
theorem direct_additive (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) : (direct J A).Additive := by
  sorry

/-- Component localization direct image is additive. Source: Stacks, Tag 09W9
(blueprint: lem-trf-site-augmentation-acyclic-cech).
Proof: It is precomposition on abelian presheaves. Hence it preserves the
sectionwise addition of natural transformations. -/
theorem localizationDirect_additive (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) (p : SimplexCategoryᵒᵖ) :
    (localizationDirect J A p).Additive := by
  sorry

attribute [instance] direct_additive localizationDirect_additive

/-- The actual nonnegative Čech complex extended by zero into negative degrees,
viewed in the category of bounded below complexes. Source: Stacks, Tag 0D79
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def cechPlusFunctor (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) :
    AbelianSheaf J A.left ⥤
      CochainComplex.Plus (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) where
  obj F := ⟨((cechFunctor J A).obj F).extend ComplexShape.embeddingUpNat,
    ⟨0, inferInstance⟩⟩
  map f := ObjectProperty.homMk
    ((ComplexShape.embeddingUpNat.extendFunctor _).map ((cechFunctor J A).map f))

universe w w'

variable (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C)
    [HasDerivedCategory.{w} (Sheaf (J.over A.right) AddCommGrpCat.{max u v})]

/-- The Čech complex as a functor to the bounded below derived category.
Source: Stacks, Tags 0D79 and 0D7A
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def cechDerivedFunctor :
    AbelianSheaf J A.left ⥤
      DerivedCategory.Plus (Sheaf (J.over A.right) AddCommGrpCat.{max u v}) :=
  cechPlusFunctor J A ⋙ DerivedCategory.Plus.Q

/-- The edge with target H⁰ of the derived Čech complex. The two final isomorphisms
are Mathlib's homology comparisons for extension by zero and localization.
Source: Stacks, Tags 0D79 and 0D7A
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
noncomputable def edgeH0 (F : AbelianSheaf J A.left) :
    (direct J A).obj F ⟶
      (DerivedCategory.Plus.homologyFunctor _ 0).obj ((cechDerivedFunctor J A).obj F) :=
  ((cechFunctor J A).obj F).liftCycles (edge J A F) 1
    (ComplexShape.next_eq' _ (by simp)) (edge_comp_d J A F) ≫
    ((cechFunctor J A).obj F).homologyπ 0 ≫
    (((cechFunctor J A).obj F).extendHomologyIso ComplexShape.embeddingUpNat
      (j := 0) (j' := 0) rfl).inv ≫
    (DerivedCategory.Plus.homologyFunctorObjQIso ((cechPlusFunctor J A).obj F) 0).inv

/-- The full subcategory of total sheaves whose component higher direct images vanish.
Source: Stacks, the componentwise acyclic case of Tag 0D7A
(blueprint: lem-trf-site-augmentation-acyclic-cech). -/
def IsComponentwiseAcyclic : ObjectProperty (AbelianSheaf J A.left) :=
  fun F ↦ ∀ (p q : ℕ), 0 < q →
    IsZero (((localizationDirect J A (op (SimplexCategory.mk p))).rightDerived q).obj
      ((restriction J A.left (op (SimplexCategory.mk p))).obj F))

/-- The counit edge identifies b_*F with the kernel, and a natural isomorphism on
the full subcategory of componentwise acyclic sheaves identifies C_b(F) with Rb_*F.
The equation on H⁰ uses the canonical derived unit to express the identity on b_*F.

Source: Stacks, Tags 0D79 and 0D7A, with the evaluation formula of Tag 09W9
(blueprint: lem-trf-site-augmentation-acyclic-cech).

Proof:
1. By the augmentation adjunction, maps G → b_*F are compatible families of maps
b_p⁻¹G → F_p. The two vertices of [1] impose exactly the degree-zero kernel
condition. Continue a kernel map along any vertex of [p]. Any two vertices are
joined by an order-preserving [1] → [p], so the continuations agree and obey all
simplicial operators. This gives the unique compatible family. Its degree-zero
mate is the edge defined above, proving the kernel universal property.
2. The augmentation spectral sequence (lem-trf-site-augmentation-spectral-sequence,
Stacks 0D7A) comes from the double complex b_{p,*}I_p^q for an injective resolution
of F. Its first page is R^q b_{p,*}F_p and its bottom differential is the alternating
face differential of cechFunctor. Its double-complex comparison is natural in F.
3. Componentwise acyclicity kills the positive rows. The comparison induces an
isomorphism in every cohomology degree, so the bounded-below derived-category
criterion (lem-weil-pbc-derived-plus-iso-on-cohomology) makes it an isomorphism.
The double-complex augmentation in degree zero is the mate of the counit. Thus
H⁰ of the comparison composed with edgeH0 is the canonical derived unit, giving
the required identity under the two b_*F identifications. -/
theorem site_augmentation_acyclic_cech
    [HasDerivedCategory.{w'} (AbelianSheaf J A.left)] :
    (∀ F : AbelianSheaf J A.left,
      Nonempty (IsLimit (KernelFork.ofι (edge J A F) (edge_comp_d J A F)))) ∧
    ∃ κ : (IsComponentwiseAcyclic J A).ι ⋙ cechDerivedFunctor J A ≅
        (IsComponentwiseAcyclic J A).ι ⋙
          DerivedCategory.Plus.singleFunctor (AbelianSheaf J A.left) 0 ⋙
            (direct J A).rightDerivedFunctorPlus,
      ∀ F : (IsComponentwiseAcyclic J A).FullSubcategory,
        edgeH0 J A F.obj ≫ (DerivedCategory.Plus.homologyFunctor _ 0).map (κ.hom.app F) =
          (direct J A).rightDerivedPlusSingleUnitHomology F.obj := by
  sorry

end CategoryTheory.SimplicialSlice
