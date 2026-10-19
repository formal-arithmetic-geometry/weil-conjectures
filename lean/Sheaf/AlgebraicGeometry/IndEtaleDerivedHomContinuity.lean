/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleAffineContinuity
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Sheaf.TraceFormula.BoundedConstructibleDerivedHomContinuity
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineFibreProductTransition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.ConstructibleEtaleFiniteAffineSyzygy
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-!
# Derived sections and global Hom on an affine etale limit

Source: Bhatt--Scholze, The pro-etale topology for schemes, Corollary 5.1.6 and
Lemmas 6.3.14--6.3.16 (blueprint: lem-per-ind-etale-derived-hom-continuity).

The section comparison is the existing strict injective section model. For global Hom
we use the field-specific zero-differential model with degree n equal to Hom(K,L[n]).
Over a field, homology identifies the derived category of modules with graded vector
spaces, so this is a model of the full global derived Hom object, naturally in both
variables. In particular this construction is not appropriate for general coefficient
rings. All transition maps are the recorded derived inverse-image maps on morphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The graded field model of global derived Hom after inverse image along f.
Its degree n is precisely Hom(f* K,f* L[n]), with its actual A-module structure.
Source: Bhatt--Scholze, proof of Lemma 6.3.16, global RHom convention, and field
semisimplicity (blueprint: lem-per-ind-etale-derived-hom-continuity). -/
def indEtaleGlobalHomComplex {X Y : Scheme.{u}} {A : Type (u + 1)} [Field A]
    (f : Y ⟶ X) (K L : DerivedCategoryModule A X) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ where
  X n := ModuleCat.of A
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K ⟶
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj L)⟦n⟧)
  d _ _ := 0

/-- The canonical pullback of the global Hom model, degree by degree.
The formula applies the exact inverse-image functor to a derived morphism and uses
its canonical composition and shift comparisons.
Source: Bhatt--Scholze, proof of Lemma 6.3.16
(blueprint: lem-per-ind-etale-derived-hom-continuity). -/
def indEtaleGlobalHomPullback {X Y Z : Scheme.{u}} {A : Type (u + 1)} [Field A]
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ X) (w : h = g ≫ f)
    (K L : DerivedCategoryModule A X) :
    indEtaleGlobalHomComplex f K L ⟶ indEtaleGlobalHomComplex h K L where
  f n := ModuleCat.ofHom
    { toFun := boundedConstructibleDerivedHomPullback f g h w K L n
      map_add' := by
        intro a b
        simp [boundedConstructibleDerivedHomPullback, Functor.map_add,
          Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by
        intro r a
        simp [boundedConstructibleDerivedHomPullback, Functor.map_smul] }
  comm' := by intros; simp [indEtaleGlobalHomComplex]

/-- Pullback along the identity over X acts identically on the global Hom model.
Source: Bhatt--Scholze, proof of Lemma 6.3.16
(blueprint: lem-per-ind-etale-derived-hom-continuity).
Proof: the canonical inverse-image identity and composition comparisons satisfy the
unit law, and the exact functor's shift comparison satisfies the same unit law.
Substitution in the pullback formula cancels the two comparison isomorphisms. -/
theorem indEtaleGlobalHomPullback_id {X Y : Scheme.{u}} {A : Type (u + 1)} [Field A]
    (f : Y ⟶ X) (K L : DerivedCategoryModule A X) :
    indEtaleGlobalHomPullback f (𝟙 Y) f (Category.id_comp f).symm K L = 𝟙 _ := by
  sorry

/-- Pullback of global Hom is compatible with composition over X.
Source: Bhatt--Scholze, proof of Lemma 6.3.16
(blueprint: lem-per-ind-etale-derived-hom-continuity).
Proof: expand the two applications of exact inverse image. Naturality moves the
composition comparisons past the pulled-back morphism, associativity identifies
these comparisons with that for the composite, and compatibility with commShiftIso
identifies the target shift comparison. This proves equality in every degree. -/
theorem indEtaleGlobalHomPullback_comp {X Y Z W : Scheme.{u}}
    {A : Type (u + 1)} [Field A]
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ X) (w : h = g ≫ f)
    (g' : W ⟶ Z) (h' : W ⟶ X) (w' : h' = g' ≫ h)
    (K L : DerivedCategoryModule A X) :
    indEtaleGlobalHomPullback f g h w K L ≫
        indEtaleGlobalHomPullback h g' h' w' K L =
      indEtaleGlobalHomPullback f (g' ≫ g) h'
        (w'.trans ((congrArg (g' ≫ ·) w).trans (Category.assoc g' g f).symm)) K L := by
  sorry

/-- The diagram's identity law, including the given etale presentation's identity map.
Source: Bhatt--Scholze, Lemma 6.3.16, restriction functoriality
(blueprint: lem-per-ind-etale-derived-hom-continuity).
Proof: rewrite the functor D's identity law, then use
indEtaleGlobalHomPullback_id. Equality witnesses in Over are proof irrelevant. -/
theorem indEtaleGlobalHomDiagram_id {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {A : Type (u + 1)} [Field A] (D : I ⥤ X.Etale)
    (K L : DerivedCategoryModule A X) (i : Iᵒᵖ) :
    indEtaleGlobalHomPullback (D.obj i.unop).hom (D.map (𝟙 i).unop).left
      (D.obj i.unop).hom (MorphismProperty.Over.w (D.map (𝟙 i).unop)).symm K L =
        𝟙 (indEtaleGlobalHomComplex (D.obj i.unop).hom K L) := by
  sorry

/-- The diagram's composition law for every pair of arrows, including parallel arrows.
Source: Bhatt--Scholze, Lemma 6.3.16, restriction functoriality
(blueprint: lem-per-ind-etale-derived-hom-continuity).
Proof: rewrite D.map_comp and the left component of composition in Over, then apply
indEtaleGlobalHomPullback_comp. The commutative-triangle witnesses are proof irrelevant. -/
theorem indEtaleGlobalHomDiagram_comp {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {A : Type (u + 1)} [Field A] (D : I ⥤ X.Etale)
    (K L : DerivedCategoryModule A X) {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    indEtaleGlobalHomPullback (D.obj i.unop).hom (D.map (a ≫ b).unop).left
        (D.obj k.unop).hom (MorphismProperty.Over.w (D.map (a ≫ b).unop)).symm K L =
      indEtaleGlobalHomPullback (D.obj i.unop).hom (D.map a.unop).left
        (D.obj j.unop).hom (MorphismProperty.Over.w (D.map a.unop)).symm K L ≫
      indEtaleGlobalHomPullback (D.obj j.unop).hom (D.map b.unop).left
        (D.obj k.unop).hom (MorphismProperty.Over.w (D.map b.unop)).symm K L := by
  sorry

/-- The strict opposite-indexed diagram of global Hom complexes.
Source: Bhatt--Scholze, proof of Lemma 6.3.16
(blueprint: lem-per-ind-etale-derived-hom-continuity). -/
def indEtaleGlobalHomDiagram {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {A : Type (u + 1)} [Field A] (D : I ⥤ X.Etale)
    (K L : DerivedCategoryModule A X) : Iᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} A) ℤ where
  obj i := indEtaleGlobalHomComplex (D.obj i.unop).hom K L
  map f := indEtaleGlobalHomPullback (D.obj _).hom (D.map f.unop).left
    (D.obj _).hom (MorphismProperty.Over.w (D.map f.unop)).symm K L
  map_id i := indEtaleGlobalHomDiagram_id D K L i
  map_comp f g := indEtaleGlobalHomDiagram_comp D K L f g

/-- The limiting restriction maps are compatible with all stage transitions.
Source: Bhatt--Scholze, Lemma 6.3.16, restriction functoriality
(blueprint: lem-per-ind-etale-derived-hom-continuity).
Proof: apply indEtaleGlobalHomPullback_comp. The cone equation identifies the composite
underlying scheme map with the other cone leg, and proof irrelevance identifies the
Over witnesses. No limit property or geometric hypothesis is used in this identity. -/
theorem indEtaleGlobalHomCocone_naturality {I : Type u} [SmallCategory I]
    {X : Scheme.{u}} {A : Type (u + 1)} [Field A] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X)) (K L : DerivedCategoryModule A X)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (indEtaleGlobalHomDiagram D K L).map a ≫
        indEtaleGlobalHomPullback (D.obj j.unop).hom (c.π.app j.unop).left c.pt.hom
          (MorphismProperty.Over.w (c.π.app j.unop)).symm K L =
      indEtaleGlobalHomPullback (D.obj i.unop).hom (c.π.app i.unop).left c.pt.hom
        (MorphismProperty.Over.w (c.π.app i.unop)).symm K L := by
  sorry

/-- The actual restriction cocone to global Hom on the limiting etale scheme.
Source: Bhatt--Scholze, proof of Lemma 6.3.16
(blueprint: lem-per-ind-etale-derived-hom-continuity). -/
def indEtaleGlobalHomCocone {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {A : Type (u + 1)} [Field A] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X)) (K L : DerivedCategoryModule A X) :
    Cocone (indEtaleGlobalHomDiagram D K L) where
  pt := indEtaleGlobalHomComplex c.pt.hom K L
  ι :=
    { app := fun i ↦ indEtaleGlobalHomPullback (D.obj i.unop).hom
        (c.π.app i.unop).left c.pt.hom
        (MorphismProperty.Over.w (c.π.app i.unop)).symm K L
      naturality := fun i j f ↦ by
        exact (indEtaleGlobalHomCocone_naturality D c K L f).trans
          (Category.comp_id _).symm }


/-- The canonical filtered derived global Hom comparison: localize the actual
restriction map from the degreewise colimit of the strict complex diagram.
Source: Bhatt--Scholze, proof of Lemma 6.3.16
(blueprint: lem-per-ind-etale-derived-hom-continuity). -/
def indEtaleGlobalHomMap {I : Type u} [SmallCategory I] {X : Scheme.{u}}
    {A : Type (u + 1)} [Field A] (D : I ⥤ X.Etale)
    (c : Cone (D ⋙ Scheme.toProEt X)) (K L : DerivedCategoryModule A X) :=
  DerivedCategory.Q.map (colimit.desc _ (indEtaleGlobalHomCocone D c K L))

/-- The field Hom model is functorial in both arguments before localization.
Source: Bhatt--Scholze, Lemma 6.3.16, global derived Hom convention
(blueprint: lem-per-ind-etale-derived-hom-continuity). -/
def indEtaleGlobalHomBifunctor {X Y : Scheme.{u}} {A : Type (u + 1)} [Field A]
    (f : Y ⟶ X) :
    (DerivedCategoryModule A X)ᵒᵖ × DerivedCategoryModule A X ⥤
      CochainComplex (ModuleCat.{u + 1} A) ℤ where
  obj P := indEtaleGlobalHomComplex f P.1.unop P.2
  map m :=
    { f := fun n ↦ ModuleCat.ofHom
        { toFun := fun a ↦ (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
            m.1.unop ≫ a ≫
            ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map m.2)⟦n⟧'
          map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp]
          map_smul' := by intros; simp }
      comm' := by intros; simp [indEtaleGlobalHomComplex] }
  map_id P := by
    ext n a
    change (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map (𝟙 P.1.unop) ≫
      a ≫ ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map (𝟙 P.2))⟦n⟧' = a
    simp
  map_comp m m' := by
    ext n a
    change
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map (m'.1.unop ≫ m.1.unop) ≫
        a ≫ ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map (m.2 ≫ m'.2))⟦n⟧' =
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map m'.1.unop ≫
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map m.1.unop ≫
          a ≫ ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map m.2)⟦n⟧') ≫
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map m'.2)⟦n⟧'
    simp [Category.assoc]

/-- The restriction comparison is natural in both derived Hom variables.
Source: Bhatt--Scholze, proof of Lemma 6.3.16
(blueprint: lem-per-ind-etale-derived-hom-continuity).
Proof: in every degree the formula is precomposition, exact inverse image,
then postcomposition. Naturality of the composition and shift isomorphisms
moves the two variable morphisms through this formula. Functoriality of inverse
image then identifies the two resulting composites. -/
theorem indEtaleGlobalHomPullback_naturality {X Y Z : Scheme.{u}}
    {A : Type (u + 1)} [Field A]
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ X) (w : h = g ≫ f)
    (K K' L L' : DerivedCategoryModule A X) (a : K' ⟶ K) (b : L ⟶ L') :
    (indEtaleGlobalHomBifunctor f).map (X := (op K, L)) (Y := (op K', L')) (a.op, b) ≫
        indEtaleGlobalHomPullback f g h w K' L' =
      indEtaleGlobalHomPullback f g h w K L ≫
        (indEtaleGlobalHomBifunctor h).map (X := (op K, L)) (Y := (op K', L')) (a.op, b) := by
  sorry

/-- Pullback commutes with evaluation, expressed as composition with a shifted
morphism. Taking P to be the coefficient unit gives evaluation on sections.
Source: Bhatt--Scholze, proof of Lemma 6.3.16; Stacks, Tag 03DI
(blueprint: lem-per-ind-etale-derived-hom-continuity).
Proof: inverse image preserves composition. Its shift comparison is natural and
compatible with addition of shifts, and its composition isomorphisms are natural.
Substitution in ShiftedHom.comp cancels the intermediate comparison and gives
exactly the pullback of the evaluated morphism. -/
theorem indEtaleGlobalHomPullback_evaluation {X Y Z : Scheme.{u}}
    {A : Type (u + 1)} [Field A]
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ X) (w : h = g ≫ f)
    (P K L : DerivedCategoryModule A X) (p n m : ℤ) (hm : n + p = m)
    (a : boundedConstructibleDerivedHom f P K p)
    (b : boundedConstructibleDerivedHom f K L n) :
    boundedConstructibleDerivedHomPullback f g h w P L m (ShiftedHom.comp a b hm) =
      ShiftedHom.comp (boundedConstructibleDerivedHomPullback f g h w P K p a)
        (boundedConstructibleDerivedHomPullback f g h w K L n b) hm := by
  sorry

/-- This is a model of global derived Hom, naturally in both variables, rather than
merely a collection of unrelated cohomology groups.
Source: Bhatt--Scholze, proof of Lemma 6.3.16, and the global Hom complex computation
of Stacks, Tag 08J9 (blueprint: lem-per-ind-etale-derived-hom-continuity).
Proof: compute global derived Hom using an arbitrary representative of the source and
a K-injective representative of the target, as in
lem-sfb-derived-internal-hom-sections-model. Its degree n cohomology is canonically
Hom(K,L[n]), compatibly with precomposition and postcomposition. Every vector space
is projective and injective. Split the cycles-to-cohomology surjections in each degree
to obtain a quasi-isomorphism from the zero-differential cohomology complex. Two such
splittings are homotopic, and every acyclic complex of vector spaces is contractible.
Consequently homology is fully faithful on D(A), and the unique derived isomorphism
inducing the canonical cohomology identifications is natural in both variables. -/
theorem indEtaleGlobalHom_model {X Y : Scheme.{u}} {A : Type (u + 1)} [Field A]
    (f : Y ⟶ X) :
    Nonempty ((indEtaleGlobalHomBifunctor (A := A) f ⋙ DerivedCategory.Q) ≅
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.op.prod
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        Functor.uncurry.obj (derivedHom (ModuleCat.{u + 1} A) Y) ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} A) Y)) := by
  sorry

/-- Sections and global derived Hom commute with the specified affine etale limit.
The first comparison uses the strict section complexes of any bounded-below injective
representative of L. The second uses the field Hom model above; its degree n map is
exactly pullback on Hom(K,L[n]). Both colimits are taken degreewise and then localized,
which computes the filtered derived colimit since filtered module colimits are exact.
The pro-etale target is evaluation over U, equivalently sections on the slice over U.
No cohomological dimension bound and no upper bound or constructibility of L is assumed.

Source: Bhatt--Scholze, Corollary 5.1.6 and Lemmas 6.3.14--6.3.16
(blueprint: lem-per-ind-etale-derived-hom-continuity).

Proof, following the nine steps of the node:
1. Apply det-sf-comparison-affine-continuity to the supplied affine presentation and
   bounded-below injective representative. This gives the first comparison, including
   its restriction maps, in the ordinary pro-etale slice.
2. For Hom, use lem-weil-pbc-filtered-category-directed-cofinal and pass to a directed
   tail. Exact inverse image preserves the lower bound on L and the bounded
   constructibility of K: pull back its finite stratifications and constant finite
   module models, using lemma-constructible-pullback-stratification and
   lemma-constructible-pullback-constant.
3. The sheafification of the free module on an etale representable P_V has
   Hom(P_V,M)=M(V), by lem-weil-pbc-free-yoneda-presheaf-module and the sheafification
   adjunction. A bounded-below injective resolution and
   lem-pe-injective-complex-slice-section-model identify the shifted derived Hom
   groups with cohomology of the section complex.
4. Etale shriek base change identifies the pullbacks of P_V with the corresponding
   generators on the fibre products. These are affine with affine transitions.
   Apply lem-weil-pbc-derived-cohomology-continuity to their section complexes.
   The basis-element formula identifies the resulting map with actual pullback.
5. The objects for which every shifted Hom comparison is bijective form an extension
   and shift closed class. Apply Hom out of triangles, exact filtered group colimits,
   and the five lemma. Brutal filtrations include finite complexes of generators.
6. Resolve a constructible sheaf by a finite string of finite affine generators using
   lem-trf-constructible-etale-finite-affine-syzygy. The augmentation cone has its
   sole cohomology in degree -r. Exact inverse image preserves this bound.
7. For any fixed n and common lower bound b, choose r>n+1-b. Standard t-structure
   orthogonality kills Hom from this cone to L[n] and L[n+1]. The Hom exact sequence
   identifies the comparison with that of the finite generator complex, uniformly
   at every stage and at the limit; no dimension bound enters.
8. Finite Postnikov induction using lem-weil-pbc-truncation-triangle proves the
   assertion for bounded constructible K.
9. The global Hom model and exactness of filtered module colimits identify these
   canonical group comparisons with the cohomology of the displayed complex map.
   Thus it is a quasi-isomorphism and becomes invertible after localization.
   Pullback preserves composition and scalar actions; restriction preserves
   evaluation. The same formulas show naturality in K and L and independence of
   representatives. The helper laws record the actual composition coherences. -/
theorem indEtaleDerivedHomContinuity {I : Type u} [SmallCategory I] [IsCofiltered I]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (u + 1)) [Field A] [Finite A]
    (D : I ⥤ X.Etale) (c : Cone (D ⋙ Scheme.toProEt X))
    (_hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ i : I, IsAffine (D.obj i).left]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategoryModule A X) (_hK : DerivedCategory.isBoundedConstructible A X K)
    (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : ℤ) [J.IsStrictlyGE a] [∀ n : ℤ, Injective (J.X n)]
    (e : DerivedCategory.Q.obj J ≅ L.obj) :
    IsIso (ProEtale.affineContinuityProEtaleMap D c L.obj J e) ∧
      IsIso (indEtaleGlobalHomMap D c K L.obj) := by
  sorry

end AlgebraicGeometry.Etale
