/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.TraceFormula.ComparisonInductionStep
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.Paper.SliceSiteLocalization
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Truncated higher direct images for a comparison of topologies

Source: Stacks Project, Tag 0EZA, lemma-V-implies-C-general; section-compare-general
and Tag 0EZE for the canonical derived maps
(blueprint: lem-trf-comparison-truncated-direct-images).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w d

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CategoryTheory.RefinedTopologyComparison

/-- Right-adjoint structure supplied by the geometric adjunction. Source: Stacks,
section-compare-general (blueprint: lem-trf-comparison-truncated-direct-images). -/
instance geometricDirectRightAdjoint {A : Type v} {B : Type w}
    [Category.{u} A] [Category.{u} B] (e : GeometricMorphism A B) :
    e.direct.IsRightAdjoint := e.adj.isRightAdjoint

/-- Direct images preserve limits. Source: Stacks, section-compare-general
(blueprint: lem-trf-comparison-truncated-direct-images). -/
instance geometricDirectFiniteLimits {A : Type v} {B : Type w}
    [Category.{u} A] [Category.{u} B] (e : GeometricMorphism A B) :
    PreservesFiniteLimits e.direct := inferInstance

/-- Direct images preserve injectives because the inverse image preserves finite limits.
Source: Stacks, Tag 0EZA, derived composition in the first paragraph
(blueprint: lem-trf-comparison-truncated-direct-images). -/
instance geometricDirectInjectives {A : Type v} {B : Type w}
    [Category.{u} A] [Category.{u} B] (e : GeometricMorphism A B) :
    e.direct.PreservesInjectiveObjects :=
  @Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits _ _ _ _ _ _ e.adj e.leftExact

/-- The inverse-image adjunction supplies its left-adjoint structure. Source: Stacks,
section-compare (blueprint: lem-trf-comparison-truncated-direct-images). -/
instance geometricInverseLeftAdjoint {A : Type v} {B : Type w}
    [Category.{u} A] [Category.{u} B] (e : GeometricMorphism A B) :
    e.inverse.IsLeftAdjoint := e.adj.isLeftAdjoint

/-- Inverse images are left exact by definition. Source: Stacks, section-compare
(blueprint: lem-trf-comparison-truncated-direct-images). -/
instance geometricInverseFiniteLimits {A : Type v} {B : Type w}
    [Category.{u} A] [Category.{u} B] (e : GeometricMorphism A B) :
    PreservesFiniteLimits e.inverse := e.leftExact

/-- Inverse images preserve finite colimits as left adjoints. Source: Stacks,
section-compare (blueprint: lem-trf-comparison-truncated-direct-images). -/
instance geometricInverseFiniteColimits {A : Type v} {B : Type w}
    [Category.{u} A] [Category.{u} B] (e : GeometricMorphism A B) :
    PreservesFiniteColimits e.inverse := inferInstance

/-- Inverse images of abelian sheaves are additive. Source: Stacks, section-compare
(blueprint: lem-trf-comparison-truncated-direct-images). -/
instance geometricInverseAdditive {A : Type v} {B : Type w}
    [Category.{u} A] [Category.{u} B] [Abelian A] [Abelian B]
    (e : GeometricMorphism A B) : e.inverse.Additive :=
  Functor.additive_of_preserves_binary_products e.inverse

/-- The augmentation F(H)[0] → RF(H[0]), obtained from the derived-functor unit.
Source: Stacks, Tag 0EZA, first paragraph
(blueprint: lem-trf-comparison-truncated-direct-images). -/
def sheafDerivedAugmentation {A : Type v} {B : Type w}
    [Category.{u} A] [Category.{u} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (H : A) :
    (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj H) ⟶
      F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj H) :=
  (Functor.mapHomotopyCategoryPlusSingleFunctorQhObjIso F 0 H).inv ≫
    F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor A 0).obj H)

variable {C : Type u} [SmallCategory C]
  (τ τ' : Precoverage C) (hτ : τ' ≤ τ) {X Y : C} (f : X ⟶ Y)

/-- The direct-image mate of the sectionwise restriction square. Source: Stacks,
equation-commutative-epsilon (blueprint: lem-trf-comparison-truncated-direct-images).
Its component is adjoint to the fine relocalization counit, with unchanged presheaf. -/
def relocalizationComparisonMate :
    (relocalization τ.toGrothendieck f).direct ⋙ (sliceComparison τ τ' hτ Y).direct ⟶
      (sliceComparison τ τ' hτ X).direct ⋙ (relocalization τ'.toGrothendieck f).direct :=
  Functor.whiskerLeft
      ((relocalization τ.toGrothendieck f).direct ⋙ (sliceComparison τ τ' hτ Y).direct)
      (relocalization τ'.toGrothendieck f).adj.unit ≫
    Functor.whiskerRight
      (Functor.whiskerRight (relocalization τ.toGrothendieck f).adj.counit
        (sliceComparison τ τ' hτ X).direct)
      (relocalization τ'.toGrothendieck f).direct

/-- The mate is the canonical commutation isomorphism of direct images. Source: Stacks,
equation-commutative-epsilon and Sites, localization of a morphism
(blueprint: lem-trf-comparison-truncated-direct-images).
Proof: localize the identity comparison morphism at the object f. Its inverse-image
square is the sheafification/restriction square; taking right adjoints identifies its
inverse mate with the displayed counit mate. The triangle identities prove invertibility. -/
theorem isIso_relocalizationComparisonMate :
    IsIso (relocalizationComparisonMate τ τ' hτ f) := by
  sorry

/-- The canonical square, oriented from coarse-after-comparison to comparison-after-fine.
Source: Stacks, equation-commutative-epsilon
(blueprint: lem-trf-comparison-truncated-direct-images). -/
def relocalizationComparisonIso :
    (sliceComparison τ τ' hτ X).direct ⋙ (relocalization τ'.toGrothendieck f).direct ≅
      (relocalization τ.toGrothendieck f).direct ⋙ (sliceComparison τ τ' hτ Y).direct := by
  letI := isIso_relocalizationComparisonMate τ τ' hτ f
  exact (asIso (relocalizationComparisonMate τ τ' hτ f)).symm

section Derived

variable [∀ Z : C, HasDerivedCategory.{d} (Sheaf (τ.toGrothendieck.over Z) AddCommGrpCat.{u})]
  [∀ Z : C, HasDerivedCategory.{d} (Sheaf (τ'.toGrothendieck.over Z) AddCommGrpCat.{u})]

/-- The canonical derived composition square, normalized by the derived-functor units.
Source: Stacks, Tag 0EZA, first derived identity
(blueprint: lem-trf-comparison-truncated-direct-images). -/
def derivedRelocalizationComparisonIso :
    (sliceComparison τ τ' hτ X).direct.rightDerivedFunctorPlus ⋙
        (relocalization τ'.toGrothendieck f).direct.rightDerivedFunctorPlus ≅
      (relocalization τ.toGrothendieck f).direct.rightDerivedFunctorPlus ⋙
        (sliceComparison τ τ' hτ Y).direct.rightDerivedFunctorPlus :=
  ((sliceComparison τ τ' hτ X).direct.rightDerivedFunctorPlusCompIso
      (relocalization τ'.toGrothendieck f).direct).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso (relocalizationComparisonIso τ τ' hτ f) ≪≫
    (relocalization τ.toGrothendieck f).direct.rightDerivedFunctorPlusCompIso
      (sliceComparison τ τ' hτ Y).direct

/-- The map a_H: apply Rf' to the comparison augmentation, then the canonical derived square.
Source: Stacks, Tag 0EZA and Tag 0EZE, truncation paragraph
(blueprint: lem-trf-comparison-truncated-direct-images). -/
def derivedDirectImageComparison
    (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u}) :
    (relocalization τ'.toGrothendieck f).direct.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((sliceComparison τ τ' hτ X).direct.obj H)) ⟶
      (sliceComparison τ τ' hτ Y).direct.rightDerivedFunctorPlus.obj
        ((relocalization τ.toGrothendieck f).direct.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj H)) :=
  (relocalization τ'.toGrothendieck f).direct.rightDerivedFunctorPlus.map
      (sheafDerivedAugmentation (sliceComparison τ τ' hτ X).direct H) ≫
    (derivedRelocalizationComparisonIso τ τ' hτ f).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj H)

/-- The specified b_H is the adjoint of a_H for the bounded-below derived adjunction.
Source: Stacks, Tag 0EZE, truncation paragraph
(blueprint: lem-trf-comparison-truncated-direct-images). -/
def adjointDerivedDirectImageComparison
    (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u}) :
    (sliceComparison τ τ' hτ Y).inverse.mapDerivedCategoryPlus.obj
        ((relocalization τ'.toGrothendieck f).direct.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((sliceComparison τ τ' hτ X).direct.obj H))) ⟶
      (relocalization τ.toGrothendieck f).direct.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj H) :=
  ((sliceComparison τ τ' hτ Y).adj.derivedPlus.homEquiv _ _).symm
    (derivedDirectImageComparison τ τ' hτ f H)

/-- Degree i of the augmentation followed by derived composition, expressed by the
Grothendieck bottom edge and the canonical direct-image square. Source: Stacks, Tag 0EZA
(blueprint: lem-trf-comparison-truncated-direct-images). -/
def comparisonBottom (i : ℕ) :
    (sliceComparison τ τ' hτ X).direct ⋙
        (relocalization τ'.toGrothendieck f).direct.rightDerived i ⟶
      ((relocalization τ.toGrothendieck f).direct ⋙
        (sliceComparison τ τ' hτ Y).direct).rightDerived i :=
  (sliceComparison τ τ' hτ X).direct.grothendieckBottomEdgeMap
      (relocalization τ'.toGrothendieck f).direct
      (Functor.isAcyclicComposablePair_of_preservesInjectiveObjects _ _) i ≫
    NatTrans.rightDerived (relocalizationComparisonIso τ τ' hτ f).hom i

/-- The relative Leray left edge, under canonical composition identifications. Source:
Stacks, Tag 0734 and Tag 0EZA (blueprint: lem-trf-comparison-truncated-direct-images). -/
def comparisonLeft (i : ℕ) :
    ((relocalization τ.toGrothendieck f).direct ⋙
        (sliceComparison τ τ' hτ Y).direct).rightDerived i ⟶
      (relocalization τ.toGrothendieck f).direct.rightDerived i ⋙
        (sliceComparison τ τ' hτ Y).direct :=
  (relocalization τ.toGrothendieck f).direct.grothendieckLeftEdgeMap
    (sliceComparison τ τ' hτ Y).direct
    (Functor.isAcyclicComposablePair_of_preservesInjectiveObjects _ _) i

/-- The specified canonical comparison c_i = H^i(a) followed by the Leray left edge.
Source: Stacks, Tag 0EZA (blueprint: lem-trf-comparison-truncated-direct-images). -/
def truncatedDirectImageComparison (i : ℕ) :
    (sliceComparison τ τ' hτ X).direct ⋙
        (relocalization τ'.toGrothendieck f).direct.rightDerived i ⟶
      (relocalization τ.toGrothendieck f).direct.rightDerived i ⋙
        (sliceComparison τ τ' hτ Y).direct :=
  comparisonBottom τ τ' hτ f i ≫ comparisonLeft τ τ' hτ f i

/-- The canonical truncated comparison is invertible, as is its relative Leray edge.
Source: Stacks, Tag 0EZA (blueprint: lem-trf-comparison-truncated-direct-images).

Proof, following the node's nine steps:
1. Sheafification fixes fine sheaves. By (3), the comparison direct image of a member of
A_X lies in A'_X. The inverse image is exact abelian sheafification.
2. Localization gives the square used in relocalizationComparisonIso. Exact left adjoints
make all direct images preserve injectives, giving derivedRelocalizationComparisonIso.
3. The spectral sequence for (epsilon_X, f') has zero rows 1 through r by V_r. On each
total degree i ≤ r, its bottom edge is therefore invertible. This is H^i(a_H).
4. The spectral sequence for (f, epsilon_Y) gives comparisonLeft. In degree zero it is
invertible since only its (0,0) term contributes; this also handles r = 0.
5. Induct on m ≤ r. Comparisons below m and (4) put R^q f_* H in A_Y for q < m.
Applying V_r kills E_2^{p,q} for 1 ≤ p ≤ r and q < m.
6. On the degree-m diagonal only (0,m) survives. Only the outgoing differential on page
m+1 can remain; if m < r its target is zero and the edge is invertible.
7. At m = r the remaining target is R^{r+1} epsilon_{Y,*} R^0 f_* H, giving the exact
sequence 0 → R^r f'_* epsilon_{X,*} H → epsilon_{Y,*} R^r f_* H → that target.
8. Apply exact fine sheafification. An injective-resolution calculation shows the last
term becomes zero: sheafification after inclusion is identity and positive resolution
cohomology vanishes. Both preceding terms already are fine sheaves by (3),(4); hence
the original comparison is invertible.
9. The maps are precisely the bottom edge, canonical derived square and left edge,
so their composite is the specified comparison. The map b_H is defined by the derived
adjunction hom equivalence, with its canonical unit and counit. -/
theorem comparisonTruncatedDirectImages
    {C : Type u} [SmallCategory C]
    (τ τ' : Precoverage C)
    (hτsite : τ.IsSiteForCoverings) (hτ'site : τ'.IsSiteForCoverings)
    (hτ : τ' ≤ τ)
    [∀ Z : C, HasDerivedCategory.{d} (Sheaf (τ.toGrothendieck.over Z) AddCommGrpCat.{u})]
    [∀ Z : C, HasDerivedCategory.{d} (Sheaf (τ'.toGrothendieck.over Z) AddCommGrpCat.{u})]
    (P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop)
    (A' : ∀ X : C, Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u} → Prop)
    (hzero : ∀ X : C, A' X 0)
    (hiso : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      Nonempty (H ≅ K) → A' X H → A' X K)
    (hkernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (kernel f))
    (hcokernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (cokernel f))
    (hextension : ∀ (X : C)
      (S : ShortComplex (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})),
      S.ShortExact → A' X S.X₁ → A' X S.X₃ → A' X S.X₂)
    (hbaseChange : ∀ (X Y Y' : C) (f : X ⟶ Y), P f → ∀ g : Y' ⟶ Y,
      ∃ (T : C) (p : T ⟶ X) (q : T ⟶ Y'), IsPullback p q f g ∧ P q)
    (hrelocalization : ∀ (X Y : C) (f : X ⟶ Y)
      (H : Sheaf (τ'.toGrothendieck.over Y) AddCommGrpCat.{u}),
      A' Y H → A' X ((relocalization τ'.toGrothendieck f).inverse.obj H))
    (htauSheaf : ∀ (X : C) (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      A' X H → Presheaf.IsSheaf (τ.toGrothendieck.over X) H.obj)
    (hderivedImage : ∀ (X Y : C) (f : X ⟶ Y), P f →
      ∀ (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}), A' X H →
        ∀ i : ℕ, A' Y (((relocalization τ'.toGrothendieck f).direct.rightDerived i).obj H))
    (r : ℕ)
    (hr : ∀ (X : C) (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u}),
      (∃ H' : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u},
        A' X H' ∧ Nonempty (H ≅ (sliceComparison τ τ' hτ X).inverse.obj H')) →
      ∀ i : ℕ, 1 ≤ i → i ≤ r →
        IsZero (((sliceComparison τ τ' hτ X).direct.rightDerived i).obj H))
    (X Y : C) (f : X ⟶ Y) (hf : P f)
    (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u})
    (hH : ∃ H' : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u},
      A' X H' ∧ Nonempty (H ≅ (sliceComparison τ τ' hτ X).inverse.obj H'))
    (i : ℕ) (hi : i ≤ r) :
    IsIso ((truncatedDirectImageComparison τ τ' hτ f i).app H) ∧
      IsIso ((comparisonLeft τ τ' hτ f i).app H) := by
  sorry

end Derived

end CategoryTheory.RefinedTopologyComparison
