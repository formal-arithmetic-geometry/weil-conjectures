/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CyclicDerivedHomData
public import WeilConjectures.CategoryTheory.FixedPairCreatedAbelianStructure
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.AlgebraicGeometry.CohomologyInWeakSerreSubcategory
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Derived realization of fixed pairs

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-def-sf-weil-complexes/_section.md, Complement, derived-to-strict comparison,
equivalence on hearts, and Jordan extension warning.
(blueprint: lem-pur-derived-fixed-pair-realization)

## Main definitions and statements

The source and target properties specify bounded cohomology in the given weak Serre class.
`derivedFixedPairRealization` states the canonical realization, its compatibility with
representatives and shifts, its equivalence on hearts, and its failure of faithfulness
in the presence of an underlying split but equivariantly nonsplit extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : A ⥤ A) [P.Additive] [P.IsEquivalence]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{wB} (IsoAlgebra P)]

/-- Bounded derived objects with cohomology in S.
Source: blueprint latest, sk-def-sf-weil-complexes, Complement, bounded underlying objects.
(blueprint: lem-pur-derived-fixed-pair-realization) -/
def fixedPairRealizationTarget (S : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=
  DerivedCategory.homologyProperty S ⊓ DerivedCategory.TStructure.t.bounded

/-- Bounded native derived fixed pairs whose underlying cohomology belongs to S.
Source: blueprint latest, sk-def-sf-weil-complexes, Complement, native derived source.
(blueprint: lem-pur-derived-fixed-pair-realization) -/
def fixedPairRealizationSource (S : ObjectProperty A) :
    ObjectProperty (DerivedCategory (IsoAlgebra P)) :=
  DerivedCategory.homologyProperty (S.inverseImage (forget P)) ⊓
    DerivedCategory.TStructure.t.bounded

/-- Restrict the exact derived action to bounded objects with cohomology in S.
Source: blueprint latest, sk-def-sf-weil-complexes, Complement, strict pairs.
(blueprint: lem-pur-derived-fixed-pair-realization) -/
abbrev fixedPairRealizationAction (S : ObjectProperty A)
    (hP : ∀ K, fixedPairRealizationTarget S K →
      fixedPairRealizationTarget S (P.mapDerivedCategory.obj K)) :
    (fixedPairRealizationTarget S).FullSubcategory ⥤
      (fixedPairRealizationTarget S).FullSubcategory :=
  (fixedPairRealizationTarget S).lift
    ((fixedPairRealizationTarget S).ι ⋙ P.mapDerivedCategory) (fun K ↦ hP K.obj K.property)

/-- Restrict derived forgetting to the specified bounded full subcategories.
Source: blueprint latest, sk-def-sf-weil-complexes, Complement, underlying derived functor.
(blueprint: lem-pur-derived-fixed-pair-realization) -/
def fixedPairRealizationForget (S : ObjectProperty A)
    (hU : ∀ K, fixedPairRealizationSource P S K →
      fixedPairRealizationTarget S ((forget P).mapDerivedCategory.obj K)) :
    (fixedPairRealizationSource P S).FullSubcategory ⥤
      (fixedPairRealizationTarget S).FullSubcategory :=
  (fixedPairRealizationTarget S).lift
    ((fixedPairRealizationSource P S).ι ⋙ (forget P).mapDerivedCategory)
      (fun K ↦ hU K.obj K.property)

/-- The heart of the restricted native standard t-structure.
Source: blueprint latest, sk-def-sf-weil-complexes, Complement, equivalence on hearts.
(blueprint: lem-pur-derived-fixed-pair-realization) -/
def fixedPairRealizationSourceHeart (S : ObjectProperty A) :
    ObjectProperty (fixedPairRealizationSource P S).FullSubcategory :=
  DerivedCategory.TStructure.t.heart.inverseImage (fixedPairRealizationSource P S).ι

/-- Strict pairs whose carrier lies in the heart of the restricted standard t-structure.
Source: blueprint latest, sk-def-sf-weil-complexes, Complement, equivalence on hearts.
(blueprint: lem-pur-derived-fixed-pair-realization) -/
def fixedPairRealizationTargetHeart (S : ObjectProperty A)
    (hP : ∀ K, fixedPairRealizationTarget S K →
      fixedPairRealizationTarget S (P.mapDerivedCategory.obj K)) :
    ObjectProperty (IsoAlgebra (fixedPairRealizationAction P S hP)) :=
  DerivedCategory.TStructure.t.heart.inverseImage
    (forget (fixedPairRealizationAction P S hP) ⋙ (fixedPairRealizationTarget S).ι)

/-- The canonical derived-to-strict realization and its heart and extension properties.

Source: blueprint latest, sk-def-sf-weil-complexes, Complement, and the agent-formulated
categorical prerequisite lem-pur-derived-fixed-pair-realization. Stacks Tags 0754, 06UQ,
08J5, 015F, 04VG, 06XS, 0152 and 0149.
(blueprint: lem-pur-derived-fixed-pair-realization)

Proof plan:
1. Grothendieck small limits and fixedPairCreatedAbelianStructure give the abelian fixed-pair
category and exact forgetting. The underlying weak Serre class is closed under zero, kernels,
cokernels and extensions. Apply cohomology_in_weak_serre_subcategory to both categories.
2. Good truncations preserve bounded cohomology in S. The exact derived functor factorization
and its cohomology comparison restrict D(P) and D(U), preserving the standard halves.
3. Localize the natural termwise structure isomorphism P U ≅ U. The localization universal
property gives cyclicDerivedStructure, its representative formula, and naturality for every
arrow, including inverses of quasi-isomorphisms.
4. Naturality defines the realization with underlying map D(U)(a). Shift compatibility reduces
on complexes to the same degreewise structure maps; additivity commutes with the shift sign.
Localization uniqueness descends this equation and the usual identity and iterated-shift laws.
5. Fully faithful degree-zero single embeddings and the concentrated-single lemma identify the
hearts with S and its native fixed pairs. Exact-functor single comparisons identify the action.
6. Fullness lifts each underlying heart arrow; faithfulness reflects its structure equation,
so the realization restricted to hearts is fully faithful.
7. For a strict pair in the heart, conjugate its structure to H⁰[0], then lift the structure and
its inverse by full faithfulness. This proves essential surjectivity of the heart restriction.
8. A short exact sequence gives its canonical single triangle. If its connecting map vanished,
Hom exactness on the rotated triangle would supply a section, lifted by full faithfulness of
singles to a splitting of the original sequence, a contradiction.
9. Exact forgetting carries this connecting map to the underlying connecting map. An underlying
section and the vanishing consecutive composite force that map to vanish. Carrier faithfulness
of strict pairs gives R(δ)=0; since δ≠0, R is not faithful.
-/
theorem derivedFixedPairRealization (S : ObjectProperty A)
    [IsGrothendieckAbelian.{v} A] [S.ContainsZero] [S.IsClosedUnderIsomorphisms]
    [S.IsClosedUnderKernels] [S.IsClosedUnderCokernels] [S.IsClosedUnderExtensions]
    (hPS : ∀ M : A, S M → S (P.obj M))
    (hPinvS : ∀ M : A, S M → S (P.inv.obj M)) :
    ∃ (hP : ∀ K, fixedPairRealizationTarget S K →
        fixedPairRealizationTarget S (P.mapDerivedCategory.obj K))
      (hU : ∀ K, fixedPairRealizationSource P S K →
        fixedPairRealizationTarget S ((forget P).mapDerivedCategory.obj K)),
      (fixedPairRealizationTarget S).IsTriangulated ∧
      (fixedPairRealizationSource P S).IsTriangulated ∧
      (∀ (K : DerivedCategory A), fixedPairRealizationTarget S K → ∀ n : ℤ,
        fixedPairRealizationTarget S ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        fixedPairRealizationTarget S ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
      (∀ (K : DerivedCategory (IsoAlgebra P)), fixedPairRealizationSource P S K → ∀ n : ℤ,
        fixedPairRealizationSource P S ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        fixedPairRealizationSource P S ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
      (∀ K : CochainComplex (IsoAlgebra P) ℤ,
        (cyclicDerivedStructure P).hom.app (DerivedCategory.Q.obj K) ≫
            (forget P).mapDerivedCategoryFactors.hom.app K =
          P.mapDerivedCategory.map ((forget P).mapDerivedCategoryFactors.hom.app K) ≫
            P.mapDerivedCategoryFactors.hom.app
              (((forget P).mapHomologicalComplex (.up ℤ)).obj K) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (strNatIso P).hom (.up ℤ)).app K)) ∧
      (∀ (K : DerivedCategory (IsoAlgebra P)) (n : ℤ),
        (cyclicDerivedStructure P).hom.app (K⟦n⟧) ≫
            ((forget P).mapDerivedCategory.commShiftIso n).hom.app K =
          P.mapDerivedCategory.map (((forget P).mapDerivedCategory.commShiftIso n).hom.app K) ≫
            (P.mapDerivedCategory.commShiftIso n).hom.app ((forget P).mapDerivedCategory.obj K) ≫
            ((cyclicDerivedStructure P).hom.app K)⟦n⟧') ∧
      ∃ R : (fixedPairRealizationSource P S).FullSubcategory ⥤
          IsoAlgebra (fixedPairRealizationAction P S hP),
        R ⋙ forget (fixedPairRealizationAction P S hP) = fixedPairRealizationForget P S hU ∧
        (∀ K : (fixedPairRealizationSource P S).FullSubcategory,
          HEq ((R.obj K).str.hom.hom) ((cyclicDerivedStructure P).hom.app K.obj)) ∧
        (∃ hR : ∀ K : (fixedPairRealizationSourceHeart P S).FullSubcategory,
            fixedPairRealizationTargetHeart P S hP
              (R.obj (((fixedPairRealizationSourceHeart P S).ι).obj K)),
          ((fixedPairRealizationTargetHeart P S hP).lift
            ((fixedPairRealizationSourceHeart P S).ι ⋙ R) hR).IsEquivalence) ∧
        (∀ (E : ShortComplex (IsoAlgebra P)) (hE : E.ShortExact),
          S E.X₁.carrier → S E.X₂.carrier → S E.X₃.carrier →
          ¬ Nonempty E.Splitting → Nonempty (E.map (forget P)).Splitting →
          hE.singleδ ≠ 0 ∧ (forget P).mapDerivedCategory.map hE.singleδ = 0 ∧
          ¬ R.Faithful ∧
          ∃ (X Y : (fixedPairRealizationSource P S).FullSubcategory)
            (eX : X.obj ≅ (DerivedCategory.singleFunctor (IsoAlgebra P) 0).obj E.X₃)
            (eY : Y.obj ≅ ((DerivedCategory.singleFunctor (IsoAlgebra P) 0).obj E.X₁)⟦1⟧),
            R.map (ObjectProperty.homMk (eX.hom ≫ hE.singleδ ≫ eY.inv)) = 0) := by
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
