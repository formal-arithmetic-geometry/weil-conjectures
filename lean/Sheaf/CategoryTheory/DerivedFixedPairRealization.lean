module

public import Sheaf.CategoryTheory.FixedPairCreatedAbelianStructure
public import Sheaf.CategoryTheory.CyclicDerivedHomData
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Derived realization of fixed pairs

Source: blueprint latest, sec-smooth-purity/sk-def-sf-weil-complexes/_section.md,
Complement: comparison with strict pairs, equivalence on hearts and the Jordan extension warning.
The general categorical formulation is the prerequisite in
(blueprint: lem-pur-derived-fixed-pair-realization).

The auxiliary abbreviations only spell out the full subcategories and the restrictions of
the already defined ordinary derived functors. No realization object is chosen from existence.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : A ⥤ A) [P.Additive] [P.IsEquivalence]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{wB} (IsoAlgebra P)]
  (S : ObjectProperty A)

/-- The full subcategory C of bounded objects with all cohomology objects in S.
Source: blueprint latest, sk-def-sf-weil-complexes, comparison complement;
(blueprint: lem-pur-derived-fixed-pair-realization). -/
abbrev fixedPairRealizationTarget : ObjectProperty (DerivedCategory A) :=
  DerivedCategory.homologyProperty S ⊓ DerivedCategory.TStructure.t.bounded

/-- The full subcategory D of bounded objects with underlying cohomology objects in S.
Source: blueprint latest, sk-def-sf-weil-complexes, comparison complement;
(blueprint: lem-pur-derived-fixed-pair-realization). -/
abbrev fixedPairRealizationSource : ObjectProperty (DerivedCategory (IsoAlgebra P)) :=
  DerivedCategory.homologyProperty (S.inverseImage (forget P)) ⊓
    DerivedCategory.TStructure.t.bounded

/-- D(P) restricted to C, given its preservation proof.
Source: blueprint latest, sk-def-sf-weil-complexes, comparison complement;
(blueprint: lem-pur-derived-fixed-pair-realization). -/
abbrev fixedPairRealizationAction
    (hP : ∀ K, fixedPairRealizationTarget S K →
      fixedPairRealizationTarget S (P.mapDerivedCategory.obj K)) :
    (fixedPairRealizationTarget S).FullSubcategory ⥤
      (fixedPairRealizationTarget S).FullSubcategory :=
  (fixedPairRealizationTarget S).lift
    ((fixedPairRealizationTarget S).ι ⋙ P.mapDerivedCategory)
    (fun K ↦ hP K.obj K.property)

/-- D(U) restricted from D to C, given its preservation proof.
Source: blueprint latest, sk-def-sf-weil-complexes, comparison complement;
(blueprint: lem-pur-derived-fixed-pair-realization). -/
abbrev fixedPairRealizationForget
    (hU : ∀ K, fixedPairRealizationSource P S K →
      fixedPairRealizationTarget S ((forget P).mapDerivedCategory.obj K)) :
    (fixedPairRealizationSource P S).FullSubcategory ⥤
      (fixedPairRealizationTarget S).FullSubcategory :=
  (fixedPairRealizationTarget S).lift
    ((fixedPairRealizationSource P S).ι ⋙ (forget P).mapDerivedCategory)
    (fun K ↦ hU K.obj K.property)

/-- The heart of D, using the ambient standard heart (the restricted heart is its inverse image).
Source: blueprint latest, sk-def-sf-weil-complexes, equivalence-on-hearts complement;
(blueprint: lem-pur-derived-fixed-pair-realization). -/
abbrev fixedPairRealizationSourceHeart :
    ObjectProperty (fixedPairRealizationSource P S).FullSubcategory :=
  DerivedCategory.TStructure.t.heart.inverseImage (fixedPairRealizationSource P S).ι

/-- Strict pairs in C whose underlying object belongs to the standard heart of C.
Source: blueprint latest, sk-def-sf-weil-complexes, equivalence-on-hearts complement;
(blueprint: lem-pur-derived-fixed-pair-realization). -/
abbrev fixedPairRealizationTargetHeart
    (hP : ∀ K, fixedPairRealizationTarget S K →
      fixedPairRealizationTarget S (P.mapDerivedCategory.obj K)) :
    ObjectProperty (IsoAlgebra (fixedPairRealizationAction P S hP)) :=
  (DerivedCategory.TStructure.t.heart.inverseImage (fixedPairRealizationTarget S).ι).inverseImage
    (forget (fixedPairRealizationAction P S hP))

/-- Canonical realization, its representative and shift normalizations, its equivalence on
hearts, and its failure of faithfulness in the presence of a nonsplit underlying split extension.

Source: blueprint latest, sec-smooth-purity/sk-def-sf-weil-complexes/_section.md, Complement;
Stacks Tags 0754, 06UQ, 08J5, 015F, 04VG, 06XS, 0152 and 0149.
(blueprint: lem-pur-derived-fixed-pair-realization).

Proof plan, following all nine steps of the node:
1. Grothendieck small limits and colimits allow fixedPairCreatedAbelianStructure to apply.
The inverse image of S under exact forgetting contains zero and is closed under isomorphisms,
kernels, cokernels and extensions. CohomologyInWeakSerreSubcategory gives both triangulated
subcategories, including the bounded intersections. No equivalence with D(S) is used.
2. Good truncations retain the old cohomology on one side and zero on the other, so both
subcategories are truncation-stable. Orthogonality and shift inclusions are inherited, giving
the restricted standard t-structures, which are bounded. Exact functor cohomology comparisons
give preservation by D(P) and D(U); the inverse autoequivalence gives the inverse preservation.
3. The structure isomorphisms give the natural isomorphism P U ≅ U. Termwise application gives
an isomorphism of complexes. Localization lifts it uniquely to cyclicDerivedStructure P.
The two exact-functor factorization isomorphisms give the cochain formula stated below.
4. Put R(K)=(D(U)K,Theta_K), with R(a)=D(U)(a). Naturality gives exactly the intertwining
equation. Quasi-isomorphisms become invertible; their inverses also intertwine. The shift
equation reduces after precomposition with Q to the same degreewise structure maps, with
the differential signs commuting by additivity. Localization reflects the equation.
5. The fully faithful degree-zero single functors and the concentrated-single theorem identify
the two standard hearts with S and the fixed pairs carried by S. Exact-functor single
comparisons identify R on these objects with (UM[0],theta_M[0]).
6. A map between such strict pairs uniquely lifts to a map of their degree-zero carriers.
Faithfulness of the single embedding reflects its intertwining equation, giving full
faithfulness of the restriction of R to the heart.
7. For a strict pair in the heart, identify its carrier with H^0[0] and conjugate the structure
isomorphism. Fullness lifts it and its inverse to degree zero; faithfulness reflects the
inverse equations. This gives essential surjectivity, hence the stated heart equivalence.
8. The canonical single triangle of a nonsplit short exact sequence has nonzero connecting
map: if it vanished, representable exactness on the rotated triangle would give a section
of its second arrow, and single full faithfulness would split the original sequence.
9. Exact forgetting takes this connecting map to the underlying connecting map, up to
invertible single and shift comparisons. An underlying section makes that map zero by the
vanishing of consecutive composites in the triangle. Faithful forgetting of strict pairs
then gives R(delta)=0; delta and zero are distinct source morphisms with the same image.
-/
theorem derivedFixedPairRealization [IsGrothendieckAbelian.{v} A]
    [S.ContainsZero] [S.IsClosedUnderIsomorphisms]
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
          P.mapDerivedCategory.map
              (((forget P).mapDerivedCategory.commShiftIso n).hom.app K) ≫
            (P.mapDerivedCategory.commShiftIso n).hom.app
              ((forget P).mapDerivedCategory.obj K) ≫
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
            R.map (ObjectProperty.homMk (eX.hom ≫ hE.singleδ ≫ eY.inv)) =
              0) := by
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
