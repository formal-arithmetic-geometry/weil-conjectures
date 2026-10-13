/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Represented evaluation on homotopy classes

Source: Stacks Project, Tags 03Q8, 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- Underived restricted sections, applied termwise below.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso). -/
noncomputable abbrev underivedSections {Y : Scheme.{v}} (W : Y.Etale) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1} ⥤ AddCommGrpCat.{v + 1} :=
  upperStar AddCommGrpCat.{v + 1} W.hom ⋙
    Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}

/-- Zeroth homology of the sections complex of a single sheaf.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso). -/
noncomputable def underivedSingleIso {Y : Scheme.{v}} (W : Y.Etale)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (((underivedSections W).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj A)).homology 0 ≅
        (underivedSections W).obj A :=
  (HomologicalComplex.homologyFunctor _ _ 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (underivedSections W) (.up ℤ) 0).app A) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 _

/-- Evaluate a chain map at the represented identity and then pass to homology.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso). -/
noncomputable def chainEvaluation {S Y : Scheme.{v}} (h : Y ⟶ S) (U : S.Etale)
    (I : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (f : (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)) ⟶ I) :
    (((underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).mapHomologicalComplex
       (.up ℤ)).obj I).homology 0 :=
  HomologicalComplex.homologyMap
      (((underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).mapHomologicalComplex
         (.up ℤ)).map f) 0
    ((underivedSingleIso ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))).inv (generator h U))

/-- The free represented sheaf identifies homotopy classes with section cohomology.
Source: Stacks Project, Tag 03Q8; Cohomology on Sites, Tags 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-homotopy-sections-iso).

Proof: the inverse-image/direct-image adjunction, the sheafification adjunction,
free-abelian adjunction and Yoneda identify maps from the pulled-back free represented
sheaf to each term of I with its sections over U times Y. The map is evaluation at
`generator h U`: this follows from the unit formula for the first adjunction and the
identity formula for Yoneda. These additive equivalences commute with every differential.
Using the from-single cochain equivalence gives a chain isomorphism from the Hom complex
of the degree-zero single sheaf into I to the termwise restricted-sections complex.
Zeroth Hom-complex cohomology is homotopy classes of maps. Apply zeroth homology to the
chain isomorphism. On a chain map this is exactly `chainEvaluation`, since the
single-complex homology isomorphism sends the identity generator to its class.
The argument applies to arbitrary complexes, including the zero complex, and to the
empty pullback, where both groups are zero. No injective resolution is used here. -/
theorem exists_rawRestrictedHomotopySectionsIso {S Y : Scheme.{v}}
    (h : Y ⟶ S) (U : S.Etale)
    (I : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
    ∃ e : AddCommGrpCat.of
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))) ⟶
          (HomotopyCategory.quotient _ (.up ℤ)).obj I) ≅
        (((underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)).mapHomologicalComplex
           (.up ℤ)).obj I).homology 0,
      ∀ f, e.hom ((HomotopyCategory.quotient _ (.up ℤ)).map f) =
        chainEvaluation h U I f := by sorry

end AlgebraicGeometry.Etale.RawRestrictedComparison
