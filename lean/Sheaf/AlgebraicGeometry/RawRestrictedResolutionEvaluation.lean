/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RawRestrictedHomotopySectionsIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Compatibility of derived evaluation with a resolution

Source: Stacks Project, Cohomology on Sites, Tags 072W, 0BKV and 0D6F.
(blueprint: lem-sbc-raw-restricted-resolution-evaluation).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- The canonical computation of restricted derived sections on a K-injective restriction.
Source: Stacks Project, Tags 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-resolution-evaluation). -/
noncomputable def resolutionSectionsIso {Y : Scheme.{v}} (W : Y.Etale)
    (I : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    [CochainComplex.IsKInjective
      (((upperStar AddCommGrpCat.{v + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj
      I.obj)] :
    (sectionsFunctor W ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).obj
        (DerivedCategory.Plus.Q.obj I) ≅
      (((underivedSections W).mapHomologicalComplex (.up ℤ)).obj I.obj).homology 0 :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).mapIso
      ((Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.mapIso
          ((upperStar AddCommGrpCat.{v + 1} W.hom).mapDerivedCategoryFactors.app I.obj) ≪≫
        (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorObjQIso
          (((upperStar AddCommGrpCat.{v + 1} W.hom).mapHomologicalComplex (.up ℤ)).obj
            I.obj)) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} 0).app _

/-- On a chain map, derived evaluation agrees with termwise evaluation in the resolution.
Source: Stacks Project, Cohomology on Sites, Tags 072W, 0BKV and 0D6F.
(blueprint: lem-sbc-raw-restricted-resolution-evaluation).

Proof: let L be etale restriction and R be sections. The comparison defining
`resolutionSectionsIso` first uses the exact-functor localization comparison for L,
then the inverse right-derived unit for R on the K-injective complex L(I), and finally
homology's localization comparison. Naturality of all three comparisons identifies
its composite with the image under H^0(R L) of the given chain map. For the degree-zero
single source, the degree-zero derived-to-underived isomorphism `zeroIso` is the same
comparison followed by the single-complex homology identification. Thus the element
`zeroIso.inv (generator h U)` maps to the generator's single-complex class. Applying
the chain map gives exactly `chainEvaluation`. This equality is independent of any
chosen homotopy class isomorphism and does not assert its bijectivity. It also holds
for a zero chain map and for a zero or empty restricted complex. -/
theorem rawRestricted_resolution_evaluation {S Y : Scheme.{v}}
    (h : Y ⟶ S) (U : S.Etale)
    (I : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    [CochainComplex.IsKInjective
      (((upperStar AddCommGrpCat.{v + 1}
      ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U).hom).mapHomologicalComplex
         (.up ℤ)).obj I.obj)]
    (f : (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)) ⟶ I.obj) :
    let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
    let A := (upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U)
    let T := sectionsFunctor W ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
    let x := (zeroIso W A).inv (generator h U)
    (resolutionSectionsIso W I).hom
        (T.map (DerivedCategory.Plus.ι.preimage
          (DerivedCategory.Q.map f) :
            (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
              DerivedCategory.Plus.Q.obj I) x) =
      chainEvaluation h U I.obj f := by sorry

end AlgebraicGeometry.Etale.RawRestrictedComparison
