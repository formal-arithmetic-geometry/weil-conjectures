/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison
import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Transport of restricted section pullback through the shift comparison

Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-restricted-derived-sections-shift-transport).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- Shifted restricted section pullback is the conjugate of its unshifted derived map.
Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-restricted-derived-sections-shift-transport).

Proof: Write T and T' for restriction followed by derived global sections, L for
D+(a^*), and tau for the derived pullback followed by the restriction-composition
comparison. The inverse-image adjunction on complexes is degreewise, so its unit
commutes with shifts. Localize that equality. The Leray comparison commutes with
shifts because it is characterized by the composite right-derived unit, whose
factors commute with shifts. The comparison q^*r^* = r'^*a^* is induced from exact
functors on complexes and also commutes with shifts. Whiskering and composing
these equalities proves shift compatibility of tau for the canonical composite
shift structures on T and L followed by T'. Apply this identity at F[0].
Naturality of the target shift comparison moves the arbitrary shifted morphism f
past that comparison. Naturality of the homology shift isomorphism then identifies
H^0 of the shifted composite with H^p of tau at F[0] followed by T'(f).
Expand both shiftIso maps into their functor shift, homology shift and single
comparisons. Insert the inverse of the source single comparison immediately
before the unshifted map; its product with that single comparison is the identity.
Associativity and functoriality give the displayed conjugation formula. This
argument does not compute the unshifted map on any coefficient morphism and
works for any f, for p=0, and for an empty restricted scheme. -/
theorem restrictedDerivedSections_shiftTransport {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (f : D+(upperStar AddCommGrpCat.{v + 1} a).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ⟶
        (DerivedCategory.Plus.singleFunctor _ 0).obj F') (U : S.Etale) :
    let T' := sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
    let τ := Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft DerivedCategory.Plus.ι
          (derivedRestrictionIso a h h' w U).hom)
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h'))
    let e := Evaluation.singleIso
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h))
      (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}) F
    let e' := Evaluation.singleIso
      (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h'))
      (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}) F'
    (restrictedSectionPullback a h h' w U).app (K⟦(p : ℤ)⟧) ≫
      (T' ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        ((D+(upperStar AddCommGrpCat.{v + 1} a).commShiftIso (p : ℤ)).hom.app K ≫
          (shiftFunctor _ (p : ℤ)).map f) ≫ (shiftIso h' p F' U).hom =
      (shiftIso h p F U).hom ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} (p : ℤ)).map
          (e.inv ≫ τ.app K ≫ T'.map f ≫ e'.hom) := by sorry

end AlgebraicGeometry.Etale.RawRestrictedComparison
