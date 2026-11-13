/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
import WeilConjectures.AlgebraicGeometry.StrictLocalMateContinuityPresentation
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.FibreProductNeighbourhoodLimit
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictLocalGermRestrictionIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # The strict-local base-change mate on global cohomology

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0GIT](https://stacks.math.columbia.edu/tag/0GIT)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The homology of the derived base-change mate is invertible on strict-local sections.
This only asserts invertibility after global sections; it does not assert that the mate
is an isomorphism of sheaves on the strict-local base.
-/
theorem isIso_strictHenselization_baseChange_globalHomology
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso
      ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictLocalizationToBase s)).toCommSq).hom))
                |>.app K))) := by
  let m :=
    ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictLocalizationToBase s)).toCommSq).hom))
                |>.app K)))
  change IsIso m
  obtain ⟨P⟩ := nonempty_strictLocalBaseChange_continuityPresentation f s K n
  let : SmallCategory P.I := P.category
  let : IsCofiltered P.I := P.cofiltered
  let : ∀ i, CompactSpace (P.D.obj i) := P.compact
  let : ∀ i, QuasiSeparatedSpace (P.D.obj i) := P.quasiSeparated
  let : ∀ {i j : P.I} (a : i ⟶ j), IsAffineHom (P.D.map a) := P.affine
  -- The mate extends the source cocone by its restriction equations.
  let a : Cocone P.F := Cocone.mk _ P.sourceLegs
  let b := a.extend m
  obtain ⟨hb⟩ := derivedEtaleCohomology_limit X P.D P.c P.isLimit P.t P.p P.over
    K n P.F P.e P.transition b P.limitIso P.restriction
  -- Both cocones are colimiting; identify their universal comparison with the mate.
  have hdesc : P.sourceIsColimit.desc b = m := by
    apply P.sourceIsColimit.hom_ext
    intro i
    exact P.sourceIsColimit.fac b i
  have : IsIso (P.sourceIsColimit.desc b) :=
    (P.sourceIsColimit.nonempty_isColimit_iff_isIso_desc).mp ⟨hb⟩
  simpa only [hdesc] using this

end AlgebraicGeometry.Etale
