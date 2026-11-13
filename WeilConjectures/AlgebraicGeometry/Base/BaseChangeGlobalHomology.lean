/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.Curve.MateContinuityPresentation
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit

/-! # The strict-local base-change mate on global cohomology

This theorem retains `strictHenselizationScheme` and its structural map.
The adopted theorem with the unprefixed name uses `strictLocalization` instead.

Source: Stacks Project, Tags 03Q8, 03Q9 and 0GIT.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The homology of the derived base-change mate is invertible on strict-local sections.
This only asserts invertibility after global sections; it does not assert that the mate
is an isomorphism of sheaves on the strict-local base.
Source: Stacks Project, Tag 03Q9, the affine-neighbourhood continuity argument and the
injective-representative construction of the canonical map. -/
theorem smallModel_isIso_strictHenselization_baseChange_globalHomology
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    IsIso
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.app K))) := by
  let m :=
    ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.app K)))
  change IsIso m
  obtain ⟨P⟩ := smallModel_nonempty_strictLocalBaseChange_continuityPresentation f s K n
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
