/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
public import WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologySourceColimit
import WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionFormulas

/-! # Presenting the strict-local mate as projection restriction

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Present the source of the strict-local mate as neighbourhood hypercohomology,
and identify its germ components with projection pullbacks to the limit.
This supplies the input to derived continuity, without applying continuity and without
asserting that either the target cocone is a colimit or the mate is invertible. -/
theorem nonempty_strictLocalBaseChange_continuityPresentation
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (GlobalCohomologyContinuityPresentation X K n
      ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictLocalizationToBase s)).toCommSq).hom))
                |>.app K)))) := by
  classical
  obtain ⟨Q⟩ := nonempty_strictLocalNeighbourhoodGeometry f s
  obtain ⟨E⟩ := nonempty_strictLocalMateProjectionData f s K n Q
  let := (Scheme.strictHenselizationAffineProperties s).2.1
  obtain ⟨hsource⟩ := isColimit_strictLocalCohomologySourceLegs s
    ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
  let : ∀ i, CompactSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.compact
  let : ∀ i, QuasiSeparatedSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.quasiSeparated
  let : ∀ {i j} (a : i ⟶ j), IsAffineHom ((strictLocalNeighbourhoodDiagram f s).map a) := Q.affine
  refine ⟨{
    I := SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)
    D := strictLocalNeighbourhoodDiagram f s
    c := Cone.mk _ Q.legs
    isLimit := Q.isLimit
    t := strictLocalNeighbourhoodProjection f s
    p := pullback.fst f (Scheme.strictLocalizationToBase s)
    «over» := Q.over
    F := strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    e := E.e
    transition := E.transition
    sourceLegs := strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    sourceIsColimit := hsource
    limitIso := strictLocalBaseChangeTargetIso f s K n
    restriction := fun i ↦ E.restriction i }⟩

end AlgebraicGeometry.Etale
