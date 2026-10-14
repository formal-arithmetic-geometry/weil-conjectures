/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import Sheaf.Algebra.Homology.ModuleStalkFunctor

/-! # Open restriction compatibility of the tensor pullback unit

Source: Stacks Project, Tags 0096 and 0098.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry

/-- The pinned tensor restriction comparison preserves the pullback unit on stalks.

Proof: express the inverse comparison as the inverse of its four defining factors.
The open-pullback factor is the unique comparison of left adjoints; the identity
`Adjunction.unit_leftAdjointUniq_hom_app` says it identifies their units.
For each composition factor, `unit_conjugateEquiv_symm` identifies the composite
unit with the unit for the composite morphism, followed by the pushforward
composition comparison. The two composition comparisons cancel after transport
along `hj`. Hence the inverse pinned comparison sends the restricted unit for
`j` to the restriction of the unit for `k`. Apply the additive stalk functor,
then the pushforward-stalk map. On section germs this map sends the germ of a
unit section over W to its germ over the inverse image of W. The formulas
`germ_restrictStalkNatIso_hom_app` identify both open restriction factors with
the same ambient germ. Transport of the input point is exactly `hx` below.
Every stalk element is represented by a section germ, so equality on germs
proves the equality of additive maps. No flatness or cartesian hypothesis is
used. Empty opens have no z; zero sheaves and identity open immersions satisfy
the same unit identities.
Source: Stacks Project, Tags 0096 and 0098; Mathlib adjunction mate unit identities.
(blueprint: lem-pc-open-pinned-tensor-restriction-stalk-unit). -/
theorem openPinnedTensorRestriction_stalk_unit
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) (M : X.Modules) (z : U'.toScheme) :
    let N := (schemeOpenRestriction X U).obj M
    let L₀ := RingedSpace.moduleStalkFunctor U'.toScheme.toRingedSpace z
    let F₀ := forget₂ (ModuleCat.{u} (U'.toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let Lᵢ := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace (j z)
    let Fᵢ := forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk (j z))) AddCommGrpCat.{u}
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U') (L₀ ⋙ F₀) ≪≫
      Scheme.Modules.restrictStalkNatIso U'.ι z
    let γᵢ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (Lᵢ ⋙ Fᵢ) ≪≫
      Scheme.Modules.restrictStalkNatIso U.ι (j z)
    let hx := congrArg (fun t : U'.toScheme ⟶ X ↦ t z) hj
    γᵢ.hom.app M ≫ (M.presheaf.stalkCongr (.of_eq hx)).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k z.val)).map
          (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)) ≫
        ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
          AddCommGrpCat.{u} k.base z.val =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j z)).map
          (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app N)) ≫
        ((Scheme.Modules.tensorPullback j).obj N).presheaf.stalkPushforward
          AddCommGrpCat.{u} j.base z ≫
        F₀.map (L₀.map ((openPinnedTensorRestrictionIso k U U' j hj).inv.app M)) ≫
        γ.hom.app ((Scheme.Modules.tensorPullback k).obj M) := by
  sorry

end AlgebraicGeometry
