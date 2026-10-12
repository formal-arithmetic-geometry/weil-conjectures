/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-! # Shift compatibility of the derived direct-image transition

Source: Stacks Project, Tag 09Z1, derived-adjunction coherence elaboration.
(blueprint: lem-sbc-abelian-derived-transition-shift).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory.Adjunction

/-- Transport a right-adjoint object through a comparison of left adjoints, and
then apply a coefficient morphism, using the two actual adjunctions. -/
noncomputable def transitionThrough
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ E} {R' : E ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (P : D ⥤ E) (θ : L' ⟶ L ⋙ P)
    (K : D) (K' : E) (t : P.obj K ⟶ K') : R.obj K ⟶ R'.obj K' :=
  adj'.unit.app (R.obj K) ≫
    R'.map (θ.app (R.obj K) ≫ P.map (adj.counit.app K) ≫ t)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Etale

/-- The derived transition before taking cohomology, for arbitrary complexes and a
coefficient morphism. This is an actual composite of units, comparison, and counit. -/
noncomputable def abelianDerivedDirectImageTransition {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (t : D+((a)^*[AddCommGrpCat.{v + 1}]).obj K ⟶ K') :
    R+((h)_*[AddCommGrpCat.{v + 1}]).obj K ⟶
      R+((h')_*[AddCommGrpCat.{v + 1}]).obj K' :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).derivedPlus.transitionThrough
    (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h').derivedPlus
    D+((a)^*[AddCommGrpCat.{v + 1}])
    (eqToIso (congrArg
      (fun f : Y' ⟶ S => ((f)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlus)
      w.symm) ≪≫ upperStarPlusComp AddCommGrpCat.{v + 1} a h).hom K K' t

/-- The derived transition commutes with integer shifts. Source: Stacks Project,
Tag 09Z1, compatibility of comparison morphisms; derived-adjunction coherence.
(blueprint: lem-sbc-abelian-derived-transition-shift).

Proof: Transport along w to reduce to h' = a ≫ h. The derived adjunction unit
commutes with shifts, as does its counit, by the existing theorem
`derivedPlus_upperStarLowerStar_commShift` for h and h'. These equalities descend
from the termwise adjunction on complexes through the localization factorization. The
composition comparison of exact pullbacks commutes with shifts because it is
induced by the termwise comparison, which commutes with shifts in every degree.
Expand the transition, apply these three identities, and use naturality of the
shift comparisons to move the coefficient morphism t through. The intermediate
shift comparisons cancel with their inverses. The two surviving comparisons are
those of Rh_* and Rh'_* displayed below. This works for arbitrary bounded below
complexes, including zero complexes, and every integer shift. -/
theorem abelianDerivedDirectImageTransition_shift {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (t : D+((a)^*[AddCommGrpCat.{v + 1}]).obj K ⟶ K') (n : ℤ) :
    abelianDerivedDirectImageTransition a h h' w (K⟦n⟧) (K'⟦n⟧)
        ((D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso n).hom.app K ≫
          (shiftFunctor _ n).map t) ≫
        (R+((h')_*[AddCommGrpCat.{v + 1}]).commShiftIso n).hom.app K' =
      (R+((h)_*[AddCommGrpCat.{v + 1}]).commShiftIso n).hom.app K ≫
        (shiftFunctor _ n).map (abelianDerivedDirectImageTransition a h h' w K K' t)
    := by sorry

end AlgebraicGeometry.Etale
