/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedAbelianFilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! Ringed pro-etale localization: a geometric step of the open-closed argument. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Closed direct image with arbitrary inverse-image-ring coefficients commutes
with filtered colimits on a quasi-compact quasi-separated base.

Source: Stacks Project, Tags 0738 (4) and 098D
(blueprint: lem-weil-pbc-proetale-ringed-filtered-colimits).

Proof: Forget module sheaves on both sites to abelian sheaves. The underlying
abelian functor of the specified module pushforward is definitionally the composite
of this forgetful functor with abelian direct image. Abelian direct image preserves
the filtered colimits by the geometric closed-image comparison. The module forgetful
functors preserve these colimits by `moduleSheaves_colimits_forgetful`; hence the
composite of module pushforward and the target forgetful functor preserves them.
The latter forgetful functor reflects isomorphisms and preserves colimits, and so
reflects colimits. Reflection now gives preservation by module pushforward itself. -/
theorem proEtale_ringed_filtered_colimits {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩) := by
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
  let S := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)
  let F := proEtaleSheafDirectImage i AddCommGrpCat.{u + 1}
  let P := (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
  change PreservesColimitsOfShape I P
  have : PreservesColimitsOfShape I F := proEtale_closed_abelian_filteredColimits i I
  have : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u + 1} R) :=
    ((CategoryTheory.moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} R).2.2.2.2.2 I).2.1
  have : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u + 1} S) :=
    ((CategoryTheory.moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} S).2.2.2.2.2 I).2.1
  have : ReflectsColimitsOfShape I (SheafOfModules.toSheaf.{u + 1} R) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : PreservesColimitsOfShape I (P ⋙ SheafOfModules.toSheaf.{u + 1} R) := by
    change PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u + 1} S ⋙ F)
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves P
    (SheafOfModules.toSheaf.{u + 1} R)

end AlgebraicGeometry.Scheme
