/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# The comparison pullback and direct images
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {U V : Scheme.{u}} (f : U ⟶ V)

/-- Base change along `f` commutes with the inclusion of the small étale site into the small
pro-étale site: both composites send an étale `V`-scheme `E` to `E ×_V U`. -/
noncomputable def toProEtCompOverPullbackIso :
    toProEt V ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ f ≅
      MorphismProperty.Over.pullback @Etale ⊤ f ⋙ toProEt U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext; simp; rfl)

/-- The composite of `ν` with base change along `f` is continuous. -/
instance isContinuous_toProEt_comp_overPullback :
    (toProEt V ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).IsContinuous
      V.smallEtaleTopology (ProEt.topology U) :=
  have := ProEt.isContinuous_overPullback f
  Functor.isContinuous_comp (toProEt V) (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
    V.smallEtaleTopology (ProEt.topology V) (ProEt.topology U)

/-- The composite of base change along `f` with `ν` is continuous. -/
instance isContinuous_overPullback_comp_toProEt :
    (MorphismProperty.Over.pullback @Etale ⊤ f ⋙ toProEt U).IsContinuous
    V.smallEtaleTopology (ProEt.topology U) :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous V.smallEtaleTopology
      U.smallEtaleTopology := Etale.isContinuous_overPullback f
  have := isContinuous_toProEt U
  Functor.isContinuous_comp (MorphismProperty.Over.pullback @Etale ⊤ f) (toProEt U)
    V.smallEtaleTopology U.smallEtaleTopology (ProEt.topology U)

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The restriction functors `ν_*` commute with the direct images along `f`. -/
noncomputable def lowerStarCompComparisonLowerStarIso :
    ProEtale.lowerStar A f ⋙ comparisonLowerStar A V ≅
      comparisonLowerStar A U ⋙ Etale.lowerStar A f :=
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous V.smallEtaleTopology
      U.smallEtaleTopology := Etale.isContinuous_overPullback f
  have := ProEt.isContinuous_overPullback f
  have := isContinuous_toProEt U
  have := isContinuous_overPullback_comp_toProEt f
  Functor.sheafPushforwardContinuousComp (toProEt V)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) A V.smallEtaleTopology
      (ProEt.topology V) (ProEt.topology U) ≪≫
    Functor.sheafPushforwardContinuousIso (toProEtCompOverPullbackIso f) A
      V.smallEtaleTopology (ProEt.topology U) ≪≫
    (Functor.sheafPushforwardContinuousComp (MorphismProperty.Over.pullback @Etale ⊤ f)
      (toProEt U) A V.smallEtaleTopology U.smallEtaleTopology (ProEt.topology U)).symm

/-- The base change morphism `ν_V^* f_* ⟶ f_* ν_U^*`, the mate of
`AlgebraicGeometry.ProEtale.lowerStarCompComparisonLowerStarIso` under the adjunctions
`ν^* ⊣ ν_*`. -/
noncomputable def lowerStarComparisonUpperStarBaseChange :
    Etale.lowerStar A f ⋙ comparisonUpperStar A V ⟶
      comparisonUpperStar A U ⋙ ProEtale.lowerStar A f :=
  (mateEquiv (comparisonAdjunction A U) (comparisonAdjunction A V)).symm
    (lowerStarCompComparisonLowerStarIso f A).inv

/-- The base change morphism `ν_V^* f_* ⟶ f_* ν_U^*` is an isomorphism for `f` quasi-compact
and quasi-separated. -/
theorem isIso_lowerStarComparisonUpperStarBaseChange [QuasiCompact f] [QuasiSeparated f] :
    IsIso (lowerStarComparisonUpperStarBaseChange f A) :=
  sorry

/-- For `f` quasi-compact and quasi-separated, the comparison pullback `ν_U^* I` of an injective
étale sheaf is acyclic for the pro-étale direct image `f_*`. -/
theorem rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective [QuasiCompact f]
    [QuasiSeparated f] (I : Sheaf U.smallEtaleTopology A) [Injective I] :
    (ProEtale.lowerStar A f).rightAcyclic ((comparisonUpperStar A U).obj I) :=
  sorry

end AlgebraicGeometry.ProEtale
