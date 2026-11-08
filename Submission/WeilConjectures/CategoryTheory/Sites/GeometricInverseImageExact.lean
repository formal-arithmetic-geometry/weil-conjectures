/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Submission.WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.EpiMono
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

set_option linter.privateModule false

/-!
# Exactness of geometric inverse image on abelian sheaves and modules

Source: Stacks Project, Modules on Sites, Tags 04JC, 03D2, 03DA and 03DB;
Sites, Proposition 00YV (2)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe w uC vC uD vD

open CategoryTheory.Limits

namespace CategoryTheory.GeometricMorphism

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

private noncomputable abbrev abSheafify
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{w} :=
  hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}

private noncomputable abbrev smallArrowLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] (U : Cᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
      AddCommGrpCat.{w} :=
  HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _

attribute [local instance] abSheafify smallArrowLimits

private noncomputable abbrev abLocallyBijective
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
    (A := AddCommGrpCat.{w})

attribute [local instance] abLocallyBijective

private theorem abForgetLimits
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) := by
  have : PreservesFiniteLimits
      (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ sheafToPresheaf J (Type w)) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type w))

attribute [local instance] abForgetLimits

open CategoryTheory.MonoidalCategory
open SheafOfModules.GeometricConstruction

-- Sectionwise reconstruction follows `SheafRingObjectReconstruction`, with the
-- sheaf condition checked on a small model to retain independent site universes.
noncomputable section RingReconstruction

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
end RingReconstruction

private def unliftSetSheafIso
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} :
    sheafCompose J uliftFunctor.{w, w} ≅ 𝟭 (Sheaf J (Type w)) :=
  NatIso.ofComponents (fun T ↦
    { hom := ⟨{ app := fun _ ↦ ↾ULift.down }⟩
      inv := ⟨{ app := fun _ ↦ ↾ULift.up }⟩ })
    (by intro T T' f; rfl)

-- The same conjugation by `ULift.down` is used in `LocalizationInverseImageCoherence`.
private noncomputable def inverseImageUniverses
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}
    (a : SheafOfModules.AlgebraicInverseImage L R S) :
    SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L R S := by
  let eJ := unliftSetSheafIso (J := J)
  let eK := unliftSetSheafIso (J := K)
  let rR := (sheafCompose J (forget CommRingCat.{w})).obj R
  let rS := (sheafCompose K (forget CommRingCat.{w})).obj S
  let mR := SheafOfModules.toSheaf.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
      sheafCompose J (forget AddCommGrpCat.{w})
  let mS := SheafOfModules.toSheaf.{w}
    ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S) ⋙
      sheafCompose K (forget AddCommGrpCat.{w})
  refine
    { ringUnderlying := L.mapIso (eJ.app rR) ≪≫ a.ringUnderlying ≪≫ (eK.app rS).symm
      modules := a.modules
      moduleUnderlying :=
        Functor.isoWhiskerLeft a.modules (Functor.isoWhiskerLeft mS eK) ≪≫
          a.moduleUnderlying ≪≫
            Functor.isoWhiskerRight (Functor.isoWhiskerLeft mR eJ.symm) L
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringAdd T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x y z h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringMul T (x ≫ eJ.hom.app rR) (y ≫ eJ.hom.app rR)
        (z ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringZero T (x ≫ eJ.hom.app rR) h W q
  · intro T x h W q
    simpa [eJ, eK, unliftSetSheafIso, Functor.map_comp] using
      a.ringOne T (x ≫ eJ.hom.app rR) h W q
  · intro M T x y z h W q
    have h' := a.moduleAdd M T (x ≫ eJ.hom.app (mR.obj M))
      (y ≫ eJ.hom.app (mR.obj M)) (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T x h W q
    have h' := a.moduleZero M T (x ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl
  · intro M T r x z h W q
    have h' := a.moduleSMul M T (r ≫ eJ.hom.app rR) (x ≫ eJ.hom.app (mR.obj M))
      (z ≫ eJ.hom.app (mR.obj M)) h W q
    simp only [Functor.map_comp] at h'
    convert h' using 1
    all_goals rfl

end CategoryTheory.GeometricMorphism
