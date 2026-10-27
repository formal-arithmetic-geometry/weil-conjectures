/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RegularRoosKoszulData
public import Sheaf.CategoryTheory.RingedKoszulSmallModelCompletedTensor
public import Sheaf.CategoryTheory.RingedKoszulSystem

/-! # Principal localization tests on the small model

Source: Stacks Project, Tags 099B, 0A0E and 0941.
(blueprint: lem-sf-principal-strict-small-model-local-tests).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe c v r w w₀
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RegularRoosKoszul
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules.{c, v, r} R)]

variable [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{max c v r}]
  [∀ W : C, HasSheafify (J.over W) CommRingCat.{max c v r}]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ W : C, HasDerivedCategory.{w}
  (SheafOfModules.{max c v r} ((sheafCompose (J.over W)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over W)))]

variable
  [HasSheafify ((equivSmallModel.{max c v r} C).inverse.inducedTopology J)
    AddCommGrpCat.{max c v r}]

variable [∀ U : SmallModel.{max c v r} C,
  HasSheafify (((equivSmallModel.{max c v r} C).inverse.inducedTopology J).over U)
    AddCommGrpCat.{max c v r}]

variable
  [HasDerivedCategory.{w₀} ((SheafOfModules.{max c v r}
    ((sheafCompose ((equivSmallModel.{max c v r} C).inverse.inducedTopology J)
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        (KoszulSmallModel.ring.{c, v, max c v r} R))))]
  [∀ U : SmallModel.{max c v r} C, HasDerivedCategory.{w₀}
    (SheafOfModules.{max c v r}
      ((sheafCompose (((equivSmallModel.{max c v r} C).inverse.inducedTopology J).over U)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
          ((KoszulSmallModel.ring.{c, v, max c v r} R).over U)))]

/-- The principal local test is unchanged by passage to the canonical small model.
The ideal is represented by multiplication from the unit module. This is solely a
comparison of local predicates, for an arbitrary derived object.

Source: Stacks Project, Modules on Sites, Tags 03DA and 03DG; algebraization.tex,
Tags 0999 and 099B.
(blueprint: lem-sf-principal-strict-small-model-local-tests).

Proof: restriction along the site equivalence induces an exact equivalence of module
sheaves on every slice. The slice restriction square commutes. Sectionwise localization
commutes with this equivalence by the localization universal property and the
sheafification adjunction. The Hom-complex comparison, followed by K-injective
replacement, identifies the derived internal Hom localization tests. Exact equivalences
preserve K-injectives and reflect zero objects, so their vanishing conditions agree.
A slice section is determined by its value at the terminal object. Under this
identification, being the image of multiplication by t is the identical equation on
sections on both sites. Every native object is isomorphic to the image of a small-model
object, so these comparisons prove both implications for all slices. For the
small-site interface, the universe-generalized and original Hom localizations agree
by the uniqueness of their localization lifts, and the two section localizations are
the same sheafifications. This also treats empty sites and zero or invertible t. -/
theorem principal_strict_small_model_local_tests
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections)
    (P : DerivedCategory.{w} (Modules.{c, v, r} R)) :
    locallyComplete.{c, v, r, w} R t P ↔
      IsLocallyDerivedRingedIdealComplete (KoszulSmallModel.ring.{c, v, max c v r} R)
        (SheafOfModules.unit ((sheafCompose _
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
            (KoszulSmallModel.ring.{c, v, max c v r} R)))
        (ringedKoszulScalar (KoszulSmallModel.ring.{c, v, max c v r} R)
          (KoszulSmallModel.globalSection.{c, v, max c v r} R ⟨t.val, t.property⟩))
        ((KoszulSmallModel.derivedEquiv.{c, v, max c v r, w, w₀} R).functor.obj P) := by sorry

end CategoryTheory.RegularRoosKoszul
