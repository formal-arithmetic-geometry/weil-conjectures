/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.CategoryTheory.RingedPresentationData
public import Sheaf.CategoryTheory.SheafSubcategoryComparison

/-!
# Coherent module transport along a presenting nerve and its localized sites

Source: Stacks Project, Sites, Tags 00Y1, 04GZ, 03EH; Modules on Sites,
Tags 03CR, 04IE, 04J4 (blueprint: lem-sp-ringed-nerve-slice-transport).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The localized ringed/module part of a nerve presentation, with normalized comparisons.
The inputs fix the whole module transport, the element-site slices, and the slice nerves.
There is no binary-cover or finite-limit-closure construction in this data.
Source: Stacks 03CR, 04IE, 04J4
(blueprint: lem-sp-ringed-nerve-slice-transport). -/
structure RingedNerveSliceTransport
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology E}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R))
    (whole : RingedPresentationAt g) (F : E ⥤ Sheaf J (Type u))
    (sourceSlice : ∀ X : E, RingedSheafSliceAdjunctionData
      (localCoefficientRings R) (F.obj X))
    (slice : ∀ X : E, Over (F.obj X) ≌ Sheaf (K.over X) (Type u))
    (continuous : ∀ {X Y : E} (f : X ⟶ Y),
      Functor.IsContinuous (elementMap (F.map f))
        (elementTopology (F.obj X)) (elementTopology (F.obj Y))) where
  ringed : ∀ X : E, RingedToposMorphism (localCoefficientRings (S.over X))
    (localCoefficientRings (presentationElementRing R (F.obj X)))
  inverse : ∀ X : E, Nonempty ((ringed X).inverse ≅
    (sourceSlice X).fibreEquivalence.functor ⋙ (slice X).functor)
  ringIsIso : ∀ X : E, IsIso (ringed X).ringMap
  modules : ∀ X : E, RingedPresentationAt (ringed X)
  restriction : ∀ X : E,
    elementModulePullback.{u, u} (localCoefficientRings R) (F.obj X) ⋙
      (modules X).transport.modules.functor ≅
    whole.transport.modules.functor ⋙ SheafOfModules.overFunctor.{u}
      (localCoefficientRings S) X
  further : ∀ {X Y : E} (f : X ⟶ Y),
    elementModulePullbackOver.{u, u} (localCoefficientRings R) (F.map f)
      (continuous f) ⋙ (modules X).transport.modules.functor ≅
    (modules Y).transport.modules.functor ⋙ SheafOfModules.overMap.{u}
      (localCoefficientRings S) f
  restrictionComposition : ∀ {X Y : E} (f : X ⟶ Y) (M : PresentationModules R),
    HEq ((restriction X).hom.app M)
      ((further f).hom.app
          ((elementModulePullback.{u, u} (localCoefficientRings R) (F.obj Y)).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings S) f).map
          ((restriction Y).hom.app M) ≫
        (SheafOfModules.overFunctorMap.{u} (localCoefficientRings S) f).hom.app
          (whole.transport.modules.functor.obj M))
  furtherIdentity : ∀ (X : E)
      (M : PresentationModules (presentationElementRing R (F.obj X))),
    HEq ((further (𝟙 X)).hom.app M)
      (𝟙 ((modules X).transport.modules.functor.obj M))
  furtherComposition : ∀ {X Y Z : E} (f : X ⟶ Y) (h : Y ⟶ Z)
      (M : PresentationModules (presentationElementRing R (F.obj Z))),
    HEq ((further (f ≫ h)).hom.app M)
      ((further f).hom.app
          ((elementModulePullbackOver.{u, u} (localCoefficientRings R) (F.map h)
            (continuous h)).obj M) ≫
        (SheafOfModules.overMap.{u} (localCoefficientRings S) f).map
          ((further h).hom.app M))

/-- Ringed transport along a presenting nerve can be chosen compatibly with every
actual localized site, with identity and composition equations on module comparisons.

Source: Stacks Project, Sites, Tags 00Y1 and 04GZ (the fibre description), 03EH
(relocalization); Modules on Sites, Tags 03CR, 04IE and 04J4.
(blueprint: lem-sp-ringed-nerve-slice-transport).

Proof in words: the formula for the whole nerve identifies a section of its image of
an internal object B at X with a map F(X) → B. The formula for the slice nerve identifies
its sections at (T → X) with maps over F(X). For the restricted ring, projection from
a lift in R × F(X) to its R component identifies this ring with S.over X. This is an
isomorphism of rings: zero, one, sums and products are all computed on the R component.
Conjugate the slice equivalence by the supplied element-site fibre equivalence and use
this structural isomorphism to obtain the displayed ringed equivalence. Its module
direct image is the one determined by the geometric adjunction and this ring map.
Transport the additive and scalar operations through the inverse equivalence; the
structural equation identifies its inverse module functor with the specified direct
image, giving a RingedPresentationAt on each slice.

For restriction, send a lift (m,c) to m, and use m ↦ (m,c) for its inverse. These maps are
linear because both addition and scalar multiplication are computed on m. They are
natural in the module and in arrows T → X. For an arrow X → Y the same projection from
a lift in the pullback gives further restriction. Choose these projections throughout.
Both sides of the restriction-composition equation send a lift to its m component;
the identity comparison does too, and both sides for two further restrictions do too.
Sectionwise extensionality, followed by faithfulness of the module forgetful functor,
proves the equations, including the stated transports of domains (HEq). Finally, any
specified whole module transport is conjugate to the transported-operation construction
by the unique adjunction-compatible comparison: both module functors are left adjoints
to the specified induced module direct image. Conjugate all restriction comparisons
by this single comparison. Its inverse
factors cancel in each composition, so all three normalization equations persist.
No assumption about subterminals, a cover, or generators beyond the supplied nerve
equivalence enters this argument. -/
theorem exists_ringedNerveSliceTransport
    {C E : Type u} [SmallCategory C] [SmallCategory E] [HasFiniteLimits E]
    {J : GrothendieckTopology C} (K : GrothendieckTopology E) [K.Subcanonical]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful] [PreservesFiniteLimits F]
    (N : Sheaf J (Type u) ≌ Sheaf K (Type u))
    (n : N.functor ⋙ sheafToPresheaf K (Type u) ≅ sheafSubcategoryNerve F)
    (g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R))
    (inverseNerve : g.inverse = N.functor) [IsIso g.ringMap]
    (whole : RingedPresentationAt g)
    (sourceSlice : ∀ X : E, RingedSheafSliceAdjunctionData
      (localCoefficientRings R) (F.obj X))
    (slice : ∀ X : E, Over (F.obj X) ≌ Sheaf (K.over X) (Type u))
    (sliceFormula : ∀ X : E,
      (slice X).functor ⋙ sheafToPresheaf (K.over X) (Type u) ≅
        yoneda ⋙ (Functor.whiskeringLeft (Over X)ᵒᵖ
          (Over (F.obj X))ᵒᵖ (Type u)).obj (Over.post F).op)
    (continuous : ∀ {X Y : E} (f : X ⟶ Y),
      Functor.IsContinuous (elementMap (F.map f))
        (elementTopology (F.obj X)) (elementTopology (F.obj Y))) :
    Nonempty (RingedNerveSliceTransport R S g whole F sourceSlice slice continuous) := by
  sorry

end CategoryTheory
