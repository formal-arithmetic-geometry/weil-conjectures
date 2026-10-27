/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module
public import Sheaf.CategoryTheory.NativeRingedRestrictionEquivalence
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.Algebra.Homology.SitePerfectModelRestriction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! # Restriction on slices and its derived square

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(blueprint: lem-pur-native-ringed-restriction-slices). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option maxErrors 4
set_option backward.isDefEq.respectTransparency false
universe c d vc vd r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
variable {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
  {K : GrothendieckTopology C} {J : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsEquivalence] [F.IsDenseSubsite K J]

/-- The induced equivalence of slices is dense. Rewrite covering sieves using the over-site
correspondence; pushforward then becomes the original site pushforward, so density follows from
its covering criterion.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(blueprint: lem-pur-native-ringed-restriction-slices). -/
theorem sliceDense (U : C) :
    (Over.post F (X := U)).IsDenseSubsite (K.over U) (J.over (F.obj U)) where
  functorPushforward_mem_iff := by
    intro X S
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_functorPushforward_post]
    exact F.functorPushforward_mem_iff K J

attribute [local instance] sliceDense
variable (R : Sheaf J CommRingCat.{max c d vc vd r})
/-- Direct module restriction commutes with restriction to a slice. Both composites evaluate the
same presheaf at the same object and arrow, so the comparison is the identity natural
isomorphism.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(blueprint: lem-pur-native-ringed-restriction-slices). -/
def sliceRestrictionIso (U : C) :
    SheafOfModules.overFunctor.{max c d vc vd r}
        (NativeRings.{max c d vc vd r, d, vd} R) (F.obj U) ⋙
      restrictModules.{max c vc, max d vd, vc, vd, r} (K := K.over U) (Over.post F) (R.over (F.obj
        U)) ≅
    restrictModules.{c, d, vc, vd, r} (K := K) F R ⋙
      SheafOfModules.overFunctor.{max c d vc vd r}
        (NativeRings.{max c d vc vd r, c, vc}
          (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)) U := by
  exact Iso.refl _

/-- Restriction on each slice is an equivalence. The slice equivalence is dense by the preceding
covering-sieve calculation, so apply the module equivalence associated with that ringed site
equivalence.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(blueprint: lem-pur-native-ringed-restriction-slices). -/
theorem sliceModulesEquivalence (U : C) :
    (restrictModules.{max c vc, max d vd, vc, vd, r}
      (K := K.over U) (Over.post F) (R.over (F.obj U))).IsEquivalence := by
  let : (Over.post F).asEquivalence.symm.inverse.IsDenseSubsite
      (K.over U) (J.over (F.obj U)) := sliceDense F U
  exact restrictModules_isEquivalence.{max d vd, max c vc, vd, vc, r}
    (Over.post F).asEquivalence.symm (R.over (F.obj U))

/-- Direct restriction on the original site is an equivalence. Apply the structural ringed
equivalence comparison to the inverse of the given equivalence.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(blueprint: lem-pur-native-ringed-restriction-slices). -/
theorem globalModulesEquivalence :
    (restrictModules.{c, d, vc, vd, r} (K := K) F R).IsEquivalence := by
  let : F.asEquivalence.symm.inverse.IsDenseSubsite K J := inferInstanceAs
    (F.IsDenseSubsite K J)
  exact restrictModules_isEquivalence.{d, c, vd, vc, r} F.asEquivalence.symm R

attribute [local instance] globalModulesEquivalence sliceModulesEquivalence

variable (U : C)
  [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify (J.over (F.obj U)) AddCommGrpCat.{max c d vc vd r}]
  [(J.over (F.obj U)).WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify (K.over U) AddCommGrpCat.{max c d vc vd r}]
  [(K.over U).WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]

variable
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, d, vd} R)]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, c, vc}
    (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R))]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max d vd, vd} (R.over (F.obj U)))]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
    ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U))]

/-- The exact derived restriction square commutes. Both module restrictions are additive
equivalences; the two over-functors are exact. Descend their identity square to derived
categories and compose the two derived-composition comparison isomorphisms.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(blueprint: lem-pur-native-ringed-restriction-slices). -/
def sliceDerivedRestrictionIso :
    let Tg := restrictModules.{c, d, vc, vd, r} (K := K) F R
    let Ts := restrictModules.{max c vc, max d vd, vc, vd, r}
      (K := K.over U) (Over.post F) (R.over (F.obj U))
    let A := SheafOfModules.overFunctor.{max c d vc vd r}
      (NativeRings.{max c d vc vd r, d, vd} R) (F.obj U)
    let B := SheafOfModules.overFunctor.{max c d vc vd r}
      (NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)) U
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd,
      max c d vc vd r} (NativeRings.{max c d vc vd r, d, vd} R) (F.obj U)).1
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd,
      max c d vc vd r} (NativeRings.{max c d vc vd r, d, vd} R) (F.obj U)).2
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc,
      max c d vc vd r} (NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)) U).1
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc,
      max c d vc vd r} (NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)) U).2
    letI : HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r}
      ((NativeRings.{max c d vc vd r, d, vd} R).over (F.obj U))) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max d vd, vd}
          (R.over (F.obj U))))
    letI : HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
      (restrictedCommRing.{max c vc, max d vd, vc, vd, r} (K := K.over U)
        (Over.post F) (R.over (F.obj U)))) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
          ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U)))
    letI : HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r}
      ((NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)).over U)) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
          ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U)))
    A.mapDerivedCategory ⋙ Ts.mapDerivedCategory ≅
      Tg.mapDerivedCategory ⋙ B.mapDerivedCategory := by
  dsimp only
  letI : HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r}
      ((NativeRings.{max c d vc vd r, d, vd} R).over (F.obj U))) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max d vd, vd}
          (R.over (F.obj U))))
  letI : HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
      (restrictedCommRing.{max c vc, max d vd, vc, vd, r} (K := K.over U)
        (Over.post F) (R.over (F.obj U)))) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
          ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U)))
  letI : HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r}
      ((NativeRings.{max c d vc vd r, c, vc}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)).over U)) := inferInstanceAs
        (HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
          ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U)))
  letI := globalModulesEquivalence.{c, d, vc, vd, r} (K := K) F R
  letI := sliceModulesEquivalence.{c, d, vc, vd, r} (K := K) F R U
  let Rg := NativeRings.{max c d vc vd r, d, vd} R
  let Rs := NativeRings.{max c d vc vd r, c, vc}
    (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd, max c d vc vd r} Rg (F.obj U)).1
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd, max c d vc vd r} Rg (F.obj U)).2
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc, max c d vc vd r} Rs U).1
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc, max c d vc vd r} Rs U).2
  let A := SheafOfModules.overFunctor.{max c d vc vd r} Rg (F.obj U)
  let B := SheafOfModules.overFunctor.{max c d vc vd r} Rs U
  let Tg := restrictModules.{c, d, vc, vd, r} (K := K) F R
  let Ts := restrictModules.{max c vc, max d vd, vc, vd, r}
    (K := K.over U) (Over.post F) (R.over (F.obj U))
  letI : Ts.Additive := restrictModules_additive.{max c vc, max d vd, vc, vd, r}
    (K := K.over U) (Over.post F) (R.over (F.obj U))
  letI : Tg.Additive := restrictModules_additive.{c, d, vc, vd, r} (K := K) F R
  letI : A.Additive := SheafOfModules.sitePerfectOverFunctor_additive.{d, vd,
    max c d vc vd r} Rg (F.obj U)
  letI : B.Additive := SheafOfModules.sitePerfectOverFunctor_additive.{c, vc,
    max c d vc vd r} Rs U
  exact (Functor.mapDerivedCategoryCompIso A Ts).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sliceRestrictionIso.{c, d, vc, vd, r} F R U) ≪≫
      Functor.mapDerivedCategoryCompIso Tg B

end CategoryTheory.NativeRestriction
