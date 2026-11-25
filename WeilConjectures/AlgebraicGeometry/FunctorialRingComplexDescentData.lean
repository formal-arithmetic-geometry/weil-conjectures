/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteIdealGeneratingCover
public import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexSheaf
public import WeilConjectures.CategoryTheory.AugmentedComplexGluing
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.AlgebraicGeometry.FunctorialRingComplexIdealDescent
import WeilConjectures.AlgebraicGeometry.RingedGeneratingListsLocalEquality

/-!
# Strict descent data for sheafified functorial ring complexes

## References

* Stacks Project, Tag 099E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace CategoryTheory

/-- The explicit augmented model on a slice with a specified generating list. (Stacks, Tag 099E) -/
abbrev ringFamilySliceModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m)
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (p : RingedIdealGeneratingIndex O I ι) :=
  ringFamilySheafModel (O.over p.U) K ε m hm p.r
    (fun i ↦ ringedSliceSection O p.U (p.f i))

/-- The sheafified ring-family slice complexes carry strict descent data, including their
augmentations. This assertion involves no Čech complex or derived comparison.
(Stacks, Tag 099E) -/
theorem exists_ringFamily_descentData
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι]
    (K : RingComplexFamily.{u}) (ε : RingComplexAugmentations K)
    (m : RingComplexMaps K) (hm : RingComplexFunctorial K ε m) :
    Nonempty (SheafOfModules.AugmentedComplexGlueData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
      (fun p : RingedIdealGeneratingIndex O I ι ↦ p.U) (ringedSiteRingComplex O)
      (fun p ↦ (ringFamilySliceModel O K ε m hm I ι p).1)
      (fun p ↦ (ringFamilySliceModel O K ε m hm I ι p).2 ≫
        (ringedRestrictionRingComplexIso O p.U).inv)) := by
  apply exists_ringFamily_idealDescentData O K ε m hm
    (fun p : RingedIdealGeneratingIndex O I ι ↦ p.U)
    (fun p ↦ p.r) (fun p ↦ p.f)
  intro p q W a b
  exact exists_cover_generatingLists_ideal_eq O I ι
    p.U p.r p.f p.generates q.U q.r q.f q.generates W a b

end CategoryTheory
