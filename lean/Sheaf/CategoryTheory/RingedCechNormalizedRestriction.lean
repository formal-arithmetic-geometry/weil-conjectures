/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem

/-! # Normalized restriction of the Cech internal-Hom functor

Source: Stacks Project, Tag 08JB. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]

/-- Cech internal Hom restricts to slices and between slices, preserving augmentation units.
No strict inverse limit or comparison with Koszul completion occurs in this statement.
Source: Stacks Project, Cohomology on Sites, Tag 08JB, applied to the localization
complex of More on Algebra, Tag 0913.
(blueprint: lem-weil-pbc-ringed-cech-normalized-restriction).

Proof: sectionwise localization commutes with restriction to a slice. Restriction is
exact, commutes with the sheafified tensor product, and preserves finite sums and
totalizations. Induction on the ordered factors thus identifies the restricted Cech
complex with the slice Cech complex, including its degree-zero augmentation. Apply
the derived internal-Hom restriction theorem to this identification. On a K-injective
target representative, every component is restriction of a local linear map, and the
map from Hom(O,-) is evaluation at one. Consequently restriction carries the
augmentation-induced unit to the same unit on the slice. The same construction
along overMap gives the second assertion: on W to V to U the localizations and local
linear maps are the same, with their canonical coefficient transports. Empty lists,
zero sections and the zero ring require no change to this calculation. -/
theorem ringedCech_normalized_restriction :
    ∃ (sigma : ∀ U : C,
      ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ⋙
          ringedDerivedRestriction O U ≅
        ringedDerivedRestriction O U ⋙ ringedCechCompletionFunctor (O.over U)
          (ringedExtendedCech (O.over U) r
            (fun i ↦ ringedKoszulSliceSection O (b i) U)).1)
      (tau : ∀ (U V : C) (f : V ⟶ U),
        ringedCechCompletionFunctor (O.over U)
            (ringedExtendedCech (O.over U) r
              (fun i ↦ ringedKoszulSliceSection O (b i) U)).1 ⋙
            ringedKoszulDerivedOverMap O f ≅
          ringedKoszulDerivedOverMap O f ⋙ ringedCechCompletionFunctor (O.over V)
            (ringedExtendedCech (O.over V) r
              (fun i ↦ ringedKoszulSliceSection O (b i) V)).1),
      (∀ (U : C) E,
        (ringedDerivedRestriction O U).map
            (ringedCechCompletionUnit O (ringedExtendedCech O r b).1
              (ringedExtendedCech O r b).2 E) ≫ (sigma U).hom.app E =
          ringedCechCompletionUnit (O.over U)
            (ringedExtendedCech (O.over U) r
              (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
            (ringedExtendedCech (O.over U) r
              (fun i ↦ ringedKoszulSliceSection O (b i) U)).2
            ((ringedDerivedRestriction O U).obj E)) ∧
      (∀ (U V : C) (f : V ⟶ U) E,
        (ringedKoszulDerivedOverMap O f).map
            (ringedCechCompletionUnit (O.over U)
              (ringedExtendedCech (O.over U) r
                (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
              (ringedExtendedCech (O.over U) r
                (fun i ↦ ringedKoszulSliceSection O (b i) U)).2 E) ≫
            (tau U V f).hom.app E =
          ringedCechCompletionUnit (O.over V)
            (ringedExtendedCech (O.over V) r
              (fun i ↦ ringedKoszulSliceSection O (b i) V)).1
            (ringedExtendedCech (O.over V) r
              (fun i ↦ ringedKoszulSliceSection O (b i) V)).2
            ((ringedKoszulDerivedOverMap O f).obj E)) := by sorry

end CategoryTheory
