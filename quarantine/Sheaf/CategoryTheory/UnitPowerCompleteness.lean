/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedExtendedCech
public import Sheaf.CategoryTheory.RingedCompletionUnit
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.CategoryTheory.RingedKoszulSystem
import Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal
import Sheaf.CategoryTheory.RingedCechKoszulDualLimit
import Sheaf.Paper.WeilCompletedTensorReflector

/-!
# Derived completeness under a unit times a positive power

Source: Stacks Project, algebraization.tex, Tags 0998, 0999, 099B and 0A0E
(blueprint: lem-pur-unit-power-completeness).

The principal ideal sheaf is the categorical image of multiplication by its generator.
Thus its sections include locally divisible sections, without requiring a global coefficient.
The comparison uses the actual two-term complexes and their augmentation-induced units.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Multiplying a positive power by a unit changes neither local derived completeness nor
its reflection, including the specified augmentation-induced units.

Source: Stacks Project, algebraization.tex, Tags 0998 (ideal of complete elements),
0999 (derived completeness), 099B (augmented localization model), and 0A0E (Koszul model)
(blueprint: lem-pur-unit-power-completeness).

`image (ringedKoszulScalar O c)` with `image.ι` is exactly the ideal subsheaf generated
by `c`, since categorical images of module sheaves sheafify sectionwise images.
`hu` expresses invertibility of the global section: its sectionwise inverses are unique,
hence commute with restriction and give a global inverse. It imposes no nonzero-ring
condition. All derived objects are unbounded. The chosen derived-category instances
only specify the localization and the size of its morphisms, also on every slice.

Proof:
1. On an object V, write R = O(V). In R[1/b], the inverse of a is u⁻¹(b⁻¹)^e.
   In R[1/a], the inverse of b is u b^(e-1) a⁻¹, using e ≥ 1. Localization gives inverse
   R-algebra maps lambda and mu. On fractions these are x/a^n ↦ x u^(-n)/b^(en) and
   x/b^n ↦ x u^n b^((e-1)n)/a^n. They commute with restrictions, so sheafification
   gives inverse maps of the recorded sectionwise localization sheaves on every slice
   (def-weil-pbc-ringed-section-localization).
2. Contravariant derived internal Hom carries these slice isomorphisms to isomorphisms.
   The complete-elements ideal theorem (lem-weil-pbc-ringed-derived-complete-elements-ideal)
   identifies vanishing at the generator on every slice with vanishing at every section
   of the generated ideal, including sections with coefficients only locally. This proves
   the first clause for a and b.
3. The identity in degree zero and lambda in degree one give an isomorphism
   [O → O[1/a]] ≅ [O → O[1/b]]. Its differential square is the compatibility with O.
   The inverse has components identity and mu. Both augmentations have degree-zero
   identity and are zero in degree one, so this isomorphism preserves them as chain maps
   (def-weil-pbc-ringed-extended-cech).
4. Apply contravariant derived internal Hom. Its inverse comparison gives the displayed
   natural isomorphism from the a functor to the b functor. The units are augmentation
   pullback after the fixed evaluation-at-one map, so the augmentation equality gives
   eta_a followed by alpha = eta_b (def-weil-pbc-ringed-completion-unit).
5. For c = a and c = b, apply lem-weil-pbc-ringed-cech-koszul-dual-limit to the singleton
   list. It compares this functor with the total derived limit of the strict tower
   N ⊗ᴸ [O --c^m--> O] in degrees -1,0, with transitions (c,1), preserving its actual
   degree-zero unit. The completeness and Hom-bijection clauses of
   lem-weil-pbc-ringed-koszul-completion-reflector transfer across this unit-preserving
   isomorphism. No regularity, Noetherian condition, or exactness of products is used. -/
theorem unit_power_localDerivedComplete
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (a b unit : (O.obj ⋙ forget CommRingCat).sections) (e : ℕ)
    (hu : ∀ U : Cᵒᵖ, IsUnit (unit.val U)) (he : 1 ≤ e)
    (hab : ∀ U : Cᵒᵖ, a.val U = unit.val U * b.val U ^ e) :
    (∀ N : ringedSiteDerived O,
      IsLocallyDerivedRingedIdealComplete O
        (image (ringedKoszulScalar O a)) (image.ι (ringedKoszulScalar O a)) N ↔
      IsLocallyDerivedRingedIdealComplete O
        (image (ringedKoszulScalar O b)) (image.ι (ringedKoszulScalar O b)) N) ∧
    (∃ alpha : ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O a) ≅
        ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O b),
      ∀ N : ringedSiteDerived O,
        ringedCechCompletionUnit O (ringedLocalizationTwoTerm O a)
          (ringedLocalizationTwoTermAugmentation O a) N ≫ alpha.hom.app N =
        ringedCechCompletionUnit O (ringedLocalizationTwoTerm O b)
          (ringedLocalizationTwoTermAugmentation O b) N) ∧
    ∀ c : (O.obj ⋙ forget CommRingCat).sections, c = a ∨ c = b →
      (∀ N : ringedSiteDerived O,
        IsLocallyDerivedRingedIdealComplete O
          (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c))
          ((ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O c)).obj N)) ∧
      ∀ (N L : ringedSiteDerived O),
        IsLocallyDerivedRingedIdealComplete O
          (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c)) L →
        Function.Bijective
          (fun f : (ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O c)).obj N ⟶ L ↦
            ringedCechCompletionUnit O (ringedLocalizationTwoTerm O c)
              (ringedLocalizationTwoTermAugmentation O c) N ≫ f) := by
  sorry

end CategoryTheory
