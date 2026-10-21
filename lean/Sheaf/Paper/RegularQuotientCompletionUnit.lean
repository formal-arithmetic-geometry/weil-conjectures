/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.DerivedCompleteKoszulReconstruction
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # The canonical regular-quotient completion unit

Source: Stacks Project, algebraization.tex, Tags 0999, 099B and 0A0E,
lemma-derived-completion-koszul; sites-cohomology.tex, Tag 0941;
Bhatt--Scholze, Lemma 3.4.12
(blueprint: lem-pur-regular-quotient-completion-unit).

The quotient tower is indexed by `n : ℕ`, representing the positive power `n+1`.
Its tensor order is the canonical symmetric model `(O/a^(n+1))[0] ⊗ P`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})

/-- The strict quotient augmentation is the degree-zero Koszul augmentation followed
by the canonical Koszul-to-quotient map. Its components are exactly
`koszulRepresentativeQuotient`, by `koszulRepresentativeAugmentation_quotient`.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-regular-quotient-completion-unit). -/
def regularQuotientAugmentation
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections) :
    (Functor.const ℕᵒᵖ).obj P ⟶ reductionTensorTower R P a :=
  koszulStrictAugmentation R P a ≫ koszulTensorTowerComparison R P a

/-- The actual shifted cone of one minus the quotient-tower shift on products.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-regular-quotient-completion-unit). -/
def regularQuotientCompletion
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections) :
    CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
  roosF.obj (koszulTowerComplex R (reductionTensorTower R P a))

/-- The specified zero-component unit, constructed by the strict Roos augmentation.
In the canonical coordinates it is `(0,(q_n)_n)`, not a chosen lift in the derived
category. Compatibility is the naturality of the strict quotient augmentation.
Source: Stacks Tags 0A0E and 0941; Bhatt--Scholze Lemma 3.4.12
(blueprint: lem-pur-regular-quotient-completion-unit). -/
def regularQuotientCompletionUnit
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections) :
    P ⟶ regularQuotientCompletion R P a :=
  roosAugment (X := koszulTowerComplex R (reductionTensorTower R P a))
    (fun n ↦ (regularQuotientAugmentation R P a).app (op n))
    (fun n ↦ ((regularQuotientAugmentation R P a).naturality
      (homOfLE (Nat.le_succ n)).op).symm.trans (Category.id_comp _))

/-- Completion is locally derived complete, and local completeness, invertibility of
its actual zero-component unit, and a Roos triangle with the prescribed quotient
components are equivalent. The ideal `(a)` is represented by multiplication by `a`
on the rank-one ring module; regularity makes this a mono. Thus its sectionwise
image is precisely the principal ideal on every slice.

Source: Stacks Tags 0999, 099B, 0A0E (lemma-derived-completion-koszul), and 0941;
Bhatt--Scholze Lemma 3.4.12 (blueprint: lem-pur-regular-quotient-completion-unit).

Proof plan:
1. Compare the strict one-generator Koszul tensor tower with the quotient tower.
   Every power of multiplication by `a` is injective. The regular Koszul reconstruction
   theorem makes this an augmentation-compatible derived-limit isomorphism, using
   K-flatness of `P`, without assuming that its individual terms are flat.
2. Exact countable products give the normalized strict Roos comparison for the
   quotient tower. Its augmentation normalization identifies this precise zero-component
   map with the derived quotient augmentation. Compose with the inverse of the Koszul
   comparison to identify it with the reflector's degree-zero Koszul unit.
3. The ringed Koszul completion reflector for the singleton list `(a)` is complete on
   every slice and for every local element of the generated ideal. Its unit is invertible
   exactly on complete objects. Transport these facts through the unit-compatible
   comparison, using preservation of isomorphisms by restriction and internal Hom.
4. If the specified unit is invertible, transport the natural distinguished Roos
   triangle of the strict-tower derived limit along its composite with the normalized
   comparison. The projection normalization gives precisely the quotient components.
5. Conversely regular Koszul reconstruction applied to the prescribed quotient Roos
   triangle identifies `P` with the Koszul completion. Reflector completeness transports
   back to `P`, and step 3 makes the specified unit invertible. An arbitrary triangle
   comparison is never identified with that unit.
-/
theorem regularQuotientCompletionUnit_criterion
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over V)))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections)
    (_ha : Mono (globalSectionMultiplication R a))
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsLocallyDerivedRingedIdealComplete R
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (globalSectionMultiplication R a)
      (DerivedCategory.Q.{w}.obj (regularQuotientCompletion R P a)) ∧
    (IsLocallyDerivedRingedIdealComplete R
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (globalSectionMultiplication R a) (DerivedCategory.Q.{w}.obj P) ↔
      IsIso (DerivedCategory.Q.{w}.map (regularQuotientCompletionUnit R P a))) ∧
    (IsIso (DerivedCategory.Q.{w}.map (regularQuotientCompletionUnit R P a)) ↔
      ∃ (_hU : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
          ((reductionTensorTower R P a).obj (op n))))
        (p : DerivedCategory.Q.{w}.obj P ⟶ ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
          ((reductionTensorTower R P a).obj (op n))))
        (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
          ((reductionTensorTower R P a).obj (op n)))) ⟶
          (DerivedCategory.Q.{w}.obj P)⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
            ((reductionTensorTower R P a).map (homOfLE (Nat.le_succ n)).op))
          (DerivedCategory.Q.{w}.obj P) p δ ∧
        ∀ n : ℕ, p ≫ Limits.Pi.π _ n =
          DerivedCategory.Q.{w}.map (koszulRepresentativeQuotient R P a n)) := by
  sorry

end CategoryTheory
