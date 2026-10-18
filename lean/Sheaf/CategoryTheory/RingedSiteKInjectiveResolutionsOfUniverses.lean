/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free

/-! # K-injective resolutions with independent site universes

Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: prop-pur-kinjective-resolutions-exist).
The free lifted Yoneda sheaves are precisely the sheafifications of the localized
rank-one extension presheaves. Their use preserves the generator in the source statement.
-/

@[expose] public section

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Grothendieck abelianness, the specified free-sheaf generator, and functorial
K-injective resolutions with injective terms, without equating site universes.
Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: prop-pur-kinjective-resolutions-exist).
Proof:
1. Form the free module on the lifted representable at each site object. Its
sections are finite linear combinations of arrows into that object, exactly the
extension-by-zero presheaf of the localized unit. Sheafification makes these a
separating family, by the free-Yoneda/sheafification adjunction. Their coproduct
is a separator. Kernels and filtered colimits are computed on underlying abelian
sheaves, where filtered colimits are exact. All index sets fit max c v r.
2. Apply the small-object construction of the source library to this Grothendieck
abelian category: factor each map M→0 functorially by the monomorphic
quasi-isomorphisms. The resulting target is K-injective, and its terms are
injective by the degreewise lifting criterion. The first factor supplies the
natural quasi-isomorphism; the construction is functorial on chain maps. -/
theorem grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r}) :
    IsGrothendieckAbelian.{max c v r}
      (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ∧
    IsSeparator (∐ fun U : C ↦
      (PresheafOfModules.sheafification.{max c v r} (𝟙 ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)).obj
        ((PresheafOfModules.free ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj).obj
          (uliftYoneda.{max c v r}.obj U))) ∧
    ∃ (I : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
        CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
      (η : 𝟭 (CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) ⟶ I),
      ∀ M : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
        QuasiIso (η.app M) ∧ (I.obj M).IsKInjective ∧
          ∀ n : ℤ, Injective ((I.obj M).X n) := by
  sorry

end SheafOfModules
