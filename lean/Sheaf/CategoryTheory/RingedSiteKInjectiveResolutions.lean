/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf

/-!
# Functorial K-injective resolutions on small ringed sites

Source: Stacks Project, Cohomology on Sites, Section 07A5, first paragraph,
and Injectives, Theorem 079P (blueprint: prop-pur-kinjective-resolutions-exist).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

set_option synthInstance.maxHeartbeats 100000 in
-- Coproduct inference reduces the repeated sheaf-compose expression in the summands.
/-- The module category on a small commutative ringed site is Grothendieck abelian,
with the coproduct of the localized rank-one extensions as a generator. Every
integer-indexed cochain complex has a functorial K-injective resolution whose
terms are injective.

Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: prop-pur-kinjective-resolutions-exist).

Proof:
1. Apply `lem-pur-ringed-site-grothendieck-abelian` to obtain the Grothendieck
   property and the stated generator: sheafify the extension-by-zero presheaf
   of the unit module on each localized site and take their coproduct.
2. Apply `lem-pur-kinjective-degreewise-existence` to this Grothendieck abelian
   category. Its functor I and transformation eta provide quasi-isomorphisms
   into K-injective complexes with injective terms. Naturality of eta and the
   functor's action on chain maps give precisely the asserted functoriality. -/
theorem grothendieckAbelian_and_functorial_kInjective_resolutions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u}) :
    IsGrothendieckAbelian.{u}
        (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ∧
      IsSeparator (∐ fun U : C ↦
        (PresheafOfModules.sheafification.{u}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).obj
          ((extensionByZeroPresheaf.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).obj
            (unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)))) ∧
      ∃ (I : CochainComplex
          (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ ⥤
          CochainComplex
          (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ)
        (η : 𝟭 (CochainComplex
          (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ) ⟶ I),
        ∀ (M : CochainComplex
          (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ),
          QuasiIso (η.app M) ∧ (I.obj M).IsKInjective ∧
            ∀ n : ℤ, Injective ((I.obj M).X n) := by
  sorry

end SheafOfModules
