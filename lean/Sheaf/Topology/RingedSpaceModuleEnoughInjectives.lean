/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Enough injectives for modules on a ringed space

Source: Stacks Project, Injectives, Lemma 01DI; Modules on Sites, Lemma 03DA
(blueprint: lem-sc-ringed-space-module-sheaves-enough-injectives).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/-- The category of module sheaves on any ringed space is abelian and has enough injectives:
every module sheaf embeds into an injective module sheaf.

Source: Stacks Project, Injectives, Lemma 01DI; Modules on Sites, Lemma 03DA
(blueprint: lem-sc-ringed-space-module-sheaves-enough-injectives).

Proof: Regard the open subsets of `X`, inclusions, and open covers as a small site.
The structure sheaf is a sheaf of commutative rings on this site, and its module sheaves
are exactly `SheafOfModules` over its underlying ring sheaf `moduleRings X`
(`def-weil-locally-ringed-space-morphism`, `def-weil-sheaf-of-modules-category`).
Mathlib supplies the abelian instance. The proved upstream theorem
`SheafOfModules.isGrothendieckAbelian` supplies the Grothendieck structure.
By `lem-sp-grothendieck-enough-injectives` it has
enough injectives: each module sheaf has a monomorphism into an injective object, in the
sense of `def-sp-injective-resolutions`. -/
theorem moduleSheaves_abelian_enoughInjectives (X : RingedSpace.{u}) :
    Nonempty (Abelian (SheafOfModules.{u} (moduleRings X))) ∧
    EnoughInjectives (SheafOfModules.{u} (moduleRings X)) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X)
  exact ⟨⟨inferInstance⟩, inferInstance⟩

end AlgebraicGeometry.RingedSpace
