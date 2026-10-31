/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceReindexIsIso
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan

/-! # Invariance of an immersive generating system under isomorphism and reindexing

Source: Stacks Project, Constructions, Tag 01NE, classification by invertible
modules with generating sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

attribute [local irreducible] homOfGeneratingSections

private theorem chart_hom_ext {S : Scheme.{u}} {I : Type u}
    {W : Scheme.{u}} {a b : W ⟶ ℙ(I; S)} (i : I)
    (ha : a ⁻¹ᵁ standardOpen I S i = ⊤) (hb : b ⁻¹ᵁ standardOpen I S i = ⊤)
    (hS : a ≫ ℙ(I; S) ↘ S = b ≫ ℙ(I; S) ↘ S)
    (hr : ∀ j, a.appLE (standardOpen I S i) ⊤ ha.ge (coordRatio I S i j) =
      b.appLE (standardOpen I S i) ⊤ hb.ge (coordRatio I S i j)) : a = b := by
  let Z := Spec (CommRingCat.of (ULift.{u} ℤ))
  let z : S ⟶ Z := specULiftZIsTerminal.from S
  have hpre : map I z ⁻¹ᵁ standardOpen I Z i = standardOpen I S i := by
    rw [standardOpen, ← Scheme.Hom.comp_preimage, map_toProjInt]
    rfl
  have ha' : (a ≫ map I z) ⁻¹ᵁ standardOpen I Z i = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hpre, ha]
  have hb' : (b ≫ map I z) ⁻¹ᵁ standardOpen I Z i = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hpre, hb]
  have h : a ≫ map I z = b ≫ map I z := by
    apply hom_ext_of_preimage_standardOpen_eq_top i ha' hb'
    · exact specULiftZIsTerminal.hom_ext _ _
    · intro j
      have ea := Scheme.Hom.appLE_comp_appLE a (map I z)
        (standardOpen I Z i) (standardOpen I S i) ⊤ hpre.ge ha.ge
      have eb := Scheme.Hom.appLE_comp_appLE b (map I z)
        (standardOpen I Z i) (standardOpen I S i) ⊤ hpre.ge hb.ge
      rw [← ea, ← eb, CommRingCat.comp_apply, CommRingCat.comp_apply,
        map_appLE_coordRatio]
      exact hr j
  apply hom_ext I S hS
  simpa only [Category.assoc, map_toProjInt (S := S) (T := Z) I z] using
    congrArg (fun q ↦ q ≫ toProjInt I Z) h

attribute [local instance] coordinateReindex_isIso

attribute [local irreducible] ProjectiveSpace.homOfIsFreeGenerator

end AlgebraicGeometry.ProjectiveSpace
