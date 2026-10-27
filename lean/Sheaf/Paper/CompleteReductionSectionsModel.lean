/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.StrictRoosModel

/-! # Ordinary sections and the strict section-tower comparison

Source: Stacks Project, Cohomology on Sites, Tags 0D6K and 0941.
(blueprint: def-sfb-complete-reduction-sections-model).

These are the unchanged constructions previously in CompleteReductionRgammaUpperBound.
They are separated so the comparison and Milnor steps can use the same constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CompleteReductionSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (U : Scheme.{u})

/-- Ordinary section groups of integral internal modules, evaluated at the identity
object of the small pro-etale site. No completion is applied to sections.
Source: Stacks 0D6K (blueprint: def-sfb-complete-reduction-sections-model). -/
abbrev sections : AdicCompletion.Modules l E U ⥤ Ab.{u + 1} :=
  Mod.forget (AdicCompletion.ring l E U) ⋙
    sheafToPresheaf (Scheme.ProEt.topology U) Ab.{u + 1} ⋙
      (evaluation U.ProEtᵒᵖ Ab.{u + 1}).obj (op (Scheme.ProEt.mk (𝟙 U)))

/-- The total right derived functor of ordinary module sections, computed in the
internal-module category on K-injective resolutions.
Source: Stacks 0D6K (blueprint: def-sfb-complete-reduction-sections-model). -/
abbrev rgamma : DerivedCategory (AdicCompletion.Modules l E U) ⥤
    DerivedCategory Ab.{u + 1} := (sections l E U).rightDerivedFunctor

/-- Termwise ordinary sections on a complex of strict integral-module towers.
Source: Stacks 0A07 (blueprint: def-sfb-complete-reduction-sections-model). -/
abbrev sectionTower (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Ab.{u + 1}) ℤ :=
  (((Functor.whiskeringRight ℕᵒᵖ (AdicCompletion.Modules l E U) Ab.{u + 1}).obj
    (sections l E U)).mapHomologicalComplex (.up ℤ)).obj I

/-- The chain comparison from sections of the ordinary tower limit to the strict Roos
fibre. It is the product of the actual limit projections, with zero nullhomotopy.
Source: Stacks 0D6K and 0941
(blueprint: def-sfb-complete-reduction-sections-model). -/
def limitToRoos (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ) :
    ((sections l E U).mapHomologicalComplex (.up ℤ)).obj (limit I.asFunctor) ⟶
      roosF.obj (sectionTower l E U I) :=
  roosAugment
    (fun n ↦ ((sections l E U).mapHomologicalComplex (.up ℤ)).map
      (limit.π I.asFunctor (op n)))
    (by
      intro n
      change _ ≫ ((sections l E U).mapHomologicalComplex (.up ℤ)).map
        (I.asFunctor.map (homOfLE (Nat.le_succ n)).op) = _
      rw [← Functor.map_comp, limit.w])

end AlgebraicGeometry.ProEtale.CompleteReductionSections
