/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedMappingAction.Step.DerivedMappingSingleStepConstruction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerivedLinear
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedMappingAction.HomModel.DerivedMappingCohomologyCycles

/-! # Shift and cohomology compatibility on K-injective representatives

Source: Stacks 070I, 070Y, 09L9; Step 6 of the mapping-complex action argument.
(blueprint: lem-sf-derived-mapping-representative-shift-cohomology)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe b v u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.DerivedMappingAction

variable {B : Type b} [CommRing B]
  [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))]
  {A : Type u} [Category.{v} A] [Abelian A] [Linear B A]
  [HasDerivedCategory.{w} A]

variable {A' : Type u} [Category.{v} A'] [Abelian A'] [Linear B A']
  [HasDerivedCategory.{w} A']
  {S : HomModel (B := B) A} {T : HomModel (B := B) A'}
  {e : Step (B := B) A A'}

/-- On K-injective pairs the normalized arrow satisfies the full target-shift square.

Source: Stacks 070I, 070Y and 09L9; Step 6 of
lem-sf-derived-functor-mapping-complex-action.
(blueprint: lem-sf-derived-mapping-representative-shift-cohomology).

Proof: precompose by the invertible source comparison on I,J[n], followed by the
source Hom image of the localization shift comparison Q(J[n]) to (QJ)[n]. Naturality
of the arrow moves this latter map across the arrow. Normalize the resulting arrow
on I,J[n]; the new middle factors are the representative comparisons at I and J[n].
The inverse representative comparison at J[n] is its universal unit. The proved full
unit shift equation replaces this unit followed by RF's two shift comparisons with
the termwise F shift comparison, the localization shift comparison on FJ, and the
shift of the unit at J. Move the termwise F shift comparison through T's ordinary
comparison by naturality. Apply T's shift normalization to its ordinary comparison
on FI,(FJ)[n], and then use T's isomorphism shift coherence for the comparisons at
I and J. The proved ordinary signed target-shift square interchanges the ordinary
F action with the ordinary shifts. Naturality of the localization shift comparison
moves the ordinary F map to the shifted factor. Normalize the remaining arrow on
I,J. Finally S's shift normalization identifies the entire source prefix with the
precomposing comparison followed by S's derived shift. Cancel the invertible prefix.
All comparisons used here exist even when FI and FJ are not K-injective. -/
theorem Step.MappingArrow.representative_target_shift (a : e.MappingArrow S T)
    (hT : T.IsoCoherent) (h : e.HasCanonicalShift)
    (I J : CochainComplex A ℤ) [I.IsKInjective] [J.IsKInjective] (n : ℤ) :
      a.transformation.app (op (DerivedCategory.Q.obj I), (DerivedCategory.Q.obj J)⟦n⟧) ≫
        T.hom.map (X := (op (e.derived.obj (DerivedCategory.Q.obj I)),
          e.derived.obj ((DerivedCategory.Q.obj J)⟦n⟧)))
          (Y := (op (e.derived.obj (DerivedCategory.Q.obj I)),
            (e.derived.obj (DerivedCategory.Q.obj J))⟦n⟧))
          (𝟙 _, (e.derived.commShiftIso n).hom.app (DerivedCategory.Q.obj J)) ≫
        (T.shift (e.derived.obj (DerivedCategory.Q.obj I))
          (e.derived.obj (DerivedCategory.Q.obj J)) n).hom =
      (S.shift (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj J) n).hom ≫
        (a.transformation.app (op (DerivedCategory.Q.obj I), DerivedCategory.Q.obj J))⟦n⟧' := by
  sorry

end CategoryTheory.DerivedMappingAction
