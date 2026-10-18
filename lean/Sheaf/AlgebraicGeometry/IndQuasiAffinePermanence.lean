/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Sheaf.AlgebraicGeometry.QuasiAffineBaseChange
import Sheaf.AlgebraicGeometry.QuasiAffineTargetLocality

/-!
# Permanence and separation for ind-quasi-affine morphisms

Source: Stacks Project, More on Morphisms, Tags 0AP6, 0F1U and 0AP7
(blueprint: lem-a1-ind-quasi-affine-permanence).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The condition that every quasi-compact open over an affine target open is quasi-affine.

Source: Stacks Project, More on Morphisms, Tags 0AP6 and 0F1U
(blueprint: lem-a1-ind-quasi-affine-permanence).
-/
def indQuasiAffineProperty {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (U : Y.Opens), IsAffineOpen U →
    ∀ (K : (Limits.pullback f U.ι).Opens),
      IsCompact (K : Set (Limits.pullback (C := Scheme.{u}) f U.ι)) →
        IsQuasiAffineHom (K.ι ≫ Limits.pullback.snd f U.ι)

/-- Ind-quasi-affineness is stable under arbitrary base change, local on an affine open
cover of the target, and implies quasi-affineness of quasi-compact opens and separatedness
when the target is affine.

Source: Stacks Project, More on Morphisms, Tags 0AP6, 0F1U and 0AP7
(blueprint: lem-a1-ind-quasi-affine-permanence).

Proof:
1. Translate between quasi-affine morphisms to affine schemes and quasi-affine source schemes,
   using the recorded quasi-affine morphism definition and affine-scheme compactness.
2. For an affine open cover of the target, restrict a quasi-compact open to affine members of
   the cover and apply the affine-cover criterion for ordinary quasi-affineness.
3. For an arbitrary base change, cover the base by affine opens, enlarge each projected
   quasi-compact open to a finite union of affine opens, and apply ordinary quasi-affine
   base-change stability.
4. Over an affine target, quasi-compact opens are quasi-affine; unions of affine opens are
   quasi-affine and separated, and the absolute diagonal is checked on the resulting target
   cover. Separatedness implies quasi-separatedness.
-/
theorem indQuasiAffineProperty_permanence {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ (T : Scheme.{u}) (g : T ⟶ Y),
      indQuasiAffineProperty f → indQuasiAffineProperty (Limits.pullback.snd f g)) ∧
    (∀ {I : Type v} (U : I → Y.Opens), (∀ i, IsAffineOpen (U i)) →
      iSup U = ⊤ →
      (indQuasiAffineProperty f ↔
        ∀ i, indQuasiAffineProperty (Limits.pullback.snd f (U i).ι))) ∧
    (∀ (_hY : IsAffine Y), indQuasiAffineProperty f →
      (∀ (K : X.Opens), IsCompact (K : Set X) → K.toScheme.IsQuasiAffine) ∧
        Scheme.IsSeparated X ∧ QuasiSeparatedSpace X) := by
  sorry

end AlgebraicGeometry
