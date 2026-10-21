/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.SemistableMultipointedPair
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Semistability at a point of a marked curve

Source: Temkin, *Stable modification of relative curves*, §1.2 and Lemma 4.4.2
(blueprint: def-trf-semistable-marked-point).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.MultipointedPair

/-- Restrict a pair to an open of its curve, pulling back its marking in the category over
its base. Source: Temkin §1.2 and the localization in Lemma 4.4.2
(blueprint: def-trf-semistable-marked-point). -/
def restrictCurve {T : Scheme.{u}} (P : MultipointedPair T) (U : P.curve.left.Opens) :
    MultipointedPair T where
  curve := Over.mk (U.ι ≫ P.curve.hom)
  marking := pullback P.inclusion
    (Over.homMk U.ι rfl : Over.mk (U.ι ≫ P.curve.hom) ⟶ P.curve)
  inclusion := pullback.snd P.inclusion
    (Over.homMk U.ι rfl : Over.mk (U.ι ≫ P.curve.hom) ⟶ P.curve)

/-- A pair is semistable at a point when its restriction to some open neighbourhood is
semistable, including the pulled-back marking. Source: Temkin §1.2 and Lemma 4.4.2
(blueprint: def-trf-semistable-marked-point). -/
def IsSemistableAt {T : Scheme.{u}} (P : MultipointedPair T) (x : P.curve.left) : Prop :=
  ∃ U : P.curve.left.Opens, x ∈ U ∧ (P.restrictCurve U).IsSemistable

end AlgebraicGeometry.MultipointedPair
