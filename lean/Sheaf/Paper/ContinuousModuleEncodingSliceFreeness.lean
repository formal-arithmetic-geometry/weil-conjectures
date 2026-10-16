/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
import Sheaf.Paper.ContinuousModuleEncodingRestriction
import all Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality

/-! # Finite freeness on pro-etale slices
Source: Stacks Project, Tags 03DM and 03DO.
(blueprint: lem-weil-pbc-continuous-module-encoding-slice-freeness)
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Finite freeness on the localized site is detected by raw internal inverse image.
Source: Stacks Project, Tags 03DM and 03DO.
(blueprint: lem-weil-pbc-continuous-module-encoding-slice-freeness)

Proof. The equivalence of the pro-etale slice with the source site induces an
equivalence of module sheaves, preserving the unit and finite free modules.
The continuous-chart restriction comparison identifies its value on the
restricted encoding with the encoding of canonical inverse image. The latter
is finite free exactly when raw inverse image is finite free, since the
canonical coefficient comparison is invertible. -/
theorem continuousRing_slice_free_iff
    (X : Scheme.{u}) (T : Type)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))
    (W : X.ProEt) :
    (∃ n : ℕ, Nonempty (((continuousRingModuleEquivalence X T).functor.obj P).over W ≅
      SheafOfModules.free (ULift.{u + 1} (Fin n)))) ↔
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} W.hom).obj
      (condensedRingObj (Profinite.continuousMapRingObj T) X))
      (((ProEtale.upperStar Ab.{u + 1} W.hom).mapMod _).obj P) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
