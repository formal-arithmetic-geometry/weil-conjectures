/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.Blowup.Gluing

/-! # The normalized blowup

The construction is separated from its calculus so that the mapping property can be
used in the calculus without an import cycle. Source: ILO, Expose VIII, 2.2.3
(blueprint: def-trf-normalized-blowup).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The normalized blowup is the componentwise normalization of the ordinary blowup.
Source: ILO, Expose VIII, 2.2.3 (blueprint: lem-trf-normalized-blowup-calculus). -/
noncomputable def normalizedBlowup {S : Scheme.{u}} (J : S.IdealSheafData) : Scheme.{u} :=
  J.blowup.reducedNormalization

/-- The normalized blowup's structural map is the normalization map followed by the blowup
map. Source: ILO, Expose VIII, 2.2.3 (blueprint: lem-trf-normalized-blowup-calculus). -/
noncomputable def normalizedBlowupMap {S : Scheme.{u}} (J : S.IdealSheafData) :
    J.normalizedBlowup ⟶ S :=
  J.blowup.fromReducedNormalization ≫ J.blowupMap

end AlgebraicGeometry.Scheme.IdealSheafData
