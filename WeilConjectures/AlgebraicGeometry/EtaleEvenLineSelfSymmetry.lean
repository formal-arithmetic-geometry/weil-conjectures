/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleLineFlatBraiding

/-! # Self symmetry of an even shifted etale line
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CoordinateTrace

variable (A : Type (u + 1)) [CommRing A]

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
/-- An even shifted rank-one line has identity self symmetry.
(Stacks, Tag 06YU). -/
theorem evenLineSelfSymmetry {Y : Scheme.{u}}
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (d : ℤ) :
    (swap A Y (shiftedLine A J d) (shiftedLine A J d)).hom = 𝟙 _ := by
  obtain ⟨hflat, hswap⟩ := etaleLineFlatAndBraiding A J hJ
  dsimp only [swap, Iso.app_hom, derivedTensorSymmetry, shiftedLine, tensor, derivedTensor]
  exact evenShiftCanonicalSelfSymmetry J hflat hswap d

end AlgebraicGeometry.Etale.CoordinateTrace
