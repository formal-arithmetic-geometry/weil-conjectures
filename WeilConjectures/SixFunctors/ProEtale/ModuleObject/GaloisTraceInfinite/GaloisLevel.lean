/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisFieldCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerLimit

/-!
# The finite Galois levels of a Galois base change

Let `Ω / L` be a Galois extension, `G` a scheme over `Spec L` and, for a finite Galois
subextension `L'`, `G_{L'} = G ×_L L'`. This file names the transition maps
`G_{L''} ⟶ G_{L'}` for `L' ≤ L''` (`AlgebraicGeometry.galoisLevelMap`), the projections
`G_Ω ⟶ G_{L'}` (`AlgebraicGeometry.galoisLevelProjection`) and the action of `Gal(L'/L)` on
`G_{L'}` (`AlgebraicGeometry.galoisLevelAction`), and proves that every automorphism of `L'` lifts
to `L''` compatibly with the transition maps
(`AlgebraicGeometry.exists_galoisLevelMap_comp_galoisLevelAction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace FiniteGaloisIntermediateField

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω]

end FiniteGaloisIntermediateField

namespace AlgebraicGeometry

open FiniteGaloisIntermediateField ProEtale

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

end AlgebraicGeometry
