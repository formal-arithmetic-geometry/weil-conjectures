/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Sheaf.AlgebraicGeometry.ToricMonoidComparison
public import Sheaf.AlgebraicGeometry.NormalizedTowerDescentData
public import Mathlib.Algebra.Field.ULift
public import Sheaf.AlgebraicGeometry.CenteredToricTowerLiftData

import Sheaf.AlgebraicGeometry.CenteredToricTowerLiftExistence
import Sheaf.AlgebraicGeometry.CenteredToricTowerLiftUniqueness

/-!
# Centerwise descent of an equivariant normalized toric tower

Source: ILO, Travaux de Gabber, Exposé VIII, 3.2.19 and Theorem 3.2.20,
p.106, using 3.2.12(ii), 3.2.15 and 3.2.18
(blueprint: lem-trf-monoscheme-toric-tower-descent).

Uniqueness is an isomorphism of centered monoscheme towers inducing the specified
realization identifications. It is not equality of presentations of sheafed spaces.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Monoscheme

/-- A finite equivariant normalized tower descends uniquely with its ordered centers
and canonical chart identifications; regularity of the final scheme gives smoothness
of the final monoscheme. The base is specified and no stage is contracted.

Source: ILO VIII 3.2.19--3.2.20, p.106
(blueprint: lem-trf-monoscheme-toric-tower-descent).

Proof:
1. Induct on the tower length, initially taking M itself with the specified base
identification. At length zero there are no ideals or blowups to choose.
2. At stage i, use lem-trf-toric-monoid-comparison (i) to recover the unique coherent
monoid ideal from the equivariant ring ideal under the current identification.
By lem-trf-monoscheme-finite-chart-components, each realization component is nonempty,
clopen and integral. An empty ideal on a component would give a zero ring ideal there,
so its zero scheme would contain a nonempty open component, violating nowhere density.
3. Take the saturated monoscheme blowup. Part (ii) of the comparison identifies its
realization canonically with the specified next normalized blowup, preserving the
original torus and the ordered center. Its charts are fine and torsion free and give
a finite affine cover. The equivariant comparison transports the next torus action.
Repeat without contracting any stage.
4. Compare two lifts inductively from their fixed base. Injectivity of the ideal
comparison identifies the centers. The saturated blowup chart identifications then
give the unique isomorphism of the next monoschemes over the preceding one, inducing
the specified realization identifications. The monomial formulas agree on localized
overlaps, so these centered identifications glue uniquely at every stage.
5. If the final scheme is regular, transport this property by its realization
identification. The rational regularity assertion of lem-trf-toric-monoid-comparison
(iii), namely ILO VIII 3.2.12(ii), gives stalks N^r times Z^t, which is precisely
`Fine.IsSmooth`. This argument also applies when the tower has length zero. -/
theorem exists_unique_centeredToricTowerLift (M : Fine.{u}) (hM : M.IsTorsionFree)
    (n : ℕ) (T : NormalizedTower.{u} n)
    (e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M)
    (hEquivariant : T.HasEquivariantToricCenters M e₀)
    (hNowhereDense : T.HasNowhereDenseCenters) :
    ∃ L : CenteredToricTowerLift M T e₀,
      (∀ L' : CenteredToricTowerLift M T e₀,
        ∃! e : ∀ i : Fin (n + 1), (L.tower.level i).space ≅ (L'.tower.level i).space,
          L.IsCenteredIdentification L' e) ∧
      (IsRegularScheme (T.level (Fin.last n)) → (L.tower.level (Fin.last n)).IsSmooth) := by
  obtain ⟨L⟩ := exists_centeredToricTowerLift M hM n T e₀ hEquivariant hNowhereDense
  refine ⟨L, fun L' ↦ existsUnique_centeredToricTowerIdentification L L', ?_⟩
  intro hRegular
  have : IsLocallyNoetherian (T.level (Fin.last n)) := hRegular.1
  have : IsRegular (T.level (Fin.last n)) := hRegular.2
  have hRealization :
      IsRegularScheme (realization (ULift.{u} ℚ) (L.tower.level (Fin.last n))) := by
    refine ⟨isLocallyNoetherian_of_isOpenImmersion (L.iso (Fin.last n)).hom, ⟨?_⟩⟩
    intro x
    exact IsRegularLocalRing.of_ringEquiv
      (asIso ((L.iso (Fin.last n)).hom.stalkMap x)).commRingCatIsoToRingEquiv
  exact isSmooth_of_rational_realization_regular _ (L.torsionFree _) hRealization

end AlgebraicGeometry.Monoscheme
