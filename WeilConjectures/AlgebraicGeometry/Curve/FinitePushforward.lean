/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

/-!
# The eight curve assertions pass to finite direct images

Let `k` be an algebraically closed field, `ν : X ⟶ Y` a finite morphism of curves over `k` and
`F` a torsion étale sheaf on `X`. If the eight curve assertions `C(X, F)` hold, then so do
`C(Y, ν_* F)`: the edge maps `Hᵠ(Y, ν_* F) ⟶ Hᵠ(X, F)` are isomorphisms compatible with
pullbacks along field extensions and open immersions.

## Main statements

- `AlgebraicGeometry.IsCurve.Assertions.lowerStar_of_isFinite`.

## References

- Stacks Project, Lemma 0A5D, <https://stacks.math.columbia.edu/tag/0A5D>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The eight curve assertions pass to finite direct images.** Let `k` be algebraically
closed, `f : X ⟶ Spec k` and `g : Y ⟶ Spec k` curves and `ν : X ⟶ Y` a finite `k`-morphism.
If the eight assertions `C(X, F)` hold for an étale sheaf `F` of `Λ`-modules on `X`, then the
eight assertions `C(Y, ν_* F)` hold.
(blueprint: `lem-weil-pbc-curve-assertions-finite-pushforward`) -/
@[stacks 0A5D]
theorem IsCurve.Assertions.lowerStar_of_isFinite {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] (g : Y ⟶ Spec (.of k)) [IsCurve g]
    (ν : X ⟶ Y) [IsFinite ν] (hν : ν ≫ g = f)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h : IsCurve.Assertions Λ f F) :
    IsCurve.Assertions Λ g ((ν)_*[ModuleCat.{u + 1} Λ].obj F) :=
  sorry

end AlgebraicGeometry
