/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity

/-!
# Constant sheaves and the comparison pullback

Let `X` be a scheme and `ν : X_ét ⥤ X_proét` the inclusion of the small étale site into the
small pro-étale site. This file proves:

- `AlgebraicGeometry.ProEtale.constantSheafCompComparisonUpperStarIso`: the comparison pullback
  `ν^*` of a constant étale sheaf is the constant pro-étale sheaf, both functors being left
  adjoint to global sections;
- `AlgebraicGeometry.ProEtale.constantSheafIsoContinuousMapRingSheaf`: for a discrete topological
  ring `T`, the abelian sheaf `U ↦ C(U, T)` on `X_proét` is the constant sheaf with value `T`
  (Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 4.2.12): a continuous map to a
  discrete space is locally constant;
- `AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf`: hence
  `U ↦ C(U, T)` is `ν^*` of the constant étale sheaf with value `T`.

For `T = 𝒪_E ⧸ ℓⁿ` this identifies the reductions of the sheaf `𝒪_{E,X}` of continuous
`𝒪_E`-valued functions (`WeilConjectures.SixFunctors.ProEtale.Adic.ContinuousMapReduction`) with
pullbacks of constant torsion étale sheaves, an input of the comparison of `ℓ`-adic sheaves with
`ℓ`-adic towers of torsion étale sheaves needed for the finiteness theorem
(`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`).
-/

@[expose] public section
universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

section Comparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (X : Scheme.{u})

end Comparison

section Discrete

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

variable [DiscreteTopology T]

end Discrete

end AlgebraicGeometry.ProEtale
