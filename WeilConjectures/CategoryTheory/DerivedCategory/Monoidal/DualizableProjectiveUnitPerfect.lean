/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingle

/-!
# Dualizable objects of `D(C)` are bounded complexes of finite projective objects

Let `C` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, whose unit `𝟙` is projective, with morphisms from `𝟙` finite on coproducts and on
tensor products (`CategoryTheory.UnitFactorsThroughFiniteCoproducts`,
`CategoryTheory.UnitTensorFinite`). We prove that every dualizable object `K` of `D(C)` is
isomorphic to a bounded complex of finite projective objects, that is, of retracts of finite
direct sums `𝟙ʳ` (`DerivedCategory.exists_iso_Q_obj_of_isDualizable`).

## Strategy

By `DerivedCategory.exists_retract_of_exactPairing_of_projective_unit`, a dualizable `K` is a
retract of a bounded complex whose terms are quotients of some `𝟙ʳ`. Hence `K` is bounded, its
top homology is a quotient of some `𝟙ʳ`, and, its dual being bounded as well, `K` has finite Tor
amplitude. We argue by induction on the length of the interval `[a, b]`, where `K` vanishes above
`b` and `K ⊗ G[0]` vanishes below `a` for every `G : C`.

* If `a = b`, then `K = H[-a]`, where `H` is a quotient of `𝟙ʳ` such that `H[0]` is dualizable of
  Tor amplitude `[0, 0]`. Its dual `X` then vanishes above `0`, so `Hom(H[0], G[1])`, which is
  `Hom(𝟙, G[1] ⊗ X)`, vanishes; the surjection `𝟙ʳ ⟶ H` splits, and `H` is finite projective.
* If `a < b`, a map `𝟙ʳ[-b] ⟶ K` which is surjective on `Hᵇ` has a dualizable cone `C'` vanishing
  above `b - 1` with the same lower Tor bound `a`. By induction `C'` is a bounded complex of
  finite projective objects, and so is `K`, an extension of `C'` by `𝟙ʳ[-b]`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

open Pretriangulated

section FinProjComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [HasDerivedCategory.{w} C]

attribute [local instance] Abelian.hasFiniteBiproducts

end FinProjComplex

section Dualizable

open MonoidalClosed

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

attribute [local instance] Abelian.hasFiniteBiproducts

end Dualizable

end DerivedCategory
