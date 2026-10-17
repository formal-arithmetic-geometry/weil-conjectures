/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit

/-!
# Torsion cohomological dimension through finitely generated subalgebras

An `L`-algebra `S` is the filtered union of its finitely generated `L`-subalgebras `A`, so that
`Spec S` is the limit of the affine schemes `Spec A`, with affine transition maps. A uniform bound
`cd_tor(Spec A) ≤ n` therefore passes to `Spec S`
(`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.spec_of_forall_fg`), by
`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- If `cd_tor(Spec A) ≤ n` for every finitely generated `L`-subalgebra `A` of an `L`-algebra
`S`, then `cd_tor(Spec S) ≤ n`: `Spec S` is the limit of the `Spec A`. -/
theorem HasTorsionCohomologicalDimensionLE.spec_of_forall_fg {L : Type u} [CommRing L]
    (S : Type u) [CommRing S] [Algebra L S] {n : ℕ}
    (h : ∀ A : Subalgebra L S, A.FG → (Spec (.of A)).HasTorsionCohomologicalDimensionLE n) :
    (Spec (.of S)).HasTorsionCohomologicalDimensionLE n :=
  sorry

end AlgebraicGeometry.Scheme
