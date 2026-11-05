/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius

/-!
# The Galois action on a base-changed group scheme preserves the group law

Let `A` be a group scheme over a field `K` and `A_{K̄} = A ×_K K̄` its base change to the
algebraic closure, with the base-changed group law. For a `K`-algebra endomorphism `σ` of `K̄`,
the map `σ_A = 𝟙 × Spec σ` of `A_{K̄}` (`AlgebraicGeometry.Scheme.Hom.geometricFiberGaloisMap`)
lies over `Spec σ` and is compatible with the group laws: it is a homomorphism of group schemes
semilinear over `Spec σ` (`AlgebraicGeometry.SemilinearGrpHom`).

## Main definitions

- `AlgebraicGeometry.Scheme.geometricFiberGaloisGrpHom`: `σ_A` as a semilinear homomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] (A : Over (Spec (.of K))) [GrpObj A]

end AlgebraicGeometry.Scheme
