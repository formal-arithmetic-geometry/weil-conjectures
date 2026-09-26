/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The spectrum of an algebraic closure as a scheme over the base field

`Spec K̄`, viewed as an object of `Over (Spec (.of K))`. Morphisms from it to a `K`-scheme `X`
are the geometric points of `X`.

## Main definitions

- `AlgebraicGeometry.Scheme.specAlgebraicClosure`: `Spec K̄` as a scheme over `K`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- `Spec K̄`, the spectrum of an algebraic closure of `K`, as a scheme over `K`. Its morphisms
to a `K`-scheme are the geometric points of that scheme. -/
noncomputable def Scheme.specAlgebraicClosure (K : Type u) [Field K] : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))

end AlgebraicGeometry
