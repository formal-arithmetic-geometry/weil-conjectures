/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite

/-!
# Comparison with Mathlib's quasi-finite morphisms

The quasi-finiteness predicates of Stacks Tag 01TD include local finite type, which Mathlib's
`LocallyQuasiFinite` and `Scheme.Hom.QuasiFiniteAt` do not. We show that they agree with
Mathlib's notions once the finite-type conditions are added.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isQuasiFiniteAtPoint_iff_quasiFiniteAt`: for `f` locally of
  finite type, `IsQuasiFiniteAtPoint f x ↔ f.QuasiFiniteAt x`.
- `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_iff`:
  `IsLocallyQuasiFinite f ↔ LocallyQuasiFinite f ∧ LocallyOfFiniteType f`.
- `AlgebraicGeometry.Scheme.Hom.isQuasiFinite_iff`:
  `IsQuasiFinite f ↔ LocallyQuasiFinite f ∧ LocallyOfFiniteType f ∧ QuasiCompact f`.

Source: Stacks Project, Morphisms of Schemes, Tags 01TD, 01TF and 01TJ
(blueprint: pqf-def-quasifinite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

end AlgebraicGeometry.Scheme.Hom
