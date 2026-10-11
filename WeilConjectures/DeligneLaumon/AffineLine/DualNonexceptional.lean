/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.DenseOpen
public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension
public import WeilConjectures.WeilSheaf.DualIrreducible

/-!
# Nonexceptionality of the dual

The geometric irreducible constituents of the dual `M^∨` of a lisse sheaf `M` are the duals of
those of `M`, and the dual of the linear Artin–Schreier sheaf `ℒ_{ψ⁻¹(a x)}` is `ℒ_{ψ(a x)}`.
Hence if `M` is nonexceptional for `ψ`, then `M^∨` is nonexceptional for `ψ⁻¹`.
(blueprint: `lem-fd-constituent-nonexceptional-concentration`, part (2))

## Main statements

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isNonexceptional_dual`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- If the lisse sheaf `M` of `D` is nonexceptional for `ψ`, its dual `M^∨` is nonexceptional
for `ψ⁻¹`: a geometric constituent `ℒ_{ψ⁻¹(a x)}|_U` of `M^∨` would dualise to the geometric
constituent `ℒ_{ψ(a x)}|_U` of `M`. (blueprint: `lem-fd-constituent-nonexceptional-concentration`,
part (2)) -/
theorem isNonexceptional_dual (D : LisseOnDenseOpen k₀ l) {ψ : AddChar k₀ (PadicAlgCl l)}
    (h : D.sheaf.IsNonexceptional ψ D.j) : (D.sheaf.dual D.lisse).IsNonexceptional ψ⁻¹ D.j :=
  sorry

end AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen
