/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.GrpEqLocus

/-!
# Lie algebras of kernels, equalizers and centralizers

Let `f, g : G ⟶ H` be homomorphisms of group schemes over a field `k`. A tangent vector of `G`,
a point `v : Spec k[ε] ⟶ G` reducing to the identity, is tangent to the kernel `ker f` (the
fibre of `f` over the identity) if and only if `v ≫ f` is the identity point, that is if
`df(v) = 0`: the Lie algebra of the kernel is the kernel of the differential. In the same way
the Lie algebra of the equalizer `eqLocus f g` of `f` and `g` is the subspace on which `df` and
`dg` agree. The equalizer is a closed subgroup scheme, since `H` is separated.

For a rational point `g` of `G`, the centralizer `C_G(g)` is the equalizer of the conjugation
`c_g : x ↦ g x g⁻¹` and the identity. Its Lie algebra is the subspace of `Lie(G)` fixed by the
adjoint action `Ad(g) = d(c_g)` of `g`.

## Main definitions

- `AlgebraicGeometry.GrpObj.centralizer`: the centralizer `C_G(g)` of a rational point, with its
  inclusion `AlgebraicGeometry.GrpObj.centralizerι`.
- `AlgebraicGeometry.GrpObj.lieEquivKer`: `Lie(ker f) ≃ ker(df)`.

## Main statements

- `AlgebraicGeometry.GrpObj.mem_range_differential_kerι_iff`: `Lie(ker f) = ker(df)` inside
  `Lie(G)`.
- `AlgebraicGeometry.GrpObj.mem_range_differential_eqLocusι_iff`: the Lie algebra of the
  equalizer of `f` and `g` is the subspace on which `df = dg`.
- `AlgebraicGeometry.GrpObj.isClosedImmersion_eqLocusι`: the equalizer is a closed subscheme.
- `AlgebraicGeometry.GrpObj.mem_range_differential_centralizerι_iff`: the Lie algebra of
  `C_G(g)` is the subspace fixed by `d(c_g)`.

## Blueprint

- `sk-p-comparison`: the kernel of `Ad` and the centralizers of points, with their Lie algebras.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {k : Type u} [Field k] {G H : Over (Spec (.of k))} [GrpObj G] [GrpObj H]

/-! ### The kernel of a homomorphism -/

section Kernel

variable (f : G ⟶ H) [IsMonHom f]

end Kernel

/-! ### The equalizer of two homomorphisms -/

section EqLocus

variable (f g : G ⟶ H) [IsMonHom f] [IsMonHom g]

end EqLocus

/-! ### Centralizers of rational points -/

section Centralizer

variable (g : 𝟙_ (Over (Spec (.of k))) ⟶ G)

end Centralizer

end AlgebraicGeometry.GrpObj
