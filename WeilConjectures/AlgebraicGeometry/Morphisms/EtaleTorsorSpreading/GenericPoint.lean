/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Datum

/-!
# Étaleness of the normalization over the generic point

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`)
over a Noetherian base, the relative normalization of `C` in the Galois cover is étale in a
neighbourhood of every point lying over the generic point of `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois`: over a Noetherian
base, the normalization `N ⟶ C` of `C` in `Z.P` is étale in a neighbourhood of every point lying
over the generic point `η` of `S`.

Proof sketch: work over affine opens `Spec A ⊆ S`, `Spec B ⊆ c⁻¹(Spec A)`, so that
`Z.P ∩ = Spec D` with `D` finite étale over `B_K = B ⊗_A K`, `K = Frac A`. As
`B_K = colim_{a ≠ 0} B_a`, the finite étale algebra `D` descends to a finite étale
`B_a`-algebra `D_a` for some `a ≠ 0` ([Stacks 01ZM] and [Stacks 07RP], or
`Algebra.FinitePresentation` + `Algebra.Etale` descent through filtered colimits). `B` is a normal
ring (smooth over the normal `A`: the integral closure of `B` in `B_K` is `B` by
`TensorProduct.toIntegralClosure_bijective_of_smooth`), hence so is `D_a` (étale over `B_a`), so
`D_a` is integrally closed in its localization `D` and equals the integral closure of `B_a` in
`D`. Thus over `c⁻¹(D(a)) ∩ Spec B` the normalization is `Spec D_a`, which is étale. -/
theorem etaleOver_genericPoint [IsNoetherian D.S] : D.EtaleOver (genericPoint D.S) :=
  sorry

end AlgebraicGeometry.Scheme.SpreadingDatum
