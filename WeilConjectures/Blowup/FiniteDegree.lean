/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.FiniteDegree.Algebra
public import WeilConjectures.Blowup.FiniteDegree.ChartIdeal
public import WeilConjectures.Blowup.FiniteDegree.ChartProbe
public import WeilConjectures.Blowup.FiniteDegree.Generation
public import WeilConjectures.Blowup.FiniteDegree.LocalAlgebra
public import WeilConjectures.Blowup.FiniteDegree.Main
public import WeilConjectures.Blowup.FiniteDegree.UniformNumerator
public import WeilConjectures.Blowup.Proper
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!

# Finite-degree approximation on the blow-up

This module only re-exports its parts, which live in `WeilConjectures.Blowup.FiniteDegree`.

It proves the finite-degree approximation of a finite-type center on a blow-up:
for finite-type centers `I` on a qcqs scheme `X` and `J` on the blow-up of `I`, there
are `d ≥ 1` and a finite-type `L ≤ I^d` whose inverse image ideal on the blow-up is
`I_E^d · J` (`Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup`).

## Implementation details

The chart rings of the blow-up are large `HomogeneousLocalization` types, so all `Finset`
bookkeeping over generating sets is done by the abstract combinators
`exists_uniform_ge₂`/`exists_finset_forall_mem` over variable types, chart probes keep their
ring abstract (`Scheme.IdealSheafData.ideal_comap_comap_of_probe`), and memberships are
transported along morphism equalities by `mem_of_ringHom_eq` instead of `▸`-rewrites.

## References

* Stacks Project, Tag 0803
* Stacks Project, Tag 01PF (finite-type extension)
-/
