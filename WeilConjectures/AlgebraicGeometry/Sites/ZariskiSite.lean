/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Topology.Sheaves.GrothendieckVanishing

/-!
# The small Zariski site of a scheme and Grothendieck vanishing

The small Zariski site `X_Zar` of a scheme `X` is the category `X.Opens` of open subsets of `X`
with jointly surjective families of open immersions as coverings
(`AlgebraicGeometry.Scheme.smallZariskiTopology`, blueprint `def-sc-zariski-site`); its sheaves
are the sheaves on the underlying topological space. The cohomology `Hᵠ(X_Zar, F)` of an
abelian sheaf `F` is `AlgebraicGeometry.Scheme.zariskiH` (blueprint
`def-sc-zariski-cohomology`), Mathlib's `CategoryTheory.Sheaf.H`, the `Ext` group
`Extᵠ(ℤ, F)`, i.e. the `q`-th right derived functor of `F ↦ F(X)`.

* Blueprint `def-sc-zariski-flasque` (flasque sheaves) is Mathlib's `TopCat.Sheaf.IsFlasque`.
* Blueprint `lem-sc-zariski-flasque-acyclic` (flasque sheaves are acyclic) is
  `TopCat.Sheaf.IsFlasque.subsingleton_H`.
* Blueprint `lem-sc-zariski-filtered-cohomology` (cohomology commutes with filtered colimits on
  a noetherian space) is `TopCat.Sheaf.preservesColimitsOfShape_functorH`.
* Blueprint `lem-sc-zariski-dimension-bound` (Grothendieck vanishing) is
  `TopCat.Sheaf.subsingleton_H_of_topologicalKrullDim_lt`, and
  `AlgebraicGeometry.Scheme.subsingleton_zariskiH_of_topologicalKrullDim_lt` for schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
