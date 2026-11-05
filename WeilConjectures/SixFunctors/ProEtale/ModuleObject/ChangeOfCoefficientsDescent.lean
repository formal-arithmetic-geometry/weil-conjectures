/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.KernelDescent

/-!
# Descending a locally free module along a change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, `S` a scheme and `L` a module
object over `Λ'_S`. Suppose given a finite pro-étale cover `{f_k : V_k ⟶ S}` and, on each `V_k`,
a free sub-`Λ_{V_k}`-module `σ_k : Λ_{V_k}^{n_k} ⟶ f_k^* Res L`, presented as the kernel of some
`π_k`, such that the `π_k` agree on the fibre products `V_j ×_S V_k` and the adjoints
`Λ'_{V_k} ⊗ Λ_{V_k}^{n_k} ⟶ f_k^* L` of the `σ_k` are isomorphisms. Then the kernel `L'` of the
`π_k` (`ProEtale.CondensedRing.kernelDescentMap`) is a locally free `Λ_S`-module with
`Λ'_S ⊗_{Λ_S} L' ≅ L` (`ProEtale.CondensedRing.exists_isLocallyFree_extendScalars_iso_of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

end AlgebraicGeometry.ProEtale.CondensedRing
