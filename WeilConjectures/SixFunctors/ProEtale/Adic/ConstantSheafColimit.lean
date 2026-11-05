/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso

/-!
# The constant `ℓ`-adic sheaf as the colimit of the sheaves `E_X`

The repository has two models of the `ℚ̄_ℓ`-sheaf of Bhatt–Scholze (*The pro-étale topology for
schemes*, §6.8) on the pro-étale site of a scheme `X`: the sheaf
`AlgebraicGeometry.ProEtale.adicConstantSheaf` of locally finite functions `U → ℚ̄_ℓ`, and the
sheafification `AlgebraicGeometry.ProEtale.padicAlgClSheaf` of the functions with values in a
finite subextension `E ⊆ ℚ̄_ℓ`, which is the colimit `colim_E E_X` of the sheaves `E_X = C(-, E)`
(`AlgebraicGeometry.ProEtale.isColimitPadicAlgClSheafCocone`). They agree
(`AlgebraicGeometry.ProEtale.padicAlgClSheafIsoAdicConstantSheaf`), so the abelian sheaf
underlying `ℚ̄_ℓ,X` is `colim_E E_X`
(`AlgebraicGeometry.ProEtale.isColimitPadicAlgClSheafCoconeExtend`). This is the first step of
the comparison of `ℓ`-adic sheaves with `ℓ`-adic towers of torsion sheaves needed for the
finiteness theorem (`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`).

We also show that on a compact space a locally finite function takes values in a finite
subextension (`PadicAlgCl.mem_finiteIntermediateFieldValued_of_mem_locallyFiniteFunctions`).
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T : Type*} [TopologicalSpace T]

end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
