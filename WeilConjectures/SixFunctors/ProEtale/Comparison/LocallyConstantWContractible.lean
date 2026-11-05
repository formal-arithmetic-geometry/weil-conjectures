/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Comparison pullbacks of locally constant sheaves on w-contractible objects

Let `F` be an étale sheaf on `S` trivialised by a jointly surjective family of étale morphisms
`uᵢ : Uᵢ ⟶ S`, that is `uᵢ^* F` is constant.

- `AlgebraicGeometry.ProEtale.isConstant_upperStar_comparisonUpperStar_obj`: for any `z : Z ⟶ S`
  factoring through some `uᵢ`, `z^* ν^* F` is a constant pro-étale sheaf.
- `AlgebraicGeometry.ProEtale.exists_disjoint_opens_isConstant_comparisonUpperStar`: an object
  `W` of `S_proét` whose underlying scheme is the spectrum of a w-contractible ring is covered by
  pairwise disjoint open subschemes on each of which `ν^* F` is constant, since the pulled-back
  étale cover of `W` has a section.

For a tower `(Lₙ)` of finite locally constant sheaves trivialised by one common étale family,
the same disjoint cover of `W` trivialises all the `ν^* Lₙ` at once; since such `W` cover
`S_proét` (`AlgebraicGeometry.Scheme.ProEt.exists_isWContractibleRing_cover`), this is the
first step towards describing `lim ν^* Lₙ` locally as `C(-, lim Mₙ)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

end AlgebraicGeometry.ProEtale
