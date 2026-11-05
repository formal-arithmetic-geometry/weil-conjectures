/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.MonoidalUnitSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.WContractibleDisjointCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# The unit of pro-étale sheaves of modules over a w-contractible affine scheme

Let `R` be a w-contractible ring and `Λ` a commutative ring. On the small pro-étale site of
`Spec R`, the terminal object has finite disjoint refinements
(`AlgebraicGeometry.Scheme.ProEt.hasFiniteDisjointRefinements_of_iso`), so the unit `Λ` of the
category of pro-étale sheaves of `Λ`-modules is projective, and morphisms out of it to
coproducts and tensor products are finite (`CategoryTheory.Sheaf.projective_unit`,
`CategoryTheory.Sheaf.unitFactorsThroughFiniteCoproducts`,
`CategoryTheory.Sheaf.unitTensorFinite`): global sections behave like modules over a ring.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] (R : CommRingCat.{u}) [IsWContractibleRing R]

end AlgebraicGeometry.ProEtale
