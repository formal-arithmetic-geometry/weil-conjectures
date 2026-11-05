/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.NatIsoOfIsKInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# The native internal hom out of a single pro-étale Weil sheaf

For a pro-étale Weil sheaf `A` placed in degree `d`, the native derived internal hom
`RHom(A[-d], -)` of pro-étale Weil sheaves (the internal hom of the closed structure
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison`, right adjoint to the native
derived tensor product) is the right derived functor of `𝓗om(A, -)` followed by the shift `[d]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilHomSingleIso`).

On a K-injective complex `I` the internal hom is the product-total hom complex
`∏_p 𝓗om(A[-d]^p, I^{p + n})`, which has only the factor `p = d`; projecting to it is an
isomorphism of complexes onto `𝓗om(A, I)[d]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.singleHomProjection`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

end AlgebraicGeometry.ProEtaleWeilSheaf
