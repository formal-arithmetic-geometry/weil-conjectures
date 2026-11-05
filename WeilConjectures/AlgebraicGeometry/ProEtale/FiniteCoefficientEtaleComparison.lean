/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientCohomology
public import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluationAll

/-!
# Pro-étale and étale cohomology with finite discrete coefficients

For a discrete abelian group `A`, the pro-étale cohomology of `continuousSheaf S A : U ↦ C(U, A)`
is the étale cohomology of the constant sheaf `A`, in every degree
(`AlgebraicGeometry.ProEtale.nonempty_addEquiv_H_continuousSheaf`): the sheaf `U ↦ C(U, A)` is the
constant pro-étale sheaf, which is `ν^*` of the constant étale sheaf, and
`RΓ(S_proét, ν^* M) ≅ RΓ(S_ét, M)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

end AlgebraicGeometry.ProEtale
