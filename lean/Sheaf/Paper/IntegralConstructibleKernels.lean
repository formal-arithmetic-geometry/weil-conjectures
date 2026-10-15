/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import Sheaf.Paper.ConstructibleCokernelsExtensions

/-! # Kernels of integral constructible internal module objects

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1).
(blueprint: lem-weil-pbc-integral-constructible-kernels)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- Kernels of maps of integral constructible internal module objects are constructible.
Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1), including the
comparison of the library's local finite presentations with finite integral models.
(blueprint: lem-weil-pbc-integral-constructible-kernels)

Proof: first use the continuous-function realization of the pulled coefficient ring.
A local finite presentation, pulled to a geometric point, is the cokernel of a finite
matrix over O_E. Its finite O_E-module isomorphism type is independent of the chosen
algebraically closed representative. Flat going-down lifts specializations through a
presentation cover. Continuous functions to the Hausdorff ring O_E agree at comparable
points, so the Smith invariants of the fiber matrices agree. On a noetherian scheme,
each connected component has finitely many irreducible components joined by intersections.
The fiber module therefore has a fixed isomorphism type on each connected component,
and there are finitely many connected components.

On a presentation cover over one component, choose an entry of smallest nonzero
valuation. Shrink to where it keeps that valuation, divide continuously by it, and
perform integral elementary row and column operations. Minimality of the valuation
keeps the quotients integral. Repeat on the smaller matrix. A zero remainder vanishes
pointwise and hence as continuous functions. Thus the module is locally a fixed finite
O_E-module model. Zero matrices and rank-zero presentations need no pivots.

Refine the two given stratifications and a constructible stratification of the cokernel,
using the proved generic cokernel closure. On each connected component of a stratum,
the source, target and cokernel therefore have fixed finite fiber module types by the
preceding comparison. Choose local presentations M = coker A and N = coker B.
Lift the finitely many generators of M through the presentation of N locally, giving
a matrix F for the map. The augmented free matrix D = (F,-B) presents its cokernel.
Thus both B and D have fixed Smith invariants, and the preceding continuous pivot
argument diagonalizes them locally. Since multiplication by a nonzero constant of
O_E is injective on continuous functions, ker B and ker D are then finite free.

Lift the finitely many columns of FA through B locally; these lifts exist because
FA has zero composite into coker B, and a sheaf epimorphism is locally surjective.
They give a map from the source relation module to ker D. Together with the map
ker B to ker D, this presents ker(M to N): project ker D to M; it surjects onto the
kernel, and its kernel consists precisely of those lifted source relations and ker B.
This is a finite presentation because the source relation module, ker B and ker D
are finite free. This argument treats torsion source and target modules without
assuming that a map between them is itself a map between free modules.
Exact inverse image computes the original kernel on the strata. These presentations
prove constructibility. Empty schemes, strata and zero ranks use empty presentations.
The finite-model comparison is part of this assertion; noetherianity alone does not
supply it for arbitrary coefficient rings. -/
theorem integralConstructible_kernels (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    ObjectProperty.IsClosedUnderKernels
      (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
