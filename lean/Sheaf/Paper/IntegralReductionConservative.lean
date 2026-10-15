/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients

/-! # Conservativity of integral reduction

Source: Bhatt--Scholze, Sections 6.7--6.8 (blueprint: lem-weil-pbc-integral-reduction-conservative).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- Derived reduction modulo ℓ detects isomorphisms between bounded constructible
integral complexes. Source: Bhatt--Scholze, Proposition 6.8.11(3) and derived Nakayama
(blueprint: lem-weil-pbc-integral-reduction-conservative).

Proof in words. The valuation ring of a finite normed extension is a complete discrete
valuation ring, and ℓ is a positive power of a uniformizer times a unit. On a finite
stratification the cohomology modules are locally finitely presented. The kernel, cokernel
and extension closure of these modules makes the cone of φ bounded constructible.
The integral realization identifies the locally finitely presented internal modules
with the continuous integral sheaves in Proposition 6.8.11(3); this identification and
the coefficient-dependent closure assertions must be established, rather than inferred
from noetherianity alone. Derived reduction carries the cone to zero when the reduced
map is invertible. On each stratum, the highest potentially nonzero cohomology of the cone has
 zero reduction,
by the top-degree tensor spectral sequence. Nakayama over the valuation ring, after
pro-etale localization, makes this cohomology zero. Descending induction through the
finite cohomological interval makes every cohomology zero. The cone is therefore zero,
so φ is invertible. This argument includes torsion modules, zero complexes, and empty X;
it uses no properness or exchange hypothesis. -/
theorem integralReduction_reflects_isIso (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    {M N : ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X)}
    (φ : M ⟶ N)
    (hφ : IsIso ((integralReduction ℓ E X).map φ.hom)) : IsIso φ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
