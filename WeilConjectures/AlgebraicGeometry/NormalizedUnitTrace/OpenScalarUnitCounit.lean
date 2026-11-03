/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedUnitTrace.OpenUnitTraceCoordinates

/-!
# Scalar transport of open unit counits

Source: smooth purity transport Steps 2--3, expanded as open normalization
Step 5 (blueprint: lem-pur-open-scalar-unit-counit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormalizedUnitTrace
open Scheme PurityTransport ExplicitSmoothComparison

/-- Scalar compatibility gives an equality with the explicit transport function,
and this same function preserves the ordinary open counit. Neither assertion
assumes the geometric normalization of the integral smooth counit.

Source: smooth purity transport coefficient compatibility and open normalization
Step 5 (blueprint: lem-pur-open-scalar-unit-counit).

Proof: apply the scalar counit equation to Z_ell -> Q_ell -> Omega and the unit.
Naturality moves the pullback/source unitor across the proper/open scalar mate;
the pointwise scalar unit trace calculation cancels the normalized source line
comparison. At dimension zero that comparison is exactly the derived scalar unit,
including the specified zero shift. For the trivial compactification, the proper
factor is the identity and the scalar support mate is the canonical open scalar
isomorphism. Its defining adjunction mate equation preserves the ordinary open
counit. The scalar-refinement pasting theorem identifies this formula with the
one in every chosen compactification. Thus the first assertion has precisely the
factors of transportIntegralOpenTrace. For the second, substitute the ordinary
integral counit and cancel the two inverse compactification comparisons. The
open mate counit equation and the scalar-unit comparison give the ordinary Omega
counit. Counit-preserving conjugation identifies this with the published bounded
exceptional open-unit counit. This last identification retains the bounded to
ambient compatibility isomorphism appearing in boundedOpenUnitTrace. -/
theorem openScalarUnitCounit
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (b : Family ell k) (hscalar : ScalarCompatible ell k b)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (unitCounit ell b .closure j =
      transportIntegralOpenTrace ell j (unitCounit ell b .integers j)) ∧
    (transportIntegralOpenTrace ell j
      (ordinaryUnitTrace ell .integers (integersAdmissible ell) j) =
        boundedOpenUnitTrace ell j) := by
  sorry

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
