/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ComparisonBrownExplicit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-! # Open scalar coordinate calculations -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormalizedUnitTrace
open Scheme CondensedRing PurityTransport ExplicitSmoothComparison

/-- The canonical compactification coordinates preserve the bounded open counit.
Source: smooth purity transport, Step 3, and open normalization, Step 6
(blueprint: lem-pur-open-bounded-counit-coordinates).

Proof: let L be the published bounded compact-support/open isomorphism.
The bounded exceptional/open isomorphism is its adjunction conjugate. Apply
the conjugate counit equation at the coefficient unit, then precompose with
the inverse pullback unit. This rewrites the bounded exceptional unit counit
as L followed by the bounded ordinary open unit counit.

Apply the fully faithful inclusion into the ambient derived category.
The restrictFullyFaithful counit formula and the bounded pullback unit formula
identify the latter counit with the ambient ordinary open counit, transported
by the specified exact-to-left-derived pullback comparison. The retained
compact-support compatibility supplies its precise source coordinate.

To identify the remaining compactification map, choose a common dense boundary
refinement of the chosen and trivial compactifications. Compute the bounded
compactification comparison through this refinement by its coherence theorem for any common
refinement. The ambient refinement component is the image of
the bounded refinement map: expand their open-adjunction transposes and proper
compositors, and use restriction of the same ambient adjunctions. Both
comparisons consequently have the same composites with the refinement component
to the trivial compactification. This component is invertible on the unit, so
cancellation identifies them. The proper identity factor agrees with identityPush
because both are conjugate to the specified identity pullback. Substituting
these equalities into the first counit equation gives exactly ordinaryUnitTrace
and boundedOpenUnitTrace in the claimed order. -/
theorem openBoundedCounitCoordinates
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    ordinaryUnitTrace ell .closure (closureAdmissible ell) j =
      boundedOpenUnitTrace ell j := by
  sorry

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
