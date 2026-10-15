module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Sheaf.Paper.CondensedQbarBaseChangeCompatibility

@[expose] public section


universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- Pointwise proper base change for the condensed finite coefficient.

Source: the finite-coefficient realization and the proper exchange theorem in the proof of
`nt-target-proetale-e` (blueprint: new-proper-continuous-basechange-app).
For every bounded constructible object, the finite-coefficient proper base-change component is
invertible; the inverse is transported through the realization comparisons. This is strictly the
componentwise part of the natural-transformation theorem; assembly is handled separately.
-/
theorem isIso_boundedConstructibleBaseChange_continuousMap_app
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] [IsProper f]
    (sq : IsPullback g' f' f g) :
    ∀ K : _,
      IsIso ((boundedConstructibleBaseChange
        (Profinite.continuousMapRingObj E) ℓ k sq.toCommSq).app K) := by
  sorry

/-- Pointwise proper base change for the condensed algebraic-closure coefficient.

Source: the finite-coefficient realization, filtered two-colimit, and proper exchange
compatibility in the proof of `nt-target-proetale-qbar`
(blueprint: new-proper-qbar-basechange-app).
For every bounded constructible object, descend to a finite coefficient stage, apply finite-stage
proper base change, and transport the inverse through coefficient-change comparisons and the
two-colimit presentation. This is strictly the componentwise part; assembly is separate.
-/
theorem isIso_boundedConstructibleBaseChange_padicAlgCl_app [IsProper f]
    (sq : IsPullback g' f' f g) :
    ∀ K : _,
      IsIso ((boundedConstructibleBaseChange
        (Profinite.padicAlgClRingObj.{u} ℓ) ℓ k sq.toCommSq).app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
