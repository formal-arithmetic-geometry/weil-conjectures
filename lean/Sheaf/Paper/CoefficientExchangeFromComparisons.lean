/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import Sheaf.Paper.FiniteDiscreteDerivedCoefficientData
import Sheaf.CategoryTheory.ThreeStepAdjunctionComparison
import WeilConjectures.SixFunctors.BaseChange.Derived

/-! # The specified exchange from coherent coefficient comparisons -/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable (ℓ : ℕ) [Fact ℓ.Prime]
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

/-- Coherent coefficient comparisons identify the three specified exchange factors.
Source: Mathlib adjunction restriction and mates; the specified exchange definitions
(blueprint: lem-weil-pbc-coefficient-exchange-from-comparisons).

Proof in words. The coefficient is the continuous-function condensed ring of the
finite discrete ring B, killed by ell. These hypotheses put the restricted direct
images in the prime-to-characteristic finite-coefficient setting.
The morphisms f and f-prime are qcqs: use the qcqs structure maps
and the separated targets over Spec k. Apply threeStepComparison to the two etale
and two internal derived adjunctions, with the four pullback isomorphisms and the
two direct-image isomorphisms supplied by P. Its hypotheses are exactly P.unit,
P.counit and P.square. The four vertex isomorphisms are the composites displayed
in that categorical theorem; take their inverses to orient the comparison here.

For a bounded constructible realized object N, fully faithful adjunction restriction
identifies the underlying restricted unit and counit with the ambient unit and
counit. The inclusion compatibility isomorphisms are identities, so the restriction
formulas simplify using map_id. Likewise the underlying restricted pullback
composition isomorphism is leftDerivedUpperStarComp. Inclusion preserves the
composition, inverse, and equality-transport isomorphisms, so the restricted square
has underlying coefficientAmbientSquare. The component formulas for whiskering,
unitors and squareTransport now identify the three specified restricted factors
with the three ambient factors, and the etale component lemmas identify the other
three factors. Substitute these six component identities in the categorical
comparison. Finally apply boundedConstructibleBaseChange_eq_unit_square_counit,
project to underlying morphisms, and use Etale.baseChange_app followed by map_comp
to supply the two required total-arrow factorizations. None of these steps asserts
that exchange is invertible, or requires a Cartesian square or properness. Empty
schemes and zero objects are included. -/
theorem coefficientComparisonData_exchangeSteps [DiscreteTopology B] [Finite B]
    (hB : (ℓ : B) = 0) (sq : CommSq g' f' f g)
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (FiniteDiscreteInternalModules B T))
    (P : CoefficientComparisonData B (Profinite.continuousMapRingObj B) F) :
    finiteDiscreteExchangeSteps B ℓ k sq (F X) (F Y') := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
