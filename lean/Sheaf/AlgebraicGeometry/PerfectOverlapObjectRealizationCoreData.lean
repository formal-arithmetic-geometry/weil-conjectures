/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionLocalization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData

/-! # Core object comparison data (without the final Hom pin).

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
set_option maxHeartbeats 8000000 in
-- The Hom-continuity packaging unfolds a large dependent proposition.
/-- Geometric natural comparison and pinned object comparisons.
Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).

Proof: Identify the inverse-image intersections with the base changes of U intersection V
by the universal property of pullbacks. Derive pullback along these scheme isomorphisms,
and compose the apex equivalence with the inverse open-site equivalence. The restriction
and composition isomorphisms give the stage object isomorphisms. Restrict phiU and phiV
and compose with the apex cartesian isomorphism to give the apex object isomorphisms.
Construct the comparison diagrams using these same pullbacks and open-site equivalences.
Set theta to kappa followed by the image of phi followed by site; both theta equations
are reflexive. The cartesian composition comparison gives the natural comparison.
Expanding psi and theta, the site unit/counit cancel. Restriction coherence cancels
gamma and tau. Associativity of the fixed counit-pinned comparison gives object_pin.
All constructions apply to empty and coincident opens as well as arbitrary objects.
-/
theorem perfect_overlap_object_realization_core_data
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (hstage : ∀ (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens),
      ∃ k : I, j ≤ k)
    : perfectOverlapObjectRealizationCoreStatement R c hc i Z t j hij := by
  unfold perfectOverlapObjectRealizationCoreStatement
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV
  let data := perfectOverlapCanonicalComparisonFamily R c hc i Z t j hij hstage
    U V hcover hU hV A B hA hB E φU φV
  have hcore := perfect_overlap_object_realization_core_of_data R c hc i Z t j hij hstage
  unfold perfectOverlapCoreOfDataStatement at hcore
  exact ⟨⟨data, Classical.choice
    (hcore U V hcover hU hV A B hA hB E φU φV data rfl)⟩⟩

end AlgebraicGeometry
