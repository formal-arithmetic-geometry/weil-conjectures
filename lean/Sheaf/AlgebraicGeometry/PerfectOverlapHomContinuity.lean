/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData

import Sheaf.AlgebraicGeometry.PerfectOverlapHomPresentation

/-! # Directed Hom continuity for prescribed overlap comparisons

Source: Stacks Project, Tags 09RE and 09RF.
(blueprint: lem-pc-perfect-overlap-hom-continuity).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

set_option synthInstance.maxHeartbeats 400000 in
-- Exact derived-category instances are supplied by the shared restriction API.
set_option maxHeartbeats 1600000 in
-- Unfolding the dependent statement exposes all prescribed comparison functors.
/-- Canonical overlap comparisons have directed Hom continuity for the two local objects.
This asserts lifting and eventual equality of morphisms, not invertible transition descent.
Source: Stacks Project, Tags 09RE, 09RF, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-hom-continuity).

Proof: Work on the directed tail above j. The compact overlap is finitely presented
and quasi-separated over R_j. Restrict A and B there; pullback preserves perfectness.
At each stage construct HU, HV and HW as pullback on the open subschemes followed
by the inverse open-site equivalences. The canonical composition and restriction
comparisons provide the diagram and the two functorial transports. Compose these
with the supplied local identifications to define thetaU and thetaV. Their overlap
composites identify both limit objects with the restriction of E to P intersection Q.
For every ordered pair of the two overlap objects apply perfect Hom continuity on
this finitely presented overlap. Its surjectivity gives lift, and its injectivity
criterion gives eventual equality at every later stage. The stage pullback functors,
conjugated by the canonical comparisons, give transport, preserve identity and
composition, and retain the limit image. These identities follow from functoriality
and the coherence of the canonical restriction/pullback comparisons. No inverse
is lifted here and no stage isomorphism is asserted. Empty and coincident opens
use the same functors and continuity statements. -/
theorem perfect_overlap_hom_continuity
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
    : perfectOverlapHomContinuityStatement R c hc i Z t j hij hstage := by
  unfold perfectOverlapHomContinuityStatement
  intro Yj X gj U V hcover hU hV A B hA hB E instP instQ instX PU PV φU φV
    P Q RU RV RW SP SQ τU τV
  have hp := perfect_overlap_hom_presentation R c hc i Z t j hij hstage
  unfold perfectOverlapHomPresentationStatement at hp
  have hp' := hp U V hcover hU hV A B hA hB E φU φV
  obtain ⟨⟨data, presentation⟩⟩ := hp'
  refine ⟨⟨data, ?_⟩⟩
  apply Classical.choice
  apply PerfectHomPresentation.toSystem (hc := hc)
  exact presentation

end AlgebraicGeometry
