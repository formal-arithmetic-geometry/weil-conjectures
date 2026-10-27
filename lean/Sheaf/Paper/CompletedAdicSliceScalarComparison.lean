/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral

/-! # Scalar extension on a pro-etale slice

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

set_option linter.defProp false in
/-- The ordinary and derived scalar-extension pair on the actual slice site.
Only universally characterized tensor and derived functors are chosen.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison). -/
def completedAdicSliceChangeData (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  letI : EssentiallySmall.{t + 1} (Over U) := essentiallySmallSelf.{0, t, t + 1} _
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (R.over U)))
  letI := HasDerivedCategory.standard (SheafOfModules.{t + 1}
    ((sheafCompose ((ProEt.topology X).over U)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj (S.over U)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (((ProEt.topology X).overPullback CommRingCat.{t + 1} U).map f)

/-- Derived extension along the restricted coefficient map on the slice.
Source: Stacks Tag 06YY.
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison). -/
def completedAdicSliceDerivedChange (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :=
  (completedAdicSliceChangeData X U f).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose

/-- Exact slice restriction commutes with unbounded derived scalar extension.
This is a comparison of the two functors, for an arbitrary coefficient map; it
contains no adic quotient, constant model, or local-isomorphism hypothesis.

Source: Stacks Project, sites-cohomology.tex, lemma-derived-base-change (06YY),
lemma-pullback-K-flat (0G7E), and lemma-derived-pullback-composition (0D6D).
(blueprint: lem-weil-pbc-completed-adic-slice-scalar-comparison).

Proof: choose a flat-term K-flat resolution of the input. Restriction to the slice
is the inverse image of the localization morphism of topoi and is exact. It carries
this resolution to a flat-term K-flat resolution, by pullback-K-flat. Ordinary scalar
extension commutes with slice restriction: on an object V -> U the two presheaf
tensors are the same tensor over R(V), and module sheafification commutes with
localization of the site. Consequently these identifications commute with all
restriction maps and differentials. The universal derived counits identify the two
localized complexes with the displayed composite functors. The representative
comparison is natural on K-flat complexes; localization of their homotopy category
extends it uniquely to a natural isomorphism on the entire derived category.
This also applies when U is empty or one of the coefficient rings is zero. -/
theorem completedAdic_slice_scalarComparison (X : Scheme.{t}) (U : X.ProEt)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    Nonempty
      (ringedDerivedRestrictionGeneral
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) U ⋙
          completedAdicSliceDerivedChange X U f ≅
        completedAdicDerivedChange X f ⋙
          ringedDerivedRestrictionGeneral
            ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S) U) := by sorry

end AlgebraicGeometry.Scheme
