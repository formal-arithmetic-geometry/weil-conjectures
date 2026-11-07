/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCETotalSections
public import Submission.WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import Submission.WeilConjectures.CategoryTheory.FilteredStationaryCycleComparison
import Submission.WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import Submission.WeilConjectures.CategoryTheory.BoundedBelowSecondFiltration

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Naturality of stationary CE page quotients

Source: Stacks Project, Homology, Tags 012K, 012Q and 012W.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality).
-/

@[expose] public section

universe uNatural

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Identifications with the actual cycle/boundary cokernels, without making any choice.
Source: Stacks Project, Tag 012K.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality). -/
abbrev EtaleCEQuotientRealization {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) :=
  ∀ (q p r : ℤ) (hr : 1 ≤ r),
    ((D.sequence.page r hr).X (q, p)) ≅
      filteredComplexPageObject D.sectionsTotal D.L r (q, p)

/-- A page map is induced by the sections-total map on graded cycle representatives.
This is an equation of maps from arbitrary test objects, rather than an existence
assertion about a spectral-sequence map. Source: Stacks Project, Tags 012K and 015K.
(blueprint: lem-weil-pbc-ce-stationary-page-naturality). -/
def EtaleCEPageMapOnRepresentatives {X Y : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    {L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (D' : EtaleTermwiseHypercohomology Y L)
    (e : EtaleCEQuotientRealization D) (e' : EtaleCEQuotientRealization D')
    (b : D.sectionsTotal ⟶ D'.sectionsTotal) (N : D.sequence ⟶ D'.sequence) : Prop :=
  ∀ (A : AddCommGrpCat.{uNatural + 1}) (q p r : ℤ) (hr : 1 ≤ r)
    (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X (q + p))
    (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X (q + p))
    (z : A ⟶ (D.L.complexCycles q (q + p) r : AddCommGrpCat.{uNatural + 1}))
    (z' : A ⟶ (D'.L.complexCycles q (q + p) r : AddCommGrpCat.{uNatural + 1})),
    x ≫ (D.L.step q).arrow.f (q + p) ≫ b.f (q + p) =
      y ≫ (D'.L.step q).arrow.f (q + p) →
    z ≫ (D.L.complexCycles q (q + p) r).arrow =
      x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
    z' ≫ (D'.L.complexCycles q (q + p) r).arrow =
      y ≫ (D'.L.complexQuotientπ q (q + 1) (by omega)).f (q + p) →
    z ≫ filteredComplexPageπ D.sectionsTotal D.L r (q, p) ≫
        (e q p r hr).inv ≫ (N.hom r hr).f (q, p) =
      z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L r (q, p) ≫ (e' q p r hr).inv


private theorem comparison_transport
    {C : Type*} [Category C] {m n : ℤ} (h : m = n)
    {P Q : C} (H J : ℤ → C) (i : P ≅ H m) (j : Q ≅ J m)
    (f : P ⟶ Q) (g : ∀ n, H n ⟶ J n)
    (sq : f ≫ j.hom = i.hom ≫ g m) :
    f ≫ (j ≪≫ eqToIso (congrArg J h)).hom =
      (i ≪≫ eqToIso (congrArg H h)).hom ≫ g n := by
  subst n
  simpa using sq


end AlgebraicGeometry.Etale
