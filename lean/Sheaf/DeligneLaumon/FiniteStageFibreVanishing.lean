/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.LisseRationalRealizationData
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Sheaf.Paper.CondensedERealization
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed

/-! # Point sections and finite-stage constructible vanishing

Source: Bhatt--Scholze, Definition 6.8.3, Proposition 6.8.14(2), Remark 6.8.15;
blueprint p-dl-a1-exact.proof.md, Steps 1 and 5
(blueprint: lem-dl-a1-finite-stage-fibre-vanishing).

The normalized `LisseRealization.At.J` is the continuous realization in the intrinsic
raw coefficient presentation: its integral comparison is derived extension of scalars
along the residue-normalized completion and the actual integral-to-rational inclusion.
Thus the lisse assumption below is on this realization, rather than a chosen global basis.
The point functor is the recorded `pointRationalFibre`, with its degree-zero module lifted
only in carrier size. The comparison is a natural isomorphism on the full subcategory
where the restricted realization is a lisse sheaf of the specified rank.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.DeligneLaumon

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The prescribed point fibre after completed pullback, before taking cohomology.
Source: BS 6.8.14(2), blueprint p-dl-a1-exact.proof.md, Steps 1 and 5
(blueprint: lem-dl-a1-finite-stage-fibre-vanishing). -/
def finiteStagePointComplex (T : LisseRealization.Base D l hl)
    (y : (LisseRealization.point D l hl).scheme ⟶ T.scheme) :=
  (sfRationalHeartProperty l E T.scheme).ι ⋙ LisseRealization.pull D l hl E y ⋙
    pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι

/-- Degree-zero vector space of that same point fibre; `uliftFunctor` only changes size.
Source: BS 6.8.14(2), blueprint p-dl-a1-exact.proof.md, Steps 1 and 5
(blueprint: lem-dl-a1-finite-stage-fibre-vanishing). -/
def finiteStagePointFibre (T : LisseRealization.Base D l hl)
    (y : (LisseRealization.point D l hl).scheme ⟶ T.scheme) :=
  (sfRationalHeartProperty l E T.scheme).ι ⋙ LisseRealization.pull D l hl E y ⋙
    LisseRealization.fibre D l hl E

/-- The node's local hypothesis: the realized restriction is in degree zero and its
cohomology sheaf is pro-etale locally free of constant rank `r`. Local generators are
allowed on a cover; no global trivialization is part of this predicate.
Source: BS Definition 6.8.3 (blueprint: lem-dl-a1-finite-stage-fibre-vanishing). -/
def finiteStageLisseRestriction (T C : LisseRealization.Base D l hl)
    (b : C.scheme ⟶ T.scheme) (a : LisseRealization.At D l hl E C) (r : ℕ) :
    ObjectProperty (sfRationalHeart l E T.scheme) :=
  fun F ↦
    Nonempty (a.J.obj ((LisseRealization.pull D l hl E b).obj F.obj) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((a.sheaf D l hl E).obj ((LisseRealization.pull D l hl E b).obj F.obj))) ∧
    ((a.sheaf D l hl E).obj
      ((LisseRealization.pull D l hl E b).obj F.obj)).IsFiniteLocallyFreeOfRank r

/-- Ordinary module pullback of the realized restriction, followed by sections at Spec k.
The coefficient action is the existing action by constant continuous E-valued functions.
Source: BS Definition 6.8.3, Remark 6.8.15
(blueprint: lem-dl-a1-finite-stage-fibre-vanishing). -/
def finiteStageOrdinaryPointSections (T C : LisseRealization.Base D l hl)
    (b : C.scheme ⟶ T.scheme) (a : LisseRealization.At D l hl E C)
    (x : (LisseRealization.point D l hl).scheme ⟶ C.scheme) :=
  (sfRationalHeartProperty l E T.scheme).ι ⋙ LisseRealization.pull D l hl E b ⋙
    a.sheaf D l hl E ⋙ LisseRealization.ordinaryPull l E x ⋙
      LisseRealization.sections D l hl E

/-- Point sections compute the constant lisse rank, detect zero on a connected lisse
stratum, and jointly detect zero for constructible rational adic heart objects.

Source: BS Definition 6.8.3, Proposition 6.8.14(2), Remark 6.8.15;
blueprint p-dl-a1-exact.proof.md, Steps 1 and 5
(blueprint: lem-dl-a1-finite-stage-fibre-vanishing).

Proof plan (the five steps of the node):
1. Put K = Lb*F. The realization and pullback-composition comparisons of
lem-weil-pbc-condensed-e-realization identify J_s L(bx)*F with Lx* J_C K. Local
freeness makes the latter ordinary module pullback. The canonical point
sections-localization map of lem-tw-lisse-point-sections-realization identifies
this with the prescribed rational fibre. Each comparison is natural in F; the fibre
is concentrated in degree zero, so this yields the displayed vector-space natural iso.
2. Pull a trivializing pro-etale cover back to x. By
lem-weil-pbc-geometric-field-proetale-evaluation the resulting cover of Spec k splits.
Pulling a trivialization back along its section gives E^r on sections, since continuous
functions on a singleton are E. This computes dimension, without selecting the natural
comparison from a basis. If a fibre is zero, r = 0; the original cover then trivializes
the realized sheaf as zero. Separatedness of sheaves and the realization equivalence give
Lb*F = 0. This argument includes r = 0.
3. For global detection, lem-dl-a1-heart-connected-lisse-strata provides a finite good
stratification with connected lisse components and k-points on every nonempty component.
Apply Step 2 at each supplied point. The restrictions to all strata are zero, by the
pullback comparisons and the sheaf axiom on the open connected components.
4. Reduce the ambient scheme using lem-weil-pbc-reduction-universal-homeomorphism and
lem-trf-proetale-topological-invariance. The coefficient identifications are those of
lem-weil-pbc-continuous-coefficients-immersion-restriction. Finite type over a field gives
Noetherianity by lem-weil-pbc-finite-type-over-noetherian, so the opens used are qc.
5. Induct on the number of nonempty strata on the reduction. The empty-cover sheaf axiom
handles the empty scheme. A maximal stratum is open by the frontier condition; its
reduced closed complement has fewer strata. Induction and
lem-weil-pbc-proetale-ringed-open-closed give the exact sequence 0 -> j_!0 -> M -> i_*0
-> 0, hence M = 0. The realization equivalence reflects zero. This uses only
constructible objects, and asserts no point-conservativity for arbitrary pro-etale sheaves. -/
theorem finite_stage_fibre_vanishing
    (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (T : LisseRealization.Base D c.l c.different)
    [IsSeparated (T.scheme ↘ Spec (.of D.k))] :
    (∀ (C : LisseRealization.Base D c.l c.different)
      (b : C.scheme ⟶ T.scheme) [b.IsOver (Spec (.of D.k))]
      [IsImmersion b] [IsReduced C.scheme] [ConnectedSpace C.scheme]
      (a : LisseRealization.At D c.l c.different E.val C) (r : ℕ)
      (x : (LisseRealization.point D c.l c.different).scheme ⟶ C.scheme)
      [x.IsOver (Spec (.of D.k))],
      Nonempty
        ((finiteStageLisseRestriction D c.l c.different E.val T C b a r).ι ⋙
            finiteStagePointFibre D c.l c.different E.val T (x ≫ b) ≅
          (finiteStageLisseRestriction D c.l c.different E.val T C b a r).ι ⋙
            finiteStageOrdinaryPointSections D c.l c.different E.val T C b a x) ∧
      ∀ F : (finiteStageLisseRestriction D c.l c.different E.val T C b a r).FullSubcategory,
        Nonempty
          ((finiteStagePointComplex D c.l c.different E.val T (x ≫ b)).obj F.obj ≅
            (DerivedCategory.singleFunctor.{u} (ModuleCat.{u} E.val) 0).obj
              ((DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E.val) 0).obj
                ((finiteStagePointComplex D c.l c.different E.val T (x ≫ b)).obj F.obj))) ∧
        Module.finrank E.val
          ((finiteStagePointFibre D c.l c.different E.val T (x ≫ b)).obj F.obj) = r ∧
        (Subsingleton
            ((finiteStagePointFibre D c.l c.different E.val T (x ≫ b)).obj F.obj) →
          IsZero ((LisseRealization.pull D c.l c.different E.val b).obj F.obj.obj))) ∧
    (∀ F : sfRationalHeart c.l E.val T.scheme,
      (∀ (y : (LisseRealization.point D c.l c.different).scheme ⟶ T.scheme)
        [y.IsOver (Spec (.of D.k))],
        IsZero ((finiteStagePointComplex D c.l c.different E.val T y).obj F)) →
      IsZero F.obj) := by
  sorry

end WeilConjectures.DeligneLaumon
