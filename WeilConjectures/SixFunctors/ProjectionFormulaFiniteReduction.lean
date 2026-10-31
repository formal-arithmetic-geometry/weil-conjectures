/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement

import WeilConjectures.SixFunctors.FiniteReductionCompactSupportIso
import WeilConjectures.SixFunctors.FiniteReductionProjectionSquare
import WeilConjectures.SixFunctors.FiniteReductionProjectionIso

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open WeilConjectures
open scoped CategoryTheory.Functor

noncomputable section
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The finite reduction square for the native condensed projection map.

Source: `literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/det-prop-sf-pf-reduction.md`, node
`det-prop-sf-pf-reduction`, order 2919 (blueprint: det-prop-sf-pf-reduction).

Proof steps: (1) set A and B to the n and m quotient coefficient rings, use the
canonical quotient rho induced by Ideal.Quotient.factor, and choose a common compactification;
the canonical mates c_f, s, t and a^f are the definitions of def-sf-pf-finite-reduction-data
(Push as the base-change mate of the inverse Pull comparison, pasted with the open Shriek
isomorphism; s the derived tensorator; a^f = (1 ⊗ t) s). (2) paste the proper Push identity
with the open Shriek identity and use naturality
of the condensed projection map to obtain the displayed step-2 equation for the specified
comparisons. (3) apply the finite projection-formula theorem at A and B, then cancel the
invertible c_f, s, t and a^f maps; this gives the final equivalence of IsIso of the two
projection maps.

Lean proof: the clauses for `s`, `t` and `a^f` are proved here from the monoidal tensorator and
`FiniteReduction.isIso_derivedPullHomFree`; the compact-support clauses, the square and the final
equivalence are the stage-3 statements `finiteReduction_compactSupport_isIso`
(det-prop-sf-pf-reduction-compact-support-iso), `finiteReduction_projection_square`
(det-prop-sf-pf-reduction-square) and `finiteReduction_projection_isIso_iff`
(det-prop-sf-pf-reduction-iso-iff). -/
theorem projectionFormula_finiteReduction
    (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    {m n : ℕ} (hmn : m ≤ n)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))] [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f]
    (K : ConstantModelConstructibleFiniteTor
      (DerivedNakayama.quotientRing ell E (n + 1)) X)
    (L : ConstantModelConstructibleFiniteTor
      (DerivedNakayama.quotientRing ell E (n + 1)) Y) :
    IsIso (FiniteReduction.c_f (f := f) ell E hmn K.obj) ∧
      IsIso (FiniteReduction.c_f (f := f) ell E hmn
        (K.obj ⊗ (CompactificationReindexing.P
          (DerivedNakayama.quotientRing ell E (n + 1)) f).obj L.obj)) ∧
      IsIso (FiniteReduction.s ell E hmn
        ((CompactificationReindexing.F
          (DerivedNakayama.quotientRing ell E (n + 1))
          (HasCompactification.compactification f)).obj K.obj) L.obj) ∧
      IsIso (FiniteReduction.t (f := f) ell E hmn L.obj) ∧
      IsIso (FiniteReduction.a_f (f := f) ell E hmn K.obj L.obj) ∧
      ((FiniteReduction.reduction ell E hmn).map
          (CompactificationReindexing.pf
            (DerivedNakayama.quotientRing ell E (n + 1))
            (HasCompactification.compactification f) K.obj L.obj) ≫
        FiniteReduction.c_f (f := f) ell E hmn
          (K.obj ⊗ (CompactificationReindexing.P
            (DerivedNakayama.quotientRing ell E (n + 1)) f).obj L.obj) ≫
        (CompactificationReindexing.F
          (DerivedNakayama.quotientRing ell E (m + 1))
          (HasCompactification.compactification f)).map
          (FiniteReduction.a_f (f := f) ell E hmn K.obj L.obj) =
      FiniteReduction.s ell E hmn
          ((CompactificationReindexing.F
            (DerivedNakayama.quotientRing ell E (n + 1))
            (HasCompactification.compactification f)).obj K.obj) L.obj ≫
        (FiniteReduction.c_f (f := f) ell E hmn K.obj ⊗ₘ 𝟙 _) ≫
        CompactificationReindexing.pf
          (DerivedNakayama.quotientRing ell E (m + 1))
          (HasCompactification.compactification f)
          ((FiniteReduction.reduction ell E hmn).obj K.obj)
          ((FiniteReduction.reduction ell E hmn).obj L.obj)) ∧
      (IsIso (CompactificationReindexing.pf
          (DerivedNakayama.quotientRing ell E (n + 1))
          (HasCompactification.compactification f) K.obj L.obj) ↔
        IsIso (CompactificationReindexing.pf
          (DerivedNakayama.quotientRing ell E (m + 1))
          (HasCompactification.compactification f)
          ((FiniteReduction.reduction ell E hmn).obj K.obj)
          ((FiniteReduction.reduction ell E hmn).obj L.obj))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (finiteReduction_compactSupport_isIso ell D hEll E hmn K L).1
  · exact (finiteReduction_compactSupport_isIso ell D hEll E hmn K L).2
  · letI := FiniteReduction.quotientRing_monObj ell E (n + 1)
      (HasCompactification.compactification f).Z
    letI := FiniteReduction.quotientRing_monObj ell E (m + 1)
      (HasCompactification.compactification f).Z
    unfold FiniteReduction.s
    infer_instance
  · letI : IsIso (FiniteReduction.derivedPullHomFree ell E hmn f) :=
      FiniteReduction.isIso_derivedPullHomFree ell E hmn f
    unfold FiniteReduction.t
    infer_instance
  · letI : IsIso (FiniteReduction.derivedPullHomFree ell E hmn f) :=
      FiniteReduction.isIso_derivedPullHomFree ell E hmn f
    letI : IsIso (FiniteReduction.s ell E hmn K.obj
        ((CompactificationReindexing.P
          (DerivedNakayama.quotientRing ell E (n + 1)) f).obj L.obj)) := by
      unfold FiniteReduction.s
      infer_instance
    letI : IsIso (FiniteReduction.t (f := f) ell E hmn L.obj) := by
      unfold FiniteReduction.t
      infer_instance
    unfold FiniteReduction.a_f
    infer_instance
  · exact finiteReduction_projection_square ell D hEll E hmn K L
  · exact finiteReduction_projection_isIso_iff ell D hEll E hmn K L

end AlgebraicGeometry.ProEtale.CondensedRing

end
