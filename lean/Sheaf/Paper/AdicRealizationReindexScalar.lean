/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicRealizationReindexComponents

/-! # The scalar square for the prescribed integral realization components

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-realization-reindex-scalar)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (stageSystem)

/-- The explicit integral reindexing composite commutes with coefficient enlargement.
Only the scalar square is asserted: both finite-stage natural isomorphisms have already
been constructed, and no common-stage natural transformation is assumed or produced.

Source: BS Remark 6.8.15, via Proposition 6.8.14; HRS Lemma 7.9; the mixed scalar
square in Step 4 of lem-sf-adic-realization-isomorphism-normalization.
(blueprint: lem-sf-adic-realization-reindex-scalar).

Proof in words: expand realizationReindexComposite_hom inside realizationIntegralReindex
at E and at L. The common_field
fields of R and S express their images of isoToStage by the specified finite-free
completion maps and balanced derived scalar associators. The prescribed common-stage
pullback acts on this transition by rationalPullbackScalarComparison, with the recorded
stage-transition identifications. Substitute these three formulas. On constructible
integral inputs the actual completion-unit comparison podCompletedToTower is invertible.
Its scalar square is the whole-cone scalar-extension square: the quotient coaugmentation
has zero shifted coordinate, so reindexing takes it to that same coaugmentation after
coefficient extension. Equivalently, use isomorphismComparison_scalarExtension after
identifying the specified comparison by its completion-unit normalization, then invert
its two complete-input components. The balance and representative equations of I(E)
and I(L) identify the remaining derived scalar maps with their cochain maps. On pure
sections these maps associate coefficient tensors and multiply their scalars, by the
sections fields and R.coefficient_scalar and S.coefficient_scalar. Balanced tensor
associativity therefore identifies the remaining square. The cochain counit equations
descend this equality through the good-complex localizations. Finally localization
preserves the equality; the component equation of realizationRationalReindex_existsUnique
identifies the L component with that just computed on its integral representative.
Identity extensions, zero objects, empty schemes, and ramified finite extensions use
these same normalized completion maps; no cancellation of a noninvertible ambient
completion unit is used. -/
theorem realizationIntegralReindex_scalar (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (B : RingReindex l X g R S) (I : ∀ E, IntegralReindex l X g B E)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let P := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := Y) E).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y).obj K)
    let t := (stageSystem l (PadicAlgCl l) Y).isoToStage P h
    (commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R).map t.hom ≫
        (realizationRationalReindex l g R S B L (I L)).hom.app (P.toStage h) =
      (realizationIntegralReindex l g R S B E (I E)).hom.app K ≫
        (ordinary l Y S ⋙ derivedPull l X g B).map t.hom := by sorry

end WeilConjectures.AdicQbarRealization
