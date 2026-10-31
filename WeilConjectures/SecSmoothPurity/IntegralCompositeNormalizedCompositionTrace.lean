/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CompositionTrace

/-! # Integral normalized trace on generated composite compactifications

This is the whole-tower realization step before arbitrary compactification
refinement.  The latter is isolated in `IntegralNormalizedTraceRefinement`.
(blueprint: lem-pur-integral-normalized-composition-trace)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale.CondensedRing
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The normalized trace equation for composite compactifications generated from
an initial compactification of `s.map`, a compactification of `g`, and a boundary
compactification of the middle proper/open composite: `NormalizedCompositionTrace`
with `ch := compositeCompactification s.compactification cg cr`.
Source: current blueprint `sk-prop-sp-composition.proof.md`, Towers paragraph
(blueprint: def-pur-integral-composite-normalized-composition-trace). -/
def CompositeNormalizedCompositionTrace
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (c : Coefficient ell) : Prop :=
  ∀ (s : SmoothDatum D) (Z : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of D.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification
      (s.compactification.g ≫ cg.i))
    (H : CompactSupportComposition.CoherentData (c.obj.{u} ell) D.k),
    letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
      fun x ↦ (by
        simpa only [map_natCast] using (primeUnit D ell hEll).map
          ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (ell : s.X.left.residueField x)).invertible
    let sg : SmoothDatum D :=
      { X := s.Y, Y := Z, map := g, dim := e, compactification := cg }
    let sh : SmoothDatum D :=
      { X := s.X, Y := Z, map := s.map ≫ g, dim := s.dim + e,
        compactification := compositeCompactification s.compactification cg cr }
    let af := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c s
    let ag := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c sg
    let ah := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c sh
    ∃ p : LinePullCoordinates ell c s.map, ∀ K : c.ctf ell Z.left,
      (WeilConjectures.PurityWeil.Condensed.supportComposition D H
        (SepFinType.homMk (X := s.X) (Y := s.Y)
          (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
        (SepFinType.homMk (X := s.Y) (Y := Z)
          (Over.homMk g (comp_over g (Spec (.of D.k)))))
        s.compactification cg (compositeCompactification s.compactification cg cr)).hom.app
          ((inclusion ell c s.X.left).obj
            ((source ell c sh.map sh.dim
              ah.source_closed).obj K)) ≫
        ah.trace K =
      (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification).map
          (sourceComp ell c s.map g s.dim e p K.obj).hom) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
          (af.trace
            ((source ell c g e
              ag.source_closed).obj K)) ≫
        ag.trace K

/--
Source: current blueprint `sk-prop-sp-composition.proof.md`, Towers paragraph
(blueprint: lem-pur-integral-composite-normalized-composition-trace).

Proof in words.  In the normalized `𝒪_E / ℓ^•` tower, use the finite
composition-factors equations to identify the two orientations of the composite
purity map.  Apply the total derived-limit comparison to this equality of tower
morphisms, then use the native integral compositor realization and the integral
counit realization to identify the resulting support and trace pastes with the
selected normalized family.  The same construction with the base-field integral
presentation gives the `ℤ_ℓ` conjunct; the argument is uniform for every finite
intermediate field, including ramified fields. -/
theorem integralCompositeNormalizedCompositionTrace
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) :
    CompositeNormalizedCompositionTrace ell D hEll .integers ∧
      ∀ E : PadicAlgCl.FiniteIntermediateField ell,
        CompositeNormalizedCompositionTrace ell D hEll (.integral E) := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
