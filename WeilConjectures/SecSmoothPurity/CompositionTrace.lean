/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTrace
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData

/-! # The normalized smooth counit composition equation

Source: current blueprint sk-prop-sp-composition.proof.md, coefficient passage,
and DAG sk-prop-sp-composition, Steps 3--7.
(blueprint: def-pur-normalized-composition-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The equality of the specified smooth adjunction counits, before comparison
with a Brown right adjoint. The support compositor is the normalized proper/open
one in `H`; the source comparison is the existing root-normalized Tate word.
The total compactification is arbitrary. This predicate includes no chosen
exceptional compositor or purity comparison.
Source: smooth-purity composition, DAG Step 5, equation (*) with the
counits of the normalized family. (blueprint: def-pur-normalized-composition-trace). -/
def NormalizedCompositionTrace
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (c : Coefficient ell) : Prop :=
  ∀ (s : SmoothDatum D) (Z : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of D.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (ch : Compactification (s.map ≫ g))
    (H : CompactSupportComposition.CoherentData (c.obj.{u} ell) D.k),
    letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
      fun x ↦ (by
        simpa only [map_natCast] using (primeUnit D ell hEll).map
          ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (ell : s.X.left.residueField x)).invertible
    let sg : SmoothDatum D :=
      { X := s.Y, Y := Z, map := g, dim := e, compactification := cg }
    let sh : SmoothDatum D :=
      { X := s.X, Y := Z, map := s.map ≫ g, dim := s.dim + e, compactification := ch }
    let af := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c s
    let ag := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c sg
    let ah := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c sh
    ∃ p : LinePullCoordinates ell c s.map, ∀ K : c.ctf ell Z.left,
      (WeilConjectures.PurityWeil.Condensed.supportComposition D H
        (SepFinType.homMk (X := s.X) (Y := s.Y)
          (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
        (SepFinType.homMk (X := s.Y) (Y := Z)
          (Over.homMk g (comp_over g (Spec (.of D.k)))))
        s.compactification cg ch).hom.app
          ((inclusion ell c s.X.left).obj
            ((source ell c sh.map sh.dim ah.source_closed).obj K)) ≫ ah.trace K =
        (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
          ((CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj ell) s.compactification).map
            (sourceComp ell c s.map g s.dim e p K.obj).hom) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
            (af.trace ((source ell c g e ag.source_closed).obj K)) ≫ ag.trace K

end AlgebraicGeometry.ProEtale.PurityTransport
