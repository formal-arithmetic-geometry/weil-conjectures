/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportDerived
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAffineGeometry
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Explicit smooth adjunction over a general field

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/
sk-thm-purity-transport/sk-prop-sp-comparison-brown-explicit.md and its proof.
(blueprint: def-pur-general-field-normalized-adjunctions).

The field-independent coefficient, Tate-line and compact-support constructions
are the published ones. The indexing below leaves the field arbitrary and does
not assume absolute separatedness of either scheme. The normalization equations
use the actual finite affine trace and the canonical scalar comparison maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ExplicitSmoothComparison

/-- The small pro-etale site is used in its actual object universe u+1.
Source: the standing small-site convention
(blueprint: def-pur-general-field-normalized-adjunctions). -/
local instance smallProEt (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- The geometric indices of the assertion: a smooth compactifiable map of pure
dimension d over a finite-type k-scheme. No algebraic closure or absolute
separatedness is part of this datum.
Source: standing geometric scope and the displayed compactification
(blueprint: def-pur-general-field-normalized-adjunctions). -/
structure Datum (k : Type u) [Field k] where
  X : Scheme.{u}
  Y : Scheme.{u}
  base : Y ⟶ Spec (.of k)
  [yFinite : LocallyOfFiniteType base]
  [yQuasiCompact : QuasiCompact base]
  map : X ⟶ Y
  [separated : IsSeparated map]
  [finiteType : LocallyOfFiniteType map]
  [quasiCompact : QuasiCompact map]
  dim : ℕ
  [smooth : SmoothOfRelativeDimension dim map]
  compactification : Compactification map

attribute [instance] Datum.yFinite Datum.yQuasiCompact Datum.separated
  Datum.finiteType Datum.quasiCompact Datum.smooth

/-- The ambient counit of this same adjunction.
Source: the specified smooth counit
(blueprint: def-pur-general-field-normalized-adjunctions). -/
def ExplicitAdjunction.trace {ell : ℕ} [Fact ell.Prime]
    {k : Type u} [Field k] {c : Coefficient ell} {s : Datum k}
    (a : ExplicitAdjunction ell c s) (K : c.ctf ell s.Y) :=
  (a.adjunction.counit.app K).hom

/-- Quantification over admissible coefficients and the displayed smooth maps.
Source: all four coefficient cases of the statement
(blueprint: def-pur-general-field-normalized-adjunctions). -/
abbrev Family (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] :=
  ∀ (c : Coefficient ell) (s : Datum k), ExplicitAdjunction ell c s

/-- The affine-line index uses the standard open chart of the projective line.
Source: integration normalization
(blueprint: def-pur-general-field-normalized-adjunctions). -/
def affineIndex (k : Type u) [Field k] (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] : Datum k := by
  let p := AffineSpace PUnit.{u + 1} Y ↘ Y
  letI : SmoothOfRelativeDimension 1 p := by
    simpa only [Nat.card_unique] using
      AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} Y
  exact
    { X := AffineSpace PUnit.{u + 1} Y
      Y := Y
      base := aY
      map := p
      dim := 1
      compactification := affineTraceLineCompactification Y }

/-- The same counits commute with the listed coefficient changes, through the
canonical compact-support mate and root-normalized scalar/pullback/tensor map.
This transports the finite affine normalization to integral, rational and
algebraic-closure coefficients rather than choosing independent counits there.
Source: final normalization paragraph, transported coefficient clause
(blueprint: def-pur-general-field-normalized-adjunctions). -/
def ScalarCompatible (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (b : Family ell k) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell),
    IsListedScalarCoefficientMap ell a →
    ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
    ∀ s : Datum k,
    ∃ p : ScalarLineCoordinates ell a ha s.X,
    ∀ K : c.ctf ell s.Y,
    ∃ hK : property ell c' s.Y ((scalarSixChange a s.Y).obj K.obj),
      (scalarSixChange a s.Y).map ((b c s).trace K) =
        (scalarSupportMap a s.compactification).app
            ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c'.obj ell) s.compactification).map
              (sourceScalar ell a s.map s.dim ha p K.obj) ≫
          (b c' s).trace ⟨_, hK⟩

end AlgebraicGeometry.ProEtale.ExplicitSmoothComparison
