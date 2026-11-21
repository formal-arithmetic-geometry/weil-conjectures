/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransport
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMatesData
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarOperation
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalar
import WeilConjectures.SixFunctors.ExceptionalFiniteScalar.ExceptionalFiniteScalarMaps

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ExceptionalFiniteScalar

/-- Finite scalar extension preserves the actual constructible finite-Tor categories
and their Tor intervals, with literal restrictions and the canonical scalar mates.
Quotient, ramified, identity and composite unital maps are all quantified directly. -/
theorem exceptionalFiniteScalarMates
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (n m : ℕ)
    (a : Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Nonempty (Construction l E L n m a c) := by
  classical
  obtain ⟨source⟩ := finiteScalarOperation_exists D l _hl E n f c
  obtain ⟨target⟩ := finiteScalarOperation_exists D l _hl L m f c
  obtain ⟨scalarX⟩ := finiteScalar_exists D l _hl E L n m a X
  obtain ⟨scalarY⟩ := finiteScalar_exists D l _hl E L n m a Y
  obtain ⟨maps⟩ :=
    finiteScalarMaps_exists D l _hl E L n m a f c scalarX scalarY source target
  exact ⟨{
    scalarX := scalarX
    scalarY := scalarY
    source := source
    target := target
    q := maps.q
    b := maps.b
    q_normalized := maps.q_normalized
    counit := maps.counit
    qShift := maps.qShift
    bShift := maps.bShift
    etale := maps.etale
  }⟩

end WeilConjectures.ExceptionalFiniteScalar
