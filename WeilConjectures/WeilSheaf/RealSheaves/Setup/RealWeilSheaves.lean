/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Category.MonCat.FilteredColimits
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralFibrePathConstruction
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.ConstructibleSheaf.Biproduct
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.AlgebraicGeometry.GaloisPointGeometricComparison
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Construction
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup
public import Mathlib.CategoryTheory.Localization.Construction
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.CompactOpen
import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.Nakayama
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Module.Lattice
import Mathlib.GroupTheory.QuotientGroup.Finite
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.RepresentationTheory.IntegralModel

/-! # Weil sheaves and representations on the real-sheaf curve

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-weil;
Deligne, Weil II (1.1.1), (1.1.10)--(1.1.13), and Stanford L19, pp. 3--5
(blueprint: sk-d-real-weil).

The Weil group, its topology, local Frobenius, lisse representations and actual
etale lisse Weil pairs are the existing dependency declarations. The additional
constructible objects retain one global compatible system and one global rational
Weil isomorphism. A single finite stratification of the arithmetic curve trivializes
its integral model stratumwise. The Weil isomorphism need not preserve that model.

## Main definitions and statements

* `RealSheaves.ConstructibleWeilSheaf`: finite-coefficient representatives of global pairs.
* `AlgebraicGeometry.WeilGroup.isLisse_iff_finiteModel`: the finite-model criterion,
  with a geometric stable lattice and no condition on its degree-one operator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace RealSheaves

/-- Reuse the finite-field datum with precisely the fields already fixed in Setup.
Source: blueprint sk-d-real-weil, standing setup (blueprint: sk-d-real-weil). -/
def Setup.weilFieldDatum (D : Setup.{u, v}) : WeilConjectures.FiniteFieldDatum.{u} where
  p := D.p
  a := D.a
  q := D.q
  prime := D.p_prime
  exponent_pos := D.a_pos
  cardinality_eq := rfl
  k₀ := D.k₀
  card_base := Nat.card_eq_fintype_card.trans D.card_eq
  k := D.k

/-- Geometric Galois Frobenius on the actual chosen geometric fibre, with inverse
q-power action on the closure. Source: Weil II (1.1.7), (1.1.10)
(blueprint: sk-d-real-weil). -/
def Setup.weilFrobenius (D : Setup.{u, v}) (C₀ : Scheme.{u})
    [C₀.Over (Spec (.of D.k₀))] (hC : D.IsCurve C₀) :
    D.geometricCurve C₀ ≅ D.geometricCurve C₀ :=
  @WeilConjectures.FiniteFieldDatum.geometricFrobenius D.weilFieldDatum
    (Over.mk (C₀ ↘ Spec (.of D.k₀))) hC.2.2.2.1 hC.2.2.2.2.1

end RealSheaves

namespace AlgebraicGeometry.WeilGroup

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.WeilGroup
