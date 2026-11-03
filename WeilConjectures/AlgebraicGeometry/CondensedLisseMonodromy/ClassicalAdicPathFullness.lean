/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseRepresentations
public import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverLift
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.Fibre.FibreFunctorBasepointTransportData
public import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-! # Descent of classical path-compatible fibre maps

Source: the latest blueprint's lisse representation theorem and Weil II (1.1.1).
(blueprint: lem-a1-classical-adic-path-fullness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedLisseMonodromy

/-- A family of linear maps commuting with finite etale paths descends to a
morphism of classical lisse algebraic-coefficient sheaves.
Source: `cor-galois-lisse-representations` (1)--(2), the full faithfulness argument
in `thm-lisse-qlbar-representations` (3), and Weil II (1.1.1) b)--d).
(blueprint: lem-a1-classical-adic-path-fullness).

Proof in words. Choose a geometric point x and its profinite fundamental group G.
The classical Galois correspondence gives an equivalence eA to the full
subcategory of continuous algebraic-coefficient representations, with a natural
underlying-fibre isomorphism tauA. Its G-action agrees with the given normalized
path action. To check this assertion, at each finite level compare the
underlying-set stalk isomorphism of the Galois correspondence with
pathUnderlyingStalk. Both send every module germ to the same set germ; joint
surjectivity of germs makes them equal. The finite-cover/FLC equivalence
identifies the finite fundamental-group automorphism with c.gamma(g). The two
integral evaluation formulas then give equality after every limit projection,
so the two integral actions agree. The rational evaluation formula determines
the rational action on pure tensors. The correspondence's algebraic model
scalar-extension comparison is equivariant and has the same pure-tensor fibre
formula, so it gives agreement at algebraic coefficients. Every localized
algebraic object is the image of its underlying coefficient pair, hence this
covers A and B.

Apply the assumed path square to loops at x. After conjugating by tauA, the
linear map a(x) therefore commutes with every G-action. It is a morphism of
representations, so fullness of eA supplies a sheaf morphism f with fibre a(x).
At any other geometric point y, connectedness gives a finite etale fibre path
from x to y. The assumed square for a and naturality of the path family for f
have the same source map a(x). Cancel the invertible path on A to obtain
f_y = a(y). This proves the assertion simultaneously for every field and point.
The zero sheaf causes no exception; no invertibility of the given maps is used. -/
theorem classical_adic_path_full (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    [ConnectedSpace X] [IsNoetherian X] [X.IsSeparated]
    [∀ z : X, Invertible (l : X.residueField z)]
    (P : AdicFibrePathTransport l X (Coeff.{u} l))
    (A B : LisseAlgebraicSheaf l X (Coeff.{u} l))
    (a : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).obj A ⟶
        (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).obj B)
    (ha : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
      (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω') ⟶ X)
      (τ : FiniteEtale.fiber x ≅ FiniteEtale.fiber y),
      (P.algebraic.map x y (flcPath τ)).hom.app A ≫ a Ω' y =
        a Ω x ≫ (P.algebraic.map x y (flcPath τ)).hom.app B) :
    ∃ f : A ⟶ B, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      (lisseAlgebraicFiberFunctor l X x (Coeff.{u} l)).map f = a Ω x := by sorry

end AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
