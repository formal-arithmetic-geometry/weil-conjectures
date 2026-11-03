/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import WeilConjectures.DeligneLaumon.CondensedWeil.ConstantExtensionPunctualWeights
public import WeilConjectures.DeligneLaumon.CondensedFibresExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex

/-! # Reality on actual condensed Weil modules

Source: latest blueprint, def-wf-iota-real.md, local characteristic factor and reality
paragraphs (blueprint: def-zl-condensed-weil-reality).

The formulas below apply directly to ordinary condensed modules. The landed
common-stage interface and its owning node remain unchanged. Quantifying over finite bases
expresses the determinant without choosing any basis or any finite-stage realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeil

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The canonical reverse characteristic polynomial of the actual scalar local
operator. Finite-dimensionality is a property of every constructible fibre, supplied
by lem-wf-condensed-fibres-exact, and no basis is part of the polynomial's data.
Source: latest blueprint def-wf-iota-real.md, displayed P_x(T)
(blueprint: def-zl-condensed-weil-reality). -/
def localFactor (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    [FiniteDimensional (PadicAlgCl l) (closedFiber D l X₀ M x i hi)] :
    Polynomial (PadicAlgCl l) :=
  (closedOperator D l X₀ M x i hi).hom.charpolyRev

/-- The local determinant in any finite basis of the actual condensed scalar fibre.
Source: latest blueprint def-wf-iota-real.md, displayed P_x(T)
(blueprint: def-zl-condensed-weil-reality). -/
def localFactorInBasis (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (n : ℕ) (b : Module.Basis (Fin n) (PadicAlgCl l) (closedFiber D l X₀ M x i hi)) :
    Polynomial (PadicAlgCl l) :=
  (LinearMap.toMatrix b b (closedOperator D l X₀ M x i hi).hom).charpoly.reverse

/-- Reality means every coefficient of every local determinant is real. For the
constructible modules under discussion the fibres have finite bases. Using all such
bases makes the definition independent of any choice, including rank zero.
Source: latest blueprint def-wf-iota-real.md, reality paragraph
(blueprint: def-zl-condensed-weil-reality). -/
def Real (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (n : ℕ) (b : Module.Basis (Fin n) (PadicAlgCl l) (closedFiber D l X₀ M x i hi))
    (j : ℕ),
    (iota ((localFactorInBasis D l X₀ M x i hi n b).coeff j)).im = 0

end WeilConjectures.CondensedWeil
