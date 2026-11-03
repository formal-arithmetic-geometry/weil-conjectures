/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ComparisonBrownExplicit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek

/-! # Open scalar coordinate calculations -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NormalizedUnitTrace
open Scheme CondensedRing PurityTransport ExplicitSmoothComparison

private local instance openScalarSourceUnitBundledComm
    (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell) :
    IsCommMonObj (CommMon.toMon (c.bundled.{u} ell)).X := by
  change IsCommMonObj (c.obj ell)
  infer_instance

/-- The zero-line scalar source comparison respects the derived coefficient unit.
Source: smooth purity transport, Step 4, and open normalization, Step 5
(blueprint: lem-pur-open-scalar-source-unit).

Proof: first compare the chosen ordinary scalar monoidal structure with the native
one. Precompose the two oplax tensorators with the balanced tensor projection and
extension unit; their balanced formulas agree. The extension/restriction Hom
bijection and the epimorphic projection cancel these precompositions. Left
unitality determines the oplax unit, and inverse uniqueness determines the lax
maps, so the structures agree. The retained power normalization at zero therefore
identifies p.power 0 with the ordinary scalar unit.

Evaluate the derived scalar adjunction unit on the single regular module. Its
composition with restriction of the derived-functor counit is the localized
ordinary adjunction unit. Compose with the ordinary oplax unit, whose adjunct is
the restriction unit. Exact restriction commutes with the single functor. These
equalities identify scalarLineZero at zero with the derived monoidal unit,
through the specified single/unit comparisons. The zero commShift axiom removes
the shifts in scalarLineMap and zeroLine.

For the scalar/pullback map, transpose through scalar extension/restriction at X.
Exact restriction/single coherence reduces its unit equation to the ordinary
coefficient-pullback square on regular modules; this square is naturality of
coefficientMap with condensedPullbackHom. Transpose back and use the preceding
unit identifications. Finally expand sourceScalar and unitSource, move the two
unit maps by tensorator naturality, and apply left unitality to its inverse
tensorator. The resulting composite is the scalar unit at X. Only specified
isomorphisms are cancelled, including when X or Y is empty. -/
theorem openScalarSourceUnit
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left]
    (ha : (Coefficient.integers : Coefficient ell).integralMap ell ≫
      (integralClosureMap ell).hom.hom = (Coefficient.closure : Coefficient ell).integralMap ell)
    (p : ScalarLineCoordinates ell (integralClosureMap ell) ha X.left) :
    (scalarSixChange (integralClosureMap ell) X.left).map
        ((unitSource ell .integers j.left 0 ≪≫ zeroLine ell .integers X.left).inv) ≫
      sourceScalar ell (integralClosureMap ell) j.left 0 ha p (𝟙_ _) ≫
      ((Coefficient.closure : Coefficient ell).smoothSource ell j.left 0).map
        (scalarUnitIso ell Y.left).hom ≫
      (unitSource ell .closure j.left 0 ≪≫ zeroLine ell .closure X.left).hom =
        (scalarUnitIso ell X.left).hom := by
  sorry

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
