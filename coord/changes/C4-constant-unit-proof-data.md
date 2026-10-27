# WeilConjectures.ConstantPurityFrobenius constant-unit constructors

## Reason

Move the normalized constant-unit constructors into the new proof prerequisite
Sheaf.Paper.CommonConstantUnitFrobenius. The separate constant-unit Frobenius
coherence theorem can then be imported by the purity-square item without a cycle.
The constructors retain their names, signatures, attributes and bodies verbatim.
The item publicly imports their new module, preserving its exported interface.
No mathematical target or definition changes meaning.

## Old

In Sheaf.Paper.ConstantPurityFrobeniusSquare, within its existing namespace:

```lean
section Unit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The constant-section unit into completed pullback is determined by its finite
unit generators and zero shifted-cone component, for an arbitrary scheme morphism.
Source: constant comparison in the six-step proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square).
Proof: finite extension of scalars takes the regular module to the regular module.
Apply its adjunction unit to 1 tensor 1 at every quotient. These elements commute
with the actual quotient maps; their product is killed by 1-shift. The mapping
cocone lift with second component zero gives the displayed map. A module map out
of the regular sheaf is determined by the image of 1 on the terminal site object;
restriction determines the image on every other object. The two cone projections
then give uniqueness in every degree. This also covers the empty scheme. -/
theorem chainUnit_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E f).obj
          (constantWeilIntegralComplex l E Y),
      (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E f)).f 0 ≫
          (Pi.π (fun m ↦ (constantWeilPullbackTower l E f).obj (op m)) n).f 0).val.app
            (op ((proEtaleBaseChange f).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange f).obj V)) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y n V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E f)).v i (i - 1) (by omega) = 0) := by
  exact ConstantGeometricStalkUnit.integralChainUnit_existsUnique l E f

/-- The uniquely specified whole-tower unit, with its fixed zero cone coordinate.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def chainUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (chainUnit_existsUnique l E f).exists.choose

/-- The strict unit is a quasi-isomorphism before rationalization.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square).
Proof: finite unit multiplication identifies the whole pullback tower with the
quotient coefficient tower of X, including its actual quotient transitions.
Those transitions are surjective. The Roos complex therefore has only degree-zero
cohomology, equal to the completed coefficient sheaf. The normalized chain unit
induces this identity and is consequently a quasi-isomorphism. -/
theorem chainUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (DerivedCategory.Q.map (chainUnit l E f)) := by
  simpa only [chainUnit, ConstantGeometricStalkUnit.integralChainUnit] using
    ConstantGeometricStalkUnit.integralChainUnit_isIso l E f

/-- The usual completed pullback-of-unit identification, using the actual good
representative comparison followed by the inverse normalized whole-tower unit.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def integralUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralDerivedPullback l E f).obj (integralConstantCoefficientObject l E Y) ≅
      integralConstantCoefficientObject l E X :=
  (integralDerivedPullbackComparison l E f).app (constantWeilIntegralGood l E Y) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (chainUnit l E f))
      (chainUnit_isIso l E f)).symm

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- Rationalize that particular unit map, retaining the prescribed object comparison.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def rationalUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (rationalDerivedPullback l E f).obj (constantWeilRationalObject l E D hl Y) ≅
      constantWeilRationalObject l E D hl X :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 _) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (integralUnit l E f))
end Unit

section CommonUnit
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The coefficient unit as its literal least-stage object, without a Weil structure.
Source: canonical constant-pair convention, clause 5
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def unit (T : Scheme.{u}) : generalAlgebraicallyClosedConstructibleCategory l Ω T :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion (Padic.finiteCoefficientBase l Ω)).obj
    (constantWeilRationalObject l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
      D hl T)

/-- Common-stage unit comparison: represent the rationalized strict unit at Q_l.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def commonUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (commonStageDerivedPullback l Ω f).obj (unit D l hl Ω Y) ≅ unit D l hl Ω X :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion (Padic.finiteCoefficientBase l Ω)).mapIso
      (rationalUnit l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
        D hl f)
end CommonUnit

```

## New

Exactly the same text occurs in Sheaf.Paper.CommonConstantUnitFrobenius, within
the same namespace and noncomputable public section. The original module has:

```lean
public import Sheaf.Paper.CommonConstantUnitFrobenius
```

The new prerequisite adds commonUnit_frobenius, whose statement concerns only
constant units and pullback; no purity or exceptional operations occur in it.
All imported constructor data remain the actual strict units and their recorded
rational/common-stage images.

## Users

The direct-import scan finds no importer of the item module. downstream.py
reports only the item itself as a textual user of commonUnit. All seven moved
names remain available to every importer of the item through the public import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | C4 | Publicly reexports unchanged constructors. |
| Sheaf.Paper.CommonConstantUnitFrobenius | C4 (new) | Owns the unchanged constructors and the separate coherence statement. |

## Node records

The moved constructors are now owned by lem-pur-common-constant-unit-frobenius.
Square, the statement of lem-pur-constant-purity-frobenius-square, uses `unit`
and `commonUnit`. That node's stmt_deps therefore gain
lem-pur-common-constant-unit-frobenius; its statement text is unchanged. Its
former proof step 1 (the chain-unit construction) and its proof_dep
lem-zl-constant-geometric-stalk-unit moved with the constructors to the new node
(reviewer fix, 2026-10-27).

## Status

landed 20261027T034621-L-3666357 2026-10-27 (merge of deliver/C4/Sheaf.Paper.ConstantPurityFrobeniusSquare)
