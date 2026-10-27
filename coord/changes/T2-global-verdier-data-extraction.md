# GlobalVerdierDuality construction data

## Reason

The original file declares the data its theorem must construct. A separate identity-normalization
lemma needs that same data without importing the theorem and creating a cycle. Move the original
public declarations into `Sheaf.Paper.GlobalVerdierDualityData`, and re-export them from the
original module. This is a dependency extraction, not a change to any existing signature, body,
universe or mathematical meaning. New records `StageMaps` and `NormalizedData` distinguish
construction of the natural transformation from its invertibility.

## Old

The following original block is declared in `Sheaf.Paper.GlobalVerdierDuality`:

```lean
/-- The identity adjunction, with its existing exact and shift structures. Using this
operation makes the point dual literally internal Hom into the coefficient unit.
Source: blueprint global-duality proof step 3, identity normalization
(blueprint: sk-thm-sf-global-duality). -/
def identityOperation (T : Scheme.{u}) (s : Stage.{u} l) : Operation.{u, u} l Ω T T s where
  F := 𝟭 _
  G := 𝟭 _
  adjunction := Adjunction.id
  leftExact := inferInstance
  rightExact := inferInstance
  unitShift := inferInstance
  counitShift := inferInstance

section Stage
variable {X S : Scheme.{u}} {s : Stage.{u} l}
  {F : Operation.{u, u} l Ω X S s} {unit : C.{u, u} l Ω S s}

/-- The stage data specialized to the identity of the point and the same structure
morphism on both sides. This is the existing StageData, without a new duality notion.
Source: blueprint global-duality proof steps 2--3
(blueprint: sk-thm-sf-global-duality). -/
abbrev Data (F : Operation.{u, u} l Ω X S s) (unit : C.{u, u} l Ω S s) :=
  StageData l Ω s F (identityOperation l Ω S s) F unit

/-- Evaluation identifies Hom from the tensor unit to omega with omega. This is the
actual evaluation map, with the right unitor inserted, before asserting invertibility.
Source: blueprint global-duality proof step 6
(blueprint: sk-thm-sf-global-duality). -/
def unitEvaluation (d : Data l Ω F unit) :
    (d.dualX l Ω).obj (op d.closedX.monoidal.tensorUnit) ⟶ F.G.obj unit :=
  (d.closedX.monoidal.rightUnitor _).inv ≫
    d.closedX.evaluation d.closedX.monoidal.tensorUnit (F.G.obj unit)

/-- The inverse candidate is the transpose of the right unitor of omega.
Source: blueprint global-duality proof step 6, tensor/Hom triangles
(blueprint: sk-thm-sf-global-duality). -/
def unitCoevaluation (d : Data l Ω F unit) :
    F.G.obj unit ⟶ (d.dualX l Ω).obj (op d.closedX.monoidal.tensorUnit) :=
  d.closedX.transpose _ d.closedX.monoidal.tensorUnit (F.G.obj unit)
    (d.closedX.monoidal.rightUnitor _).hom

/-- The natural isomorphism has the evaluation/projection transpose as its components;
its constant specialization is the same component followed by evaluation of Hom(unit,-).
All data here are conclusions. The point coefficient dual is `d.dualY`, since its
exceptional operation is the literal identity adjunction.
Source: blueprint global-duality statement, naturality, shifts and final clause
(blueprint: sk-thm-sf-global-duality). -/
structure Conclusion (d : Data l Ω F unit) where
  exchange : StageConclusion l Ω d
  dualizing : d.dualizing = Iso.refl (F.G.obj unit)
  unitIso : (d.dualX l Ω).obj (op d.closedX.monoidal.tensorUnit) ≅ F.G.obj unit
  evaluation : unitIso.hom = unitEvaluation l Ω d
  coevaluation : unitIso.inv = unitCoevaluation l Ω d
  constant : (d.dualY l Ω).obj (op (F.F.obj d.closedX.monoidal.tensorUnit)) ≅
    d.star.obj (F.G.obj unit)
  constant_hom : constant.hom =
    exchange.epsilon.hom.app (op d.closedX.monoidal.tensorUnit) ≫ d.star.map unitIso.hom

end Stage

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X S : Scheme.{u}} (f : X ⟶ S)
  [X.Over (Spec (.of D.k))] [S.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (S ↘ Spec (.of D.k))] [QuasiCompact (S ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (A : System.{u, u} l Ω D hl (f := f)) (c : Compactification f)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A global-duality package uses the existing exact finite-Tor categories and the
published compact-support system. Ring realizations fix internal Hom, evaluation,
ordinary direct image, projection and signed shifts on the actual small sites.
Coefficient comparisons below include nonflat finite reduction, completed scalar
extension, rationalization and common finite stages. They are conclusions, never
extra assumptions on X or K.
Source: blueprint global-duality statement and proof steps 1--6
(blueprint: sk-thm-sf-global-duality). -/
structure Package where
  unit (s : Stage.{u} l) : C.{u, u} l Ω S s
  stage (s : Stage.{u} l) : Data l Ω (A.ring.operation c s) (unit s)
  conclusion (s : Stage.{u} l) : Conclusion l Ω (stage s)
  ring (s : RingStage.{u} l) : RingRealization l Ω f s (stage (s.stage l))
  projection (s : RingStage.{u} l) :
    RingProjection l Ω c s (ring s) (A.ring.left c s)
  ringShifts (s : RingStage.{u} l) :
    RingShiftRealization l Ω (ring s) (conclusion (s.stage l)).exchange
  unitX (s : RingStage.{u} l) :
    (s.inclusion l Ω X).obj (stage (s.stage l)).closedX.monoidal.tensorUnit ≅ ringUnit l X s
  unitY (s : Stage.{u} l) : (stage s).closedY.monoidal.tensorUnit ≅ unit s
  unitX_normalized (s : RingStage.{u} l) (K : C.{u, u} l Ω X (s.stage l)) :
    (s.inclusion l Ω X).map ((stage (s.stage l)).closedX.monoidal.rightUnitor K).hom =
      (ring s).tensorX.hom.app (K, (stage (s.stage l)).closedX.monoidal.tensorUnit) ≫
        (ring s).modelX.closed.tensor.map (Prod.mkHom (𝟙 _)
          ((unitX s).hom ≫ (ring s).modelX.unitIso.inv)) ≫
        ((ring s).modelX.closed.monoidal.rightUnitor ((s.inclusion l Ω X).obj K)).hom
  unitY_normalized (s : RingStage.{u} l) (K : C.{u, u} l Ω S (s.stage l)) :
    (s.inclusion l Ω S).map ((stage (s.stage l)).closedY.monoidal.rightUnitor K).hom =
      (ring s).tensorY.hom.app (K, (stage (s.stage l)).closedY.monoidal.tensorUnit) ≫
        (ring s).modelY.closed.tensor.map (Prod.mkHom (𝟙 _)
          ((s.inclusion l Ω S).map (unitY (s.stage l)).hom ≫
            (ring s).unitIso.hom ≫ (ring s).modelY.unitIso.inv)) ≫
        ((ring s).modelY.closed.monoidal.rightUnitor ((s.inclusion l Ω S).obj K)).hom
  ringScalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :
    ∃ b : StageScalar l Ω (stage (s.stage l)) (stage (t.stage l))
        (A.ring.scalar a ha true).functor (A.ring.scalar a ha false).functor
        (A.ring.scalar a ha false).functor,
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (s.stage l)).exchange
        (conclusion (t.stage l)).exchange b) ∧
      (b.exceptional.q l Ω) = (A.ring.comparison c a ha).q ∧
      (t.inclusion l Ω S).map b.unit.hom ≫ (ring t).unitIso.hom =
        (A.ring.scalar a ha false).realization.hom.app (unit (s.stage l)) ≫
          (pbcDerivedExtend (a.map S)).map (ring s).unitIso.hom ≫ ringUnitScalar l a S
  rationalization (E : FieldStage.{u} l) :
    ∃ b : StageScalar l Ω (stage (.integral E)) (stage (.rational E))
        (ConstructibleExceptionalCoefficients.rationalization.{u, u} l Ω E X)
        (ConstructibleExceptionalCoefficients.rationalization.{u, u} l Ω E S)
        (ConstructibleExceptionalCoefficients.rationalization.{u, u} l Ω E S),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.integral E)).exchange
        (conclusion (.rational E)).exchange b) ∧
      b.exceptional = A.fields.rationalizationComparison c E
  rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    ∃ b : StageScalar l Ω (stage (.rational E)) (stage (.rational L))
        (ConstructibleExceptionalCoefficients.rationalScalar.{u, u} l Ω E L i X)
        (ConstructibleExceptionalCoefficients.rationalScalar.{u, u} l Ω E L i S)
        (ConstructibleExceptionalCoefficients.rationalScalar.{u, u} l Ω E L i S),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.rational E)).exchange
        (conclusion (.rational L)).exchange b) ∧
      b.exceptional = A.fields.rationalComparison c E L i
  common (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ∃ b : StageScalar l Ω (stage (.rational (commonField.{u, u} l Ω i))) (stage .closed)
        (commonInclusion.{u, u} l Ω X i) (commonInclusion.{u, u} l Ω S i)
        (commonInclusion.{u, u} l Ω S i),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.rational (commonField.{u, u} l Ω i))).exchange
        (conclusion .closed).exchange b) ∧
      b.exceptional = A.common.commonComparison c i

end Geometry

/-- Both geometric alternatives are retained, including the nonproper descended case.
An isomorphism in Over identifies the structure map, as well as the underlying scheme.
Source: blueprint global-duality statement, second sentence
(blueprint: sk-thm-sf-global-duality). -/
def GeometricAlternative (D : FiniteFieldDatum.{u}) (X : Over (Spec (.of D.k))) : Prop :=
  IsProper X.hom ∨
    ∃ (X₀ : Over (Spec (.of D.k₀))) (_ : Smooth X₀.hom) (_ : IsSeparated X₀.hom)
      (_ : LocallyOfFiniteType X₀.hom) (_ : QuasiCompact X₀.hom)
      (_ : GeometricallyConnected X₀.hom), Nonempty (X ≅ D.geometricFiber X₀)

/-- State the assertion at the geometric point with its identity structure morphism.
The quantifier ranges over the already constructed normalized systems; it is not an
existence assumption, and the theorem is independent of the compactification chosen.
Source: blueprint global-duality proof steps 1--3
(blueprint: sk-thm-sf-global-duality). -/
def Assertion (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] : Prop :=
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  ∀ (A : System.{u, u} l Ω D hl (f := X ↘ Spec (.of D.k)))
    (c : Compactification (X ↘ Spec (.of D.k))),
    Nonempty (Package l Ω D hl (X ↘ Spec (.of D.k)) A c)

```

## New

The identical original block is declared in `Sheaf.Paper.GlobalVerdierDualityData` with the same
namespace and public visibility. The original module publicly imports the data module. The new
records and the proved `StageMaps.toConclusion` constructor are attached to
`def-sf-global-normalized-construction`. No original definition or theorem signature changes.

## Users

`tools/downstream.py Sheaf.Paper.GlobalVerdierDuality --uses identityOperation Data unitEvaluation
unitCoevaluation Conclusion Package GeometricAlternative Assertion` reports zero downstream
modules in the current source snapshot. Quarantined/import-planned parents retain the same fully
qualified declarations and public imports. No target meaning changes and no adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.GlobalVerdierDuality | T2 | Publicly re-exports the identical declarations; proves the theorem from identity normalization. |
| Sheaf.Paper.GlobalVerdierDualityData | T2, new | Holds the identical original data plus the new construction records. |
| Sheaf.Paper.GlobalIdentityNormalization | T2, new | Uses the construction records; states the separate normalization obligation. |

## Status

landed 20261025T101443-L-3695530 2026-10-25 (merge of deliver/T2/Sheaf.Paper.GlobalVerdierDuality)
