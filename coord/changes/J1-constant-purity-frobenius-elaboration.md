# WeilConjectures.ConstantPurityFrobenius.betaAtStage

## Reason

Restore the quarantined item from coord/rework.tsv. The archived betaAtStage
exhausts 200000 heartbeats while matching the rational exchange with the
common-stage coefficient comparison.

Give rationalBeta and betaAtStage their explicit existing endpoint types. Elaborate
the five original factors separately, with explicit geometric instances for the
coefficient-system projections. Transport the rational arrow along a proved equality
of the two published common-stage category structures before applying inclusion.
This equality is definitional, as in RationalSmoothPurityCanonical.commonCategory_eq;
the explicit cast avoids searching through the coefficient and derived-category
constructions. The original conjugation factors, normalizations, and theorem
statements are preserved. Local irreducibility limits unfolding during this definition;
no global imported attribute or timeout/heartbeat limit is changed.

## Old

```lean
def rationalBeta (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l)
    (K : sfRationalConstructibleCategory l
      E.carrier (D.geometricFiber X₀).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  (rationalDerivedPullback l E.carrier
      (D.geometricFrobenius Y₀).hom).map
    ((S.ring.rationalLeft (FrobeniusExchange.geometricCompactification D f₀ c₀)
      E).hom.app K) ≫
    eqToHom (congrArg (fun H ↦ H.obj K)
      (rationalExchange_endpoints D l hl Ω X₀ Y₀ f₀ c₀ S E).1.symm) ≫
    (FrobeniusExchange.frobeniusRational D l hl
      E.carrier f₀
      (FrobeniusExchange.frobeniusCompactModel D f₀ c₀)).app K ≫
    eqToHom (congrArg (fun H ↦ H.obj K)
      (rationalExchange_endpoints D l hl Ω X₀ Y₀ f₀ c₀ S E).2) ≫
    (S.ring.rationalLeft (FrobeniusExchange.geometricCompactification D f₀ c₀)
      E).inv.app
        ((rationalDerivedPullback l E.carrier
          (D.geometricFrobenius X₀).hom).obj K)

/-- Its common-stage component is explicitly conjugated by the prescribed
stage pullback and exceptional-coefficient comparisons.
Source: common-stage exchange convention and proof Step 4
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def betaAtStage (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (D.geometricFiber X₀).left) :=
  (targetFrobenius D l hl Ω Y₀).map
    ((S.common.commonComparison (FrobeniusExchange.geometricCompactification D f₀ c₀)
      L).q.inv.app K) ≫
    (sfWeilStagePullbackIdentification D l hl Y₀ Ω L
      ((operation D l hl Ω X₀ Y₀ f₀ c₀ S (.rational
        (ConstructibleExceptionalCoefficients.commonField l Ω L))).F.obj K)).hom ≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
      (rationalBeta D l hl Ω X₀ Y₀ f₀ c₀ S
        (ConstructibleExceptionalCoefficients.commonField l Ω L) K) ≫
    (S.common.commonComparison (FrobeniusExchange.geometricCompactification D f₀ c₀)
      L).q.hom.app
        ((sfWeilFrobeniusPullback D l hl X₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).obj K) ≫
    (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).F.map
      (sfWeilStagePullbackIdentification D l hl X₀ Ω L K).inv
```

## New

```lean
def rationalBeta (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l)
    (K : sfRationalConstructibleCategory l
      E.carrier (D.geometricFiber X₀).left) :
    (sfWeilFrobeniusPullback D l hl Y₀ E.carrier).obj
        ((operation D l hl Ω X₀ Y₀ f₀ c₀ S (.rational E)).F.obj K) ⟶
      (operation D l hl Ω X₀ Y₀ f₀ c₀ S (.rational E)).F.obj
        ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K) :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  (rationalDerivedPullback l E.carrier
      (D.geometricFrobenius Y₀).hom).map
    ((S.ring.rationalLeft (FrobeniusExchange.geometricCompactification D f₀ c₀)
      E).hom.app K) ≫
    eqToHom (congrArg (fun H ↦ H.obj K)
      (rationalExchange_endpoints D l hl Ω X₀ Y₀ f₀ c₀ S E).1.symm) ≫
    (FrobeniusExchange.frobeniusRational D l hl
      E.carrier f₀
      (FrobeniusExchange.frobeniusCompactModel D f₀ c₀)).app K ≫
    eqToHom (congrArg (fun H ↦ H.obj K)
      (rationalExchange_endpoints D l hl Ω X₀ Y₀ f₀ c₀ S E).2) ≫
    (S.ring.rationalLeft (FrobeniusExchange.geometricCompactification D f₀ c₀)
      E).inv.app
        ((rationalDerivedPullback l E.carrier
          (D.geometricFrobenius X₀).hom).obj K)

section StageComparison
attribute [local instance 2000] IntermediateField.algebra'
attribute [local irreducible] rationalBeta
  rationalDerivedPullback commonStageDerivedPullback
attribute [local irreducible] ScalarLocalization.category scalarReductionSourceDerived
  SheafOfModules.instCategory SheafOfModules.instAbelian
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Its common-stage component is explicitly conjugated by the prescribed
stage pullback and exceptional-coefficient comparisons.
Source: common-stage exchange convention and proof Step 4
(blueprint: lem-pur-constant-purity-frobenius-square). -/
def betaAtStage (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (D.geometricFiber X₀).left) :
    (targetFrobenius D l hl Ω Y₀).obj
        ((operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).F.obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)) ⟶
      (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).F.obj
        ((sourceFrobenius D l hl Ω X₀).obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)) :=
by
  let E := ConstructibleExceptionalCoefficients.commonField l Ω L
  let FX := sourceFrobenius D l hl Ω X₀
  let FY := targetFrobenius D l hl Ω Y₀
  let IY := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
    (Y := (D.geometricFiber Y₀).left) L
  let IX := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
    (Y := (D.geometricFiber X₀).left) L
  let R := (operation D l hl Ω X₀ Y₀ f₀ c₀ S (.rational E)).F
  let F := (operation D l hl Ω X₀ Y₀ f₀ c₀ S .closed).F
  let q := (@ConstructibleExceptionalCoefficients.CommonSystem.commonComparison
    l inferInstance Ω inferInstance inferInstance inferInstance D hl
    (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
    (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
    xft xqc yft yqc fover fsep fft fqc
    (@ConstructibleExceptionalCoefficients.System.ring
      l inferInstance Ω inferInstance inferInstance inferInstance D hl
      (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
      (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
      xft xqc yft yqc fover fsep fft fqc S)
    (@ConstructibleExceptionalCoefficients.System.fields
      l inferInstance Ω inferInstance inferInstance inferInstance D hl
      (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
      (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
      xft xqc yft yqc fover fsep fft fqc S)
    (@ConstructibleExceptionalCoefficients.System.common
      l inferInstance Ω inferInstance inferInstance inferInstance D hl
      (D.geometricFiber X₀).left (D.geometricFiber Y₀).left
      (FrobeniusExchange.fiberMap D f₀) inferInstance inferInstance
      xft xqc yft yqc fover fsep fft fqc S)
    (FrobeniusExchange.geometricCompactification D f₀ c₀) L).q
  let a : FY.obj (F.obj (IX.obj K)) ⟶ FY.obj (IY.obj (R.obj K)) :=
    FY.map (q.inv.app K)
  let b : FY.obj (IY.obj (R.obj K)) ⟶
      IY.obj ((sfWeilFrobeniusPullback D l hl Y₀ E.carrier).obj (R.obj K)) :=
    (sfWeilStagePullbackIdentification D l hl Y₀ Ω L (R.obj K)).hom
  have hcat : ConstructibleExceptionalCoefficients.category l Ω
      (D.geometricFiber Y₀).left (.rational E) =
      GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω
        (D.geometricFiber Y₀).left L := by
    unfold ConstructibleExceptionalCoefficients.category
      GeneralAlgebraicallyClosedCoefficients.stageCategory
    unfold ScalarLocalization.category
    rfl
  let r := rationalBeta D l hl Ω X₀ Y₀ f₀ c₀ S E K
  let A := (sfWeilFrobeniusPullback D l hl Y₀ E.carrier).obj (R.obj K)
  let B := R.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)
  let r' := Eq.mp (congrArg (fun cat : Category.{u + 2}
      (sfRationalConstructibleCategory l E.carrier (D.geometricFiber Y₀).left) ↦
      @Quiver.Hom _ cat.toQuiver A B) hcat) r
  let c : IY.obj ((sfWeilFrobeniusPullback D l hl Y₀ E.carrier).obj (R.obj K)) ⟶
      IY.obj (R.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)) :=
    IY.map r'
  let d : IY.obj (R.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)) ⟶
      F.obj (IX.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)) :=
    q.hom.app ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)
  let e : F.obj (IX.obj ((sfWeilFrobeniusPullback D l hl X₀ E.carrier).obj K)) ⟶
      F.obj (FX.obj (IX.obj K)) :=
    F.map (sfWeilStagePullbackIdentification D l hl X₀ Ω L K).inv
  exact a ≫ b ≫ c ≫ d ≫ e

end StageComparison
```

## Users

`tools/downstream.py Sheaf.Paper.ConstantPurityFrobeniusSquare --allow-missing
--uses betaAtStage` reports zero current downstream modules. A search of both
lean/ and quarantine/ finds no external Lean user of the namespace. The item's
DAG attachment and parent dependencies are retained. This restoration does not
withdraw the item or assert that its mathematics is unused.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | J1 | Restored; explicit endpoints, instances and category transport preserve the original maps. |

The file-local attributes do not change imported attributes. No consumer adaptation
or target statement change is required.

## Status

landed 20261026T023327-L-544013 2026-10-26 (merge of deliver/J1/Sheaf.Paper.ConstantPurityFrobeniusSquare)
