# AlgebraicGeometry.Etale.SfDiagonalKernel.unit

## Reason

The two independent bridge lemmas need the canonical kernel maps, while the triangle
assembly imports both lemmas. Extract the data to avoid a circular import and duplicate
constructions. Seven declarations, including their bodies and docstrings, move verbatim to
SfSupportedDiagonalData. The unit is reassociated into named canonical insertion and
comparison factors, avoiding an expensive component-factorization type check. All eight
are publicly re-exported from the original module.

## Old

In lean/Sheaf/AlgebraicGeometry/SfDiagonalKernelIntegrals.lean:

```lean
/-- The first-coordinate proper exchange, with exactly the flipped Cartesian square.
Source: thm-amb-p1-adjunction.proof.md, first triangle. -/
def exchangeFirst :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙ CoordinateTrace.pull A f ≅
      CoordinateTrace.pull A (pullback.snd f f) ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f f).flip
  asIso (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f f).flip)

/-- The canonical identification of the two pullbacks of a coefficient from the base.
Source: thm-amb-p1-adjunction.proof.md, common coefficient in the second triangle. -/
def coordinate {B : DerivedCategoryModule A X} (L : DerivedCategoryModule A Y)
    (e : B ≅ (CoordinateTrace.pull A f).obj L) :
    (CoordinateTrace.pull A (pullback.fst f f)).obj B ≅
      (CoordinateTrace.pull A (pullback.snd f f)).obj B :=
  (CoordinateTrace.pull A (pullback.fst f f)).mapIso e ≪≫
    CoordinateTrace.coordinate A f L ≪≫
      (CoordinateTrace.pull A (pullback.snd f f)).mapIso e.symm

/-- The source identification for integration along the first projection.
Source: thm-amb-p1-adjunction.proof.md, alpha_1 for p_1 Delta = id. -/
def diagonalFirst :
    𝟭 (DerivedCategoryModule A X) ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (TraceDiagonalDatum.diagonal f) ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f) :=
  let h := TraceDiagonalDatum.diagonal_fst f
  have : HasCompactification (TraceDiagonalDatum.diagonal f ≫ pullback.fst f f) := by
    rw [h]
    infer_instance
  have : QuasiCompact (TraceDiagonalDatum.diagonal f ≫ pullback.fst f f) := by
    rw [h]
    infer_instance
  (rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).symm ≪≫
    rightDerivedLowerShriekCongrIso A h.symm ≪≫
      rightDerivedLowerShriekCompIso A (TraceDiagonalDatum.diagonal f) (pullback.fst f f)

variable {f} {B : DerivedCategoryModule A X} (d : TraceDiagonalDatum A f B)

/-- The first trace is obtained from the original trace by inverse proper exchange.
Source: thm-amb-p1-adjunction.proof.md, trace base change in the first coordinate. -/
def traceFirst :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f)).obj
      ((CoordinateTrace.pull A (pullback.snd f f)).obj B) ⟶
        derivedTensorUnit (ModuleCat.{u + 1} A) X :=
  (exchangeFirst A f).inv.app B ≫
    (CoordinateTrace.pull A f).map d.trace ≫
      (leftDerivedUpperStarDerivedTensorUnitIso f).hom

/-- The second trace uses the same original trace and the other proper exchange.
Source: thm-amb-p1-adjunction.proof.md, trace base change in the second coordinate. -/
def traceSecond (L : DerivedCategoryModule A Y)
    (e : B ≅ (CoordinateTrace.pull A f).obj L) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).obj
      ((CoordinateTrace.pull A (pullback.snd f f)).obj B) ⟶
        derivedTensorUnit (ModuleCat.{u + 1} A) X :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).map
      (coordinate A f L e).inv ≫
    (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app B ≫
      (CoordinateTrace.pull A f).map d.trace ≫
        (leftDerivedUpperStarDerivedTensorUnitIso f).hom

/-- Both coordinate integrals of the same diagonal class are one. No adjunction or
triangle identity is included in this property.
Source: thm-amb-p1-adjunction.proof.md, the two diagonal integrals. -/
def Integrals (L : DerivedCategoryModule A Y)
    (e : B ≅ (CoordinateTrace.pull A f).obj L) : Prop :=
  ((diagonalFirst A f).hom.app (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f)).map
        d.diagonalClass ≫ traceFirst A d =
      𝟙 (derivedTensorUnit (ModuleCat.{u + 1} A) X)) ∧
    ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app
        (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).map
        d.diagonalClass ≫ traceSecond A d L e =
      𝟙 (derivedTensorUnit (ModuleCat.{u + 1} A) X))

/-- The canonical diagonal unit in the factor order B tensor f* K.
Source: thm-amb-p1-adjunction.proof.md, diagonal-kernel construction of eta. -/
def unit :
    𝟭 (DerivedCategoryModule A X) ⟶
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B) :=
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let P := CoordinateTrace.pull A f
  let G := derivedTensorRight (ModuleCat.{u + 1} A) X B
  let η : 𝟭 (DerivedCategoryModule A X) ⟶ F ⋙ (P ⋙ G) :=
    (TraceDiagonalDatum.idIsoDiagonalSnd f).hom ≫
      Functor.whiskerRight (TraceDiagonalDatum.diagonalIso f).hom
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)) ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (CoordinateTrace.pull A (pullback.fst f f))
          ((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map d.diagonalClass ≫
            ((derivedTensorSymmetry (ModuleCat.{u + 1} A) (pullback f f)).app _).hom))
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)) ≫
      (TraceDiagonalDatum.sndProjectionIso f B).hom
  η ≫ Functor.whiskerLeft F
    (Functor.isoWhiskerLeft P
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app B).symm).hom

/-- The inverse canonical projection followed by trace tensor identity and left unitor.
Source: thm-amb-p1-adjunction.proof.md, G7. -/
def counit :
    (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B) ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⟶
        𝟭 (DerivedCategoryModule A Y) :=
  (projectionIso A f B).inv ≫
    (derivedTensor (ModuleCat.{u + 1} A) Y).map d.trace ≫
      (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) Y).hom

```

## New

The seven definitions other than unit, reproduced above, move verbatim into
lean/Sheaf/AlgebraicGeometry/SfSupportedDiagonalData.lean. The unit signature is unchanged;
its new body is:

```lean
  SupportedTrace.insertion A f d.diagonalClass ≫
    (SupportedTrace.comparisonIso A f B).hom
```

insertion is precisely the first three factors of the old unit. comparisonIso is the old
sndProjectionIso followed by isoWhiskerLeft F (isoWhiskerLeft P symmetry.symm).
Functor.isoWhiskerLeft_hom identifies its hom with the final whiskered symmetry of the
old unit. Associativity of natural-transformation composition gives the same map as before.
comparison is the component of comparisonIso. insertionApp is the component of insertion,
with its source and kernel target explicit. No mathematical map is replaced.

The new proved component lemmas unit_app_eq and counit_app_eq expose these
composites without unfolding the concrete derived functors in the triangle proof. Their
local instance priorities and reducibility attributes are scoped to their section and
are not exported to consumers.

The original module publicly imports SfSupportedDiagonalData and retains both original
public imports. The data module uses the same two original public imports, preserving
the elaboration environment of the extracted definitions. All existing signatures and
attributes are unchanged. Additional data
name the outside-first projection, partial unit, final kernel comparison and common
coefficient comparison used by the two independent bridge statements. A right-unitor
API over general coefficients explicitly names derivedTensorUnit in its domain; its
body is the existing canonical derivedTensorRightUnitor.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SfP1IntegralTransportData | unclaimed | Same kernel maps; supportedMap extracted separately to meet the compile limit. |
| Sheaf.AlgebraicGeometry.SfCompactificationKernelTransport | unclaimed | Same canonical maps through public re-export; no edits. |
| Sheaf.AlgebraicGeometry.SfP1CoordinateIntegrals | unclaimed | Same canonical maps through public re-export; no edits. |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransport | unclaimed | Same canonical maps through public re-export; no edits. |
| Sheaf.SmoothPurity.FiniteP1CoordinateKernel | unclaimed | Same canonical maps through public re-export; no edits. |
| Sheaf.SmoothPurity.FiniteP1AdjunctionOfIntegrals | unclaimed | Same canonical maps through public re-export; no edits. |
| Sheaf.AlgebraicGeometry.SfAffineBaseP1TraceAdjunction | unclaimed | Same canonical maps through public re-export; no edits. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | Different ProEtale namespace; textual match only; unaffected. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Different ProEtale namespace; textual match only; unaffected. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | unclaimed | Different ProEtale namespace; textual match only; unaffected. |

The first five rows are every current direct importer. The next two are indirect consumers
using the fully qualified original names. The last three are additional textual exchangeFirst
users reported by tools/downstream.py --uses; their exchangeFirst belongs to
AlgebraicGeometry.ProEtale.FiniteProjectionExchange. The item module itself now imports
the data.
The downstream script matches the last name segment, so its unit search also matches
unrelated adjunction units throughout the library. The qualified-name and namespace audit
finds unit/counit uses in SfCompactificationKernelTransport, FiniteP1AdjunctionOfIntegrals,
and SfAffineBaseP1TraceAdjunction, all listed above.
The direct importers are checked against the extracted declarations before delivery; unchanged
sandbox copies are removed afterward. The independent reader must review the unit definition
change using the factor-by-factor identification above and confirm that dependent target
statements retain their meaning. None of the five Challenge.lean target texts mentions this
unit, and no target signature changes. The triangle statement continues to use precisely
the canonical unit.

Validation: the complete 16-file compilation passed after the extractions, including
all direct importers and additional unit/counit users. No consumer edits were required;
only the six intended delivery source files remain in the sandbox.

## Status

landed 20261026T222540-L-666663 2026-10-26 (merge of deliver/A4/Sheaf.AlgebraicGeometry.SfDiagonalKernelIntegrals)
