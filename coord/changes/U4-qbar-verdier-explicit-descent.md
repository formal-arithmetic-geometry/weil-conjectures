# WeilConjectures.CoefQbarVerdier.core_descent

## Reason

Repair C-73b31 restores the item from its current quarantine to the original
lean/ path on current sheaf-dag. The retained reviewed implementation matched
returned head 73b31bacd. Its five original public declarations and core node
attachment remain present; CoreProperties matches the archived text verbatim.
The quarantine is retained and no module is withdrawn. U4 reclaimed the rework
item before this repair.

Replace the upper existence hole by an explicit representative functor, base-field
omega, transported finite evaluation, and assembly from three strictly smaller
coherence/equations statements. Preserve the complete statement and all existing
public declaration names. Isolate the already proved formal retract completion
in a new module, publicly reexported by the item, to keep compilation local.
No adopted WeilConjectures source module is changed.

## Old

The item publicly imports `Sheaf.SixFunctors.CoefQbarVerdierData` and itself declares
`CoreProperties`, `core_complete`, and `completeCore`. Its sole hole is:

```lean
theorem core_descent :
    ∃ B : DualityData D l hl Ω X, CoreProperties D l hl Ω X B := by sorry
```

The core proposition is:

```lean
def CoreProperties (B : DualityData D l hl Ω X) : Prop :=
  (fun [_linearInst : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω X)] ↦
  (FiniteCoherent D l hl Ω X B.finite) ∧
  B.duality.dual.Additive ∧
  (∀ (E : Index l Ω)
      (K M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) (f : K ⟶ M)
      (c : Coefficient.{u} l Ω E),
    (inclusion (Y := X) E).map
      ((sfRationalCoefficientEquiv l (Coefficient.{u} l Ω E)).symm c •
        (f : (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) ⟶ M)) =
      ((Shrink.algEquiv (Padic l) E.val c : E.val) : Ω) • (inclusion (Y := X) E).map f) ∧
  (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (f : K ⟶ M) (c : Ω),
    B.duality.dual.map (c • f).op = c • B.duality.dual.map f.op) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    B.duality.dual.obj (op ((inclusion (Y := X) E).obj K)) =
      (inclusion (Y := X) E).obj ((B.finite.datum E).dual.obj (op K))) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    HEq ((B.comparison E).hom.app (op K))
      (𝟙 ((inclusion (Y := X) E).obj ((B.finite.datum E).dual.obj (op K))))) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    (inclusion (Y := X) L).map ((B.finite.beta E L h).hom.app (op K)) ≫
      (B.comparison L).hom.app (op ((transition l Ω X E L h).obj K)) ≫
      B.duality.dual.map ((inclusionTransition l Ω X E L h).inv.app K).op =
    (inclusionTransition l Ω X E L h).hom.app ((B.finite.datum E).dual.obj (op K)) ≫
      (B.comparison E).hom.app (op K)) ∧
  (∀ (E : Index l Ω),
    SfClassEvaluationCompatible (inclusion (Y := X) E) (B.finite.datum E).dual B.duality.dual
      (B.finite.datum E).bidual.hom B.duality.bidual.hom (B.comparison E)) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L),
    (inclusion (Y := X) L).map (B.finite.scalar E L h).omega.hom ≫ (B.omegaComparison L).hom =
      (inclusionTransition l Ω X E L h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
          (B.finite.omega E).omega) ≫ (B.omegaComparison E).hom) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    (tensorInclusion D l hl Ω X E K ((B.finite.datum E).dual.obj (op K))).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 ((inclusion (Y := X) E).obj K)) ((B.comparison E).hom.app (op K))) ≫
      B.evaluation ((inclusion (Y := X) E).obj K) =
    (inclusion (Y := X) E).map ((B.finite.datum E).evaluation K) ≫ (B.omegaComparison E).hom) ∧
  (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (f : K ⟶ M),
    (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom f (𝟙 (B.duality.dual.obj (op M)))) ≫ B.evaluation M =
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 K) (B.duality.dual.map f.op)) ≫ B.evaluation K))
      (_linearInst := B.linearCategory)
```

The preserved completion APIs are:

```lean
theorem core_complete (B : DualityData D l hl Ω X)
    (hB : CoreProperties D l hl Ω X B) : DualityProperties D l hl Ω X B
```

```lean
def completeCore (B : DualityData D l hl Ω X) (hB : CoreProperties D l hl Ω X B) :
    Duality D l hl Ω X where
  val := B
  property := core_complete D l hl Ω X B hB
```

## New

The item publicly imports `Sheaf.SixFunctors.CoefQbarVerdierCoreEquations`, which
publicly imports the same Data module. The three declarations above move into
CoreEquations with identical names, binders, visibility and mathematical bodies.
`core_complete` uses sequential conjunction constructors instead of a large tuple, and applies
the HEq comparison pointwise at each E,K to avoid repeated dependent conversion.
The displayed CoreProperties definition and the signature of core_descent are
unchanged. Core descent has a complete proof assembling explicit constructions.
The proved finite-data construction is in finiteData_nonempty in the new
FiniteCoherence module. The original finite_data_exists name, binders and
visibility remain in the item as a proved wrapper; its proof import is private.
The new Functor module implements the actual quotient functor and its finite
comparison; EvaluationDescent implements omega, its comparisons and evaluation.
The three remaining statements concern those fixed constructions rather than
choosing unspecified data. No existing attribute or instance is changed.

The relocated definition is, verbatim:

```lean
def CoreProperties (B : DualityData D l hl Ω X) : Prop :=
  (fun [_linearInst : Linear Ω (generalAlgebraicallyClosedConstructibleCategory l Ω X)] ↦
  (FiniteCoherent D l hl Ω X B.finite) ∧
  B.duality.dual.Additive ∧
  (∀ (E : Index l Ω)
      (K M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) (f : K ⟶ M)
      (c : Coefficient.{u} l Ω E),
    (inclusion (Y := X) E).map
      ((sfRationalCoefficientEquiv l (Coefficient.{u} l Ω E)).symm c •
        (f : (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) ⟶ M)) =
      ((Shrink.algEquiv (Padic l) E.val c : E.val) : Ω) • (inclusion (Y := X) E).map f) ∧
  (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (f : K ⟶ M) (c : Ω),
    B.duality.dual.map (c • f).op = c • B.duality.dual.map f.op) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    B.duality.dual.obj (op ((inclusion (Y := X) E).obj K)) =
      (inclusion (Y := X) E).obj ((B.finite.datum E).dual.obj (op K))) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    HEq ((B.comparison E).hom.app (op K))
      (𝟙 ((inclusion (Y := X) E).obj ((B.finite.datum E).dual.obj (op K))))) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    (inclusion (Y := X) L).map ((B.finite.beta E L h).hom.app (op K)) ≫
      (B.comparison L).hom.app (op ((transition l Ω X E L h).obj K)) ≫
      B.duality.dual.map ((inclusionTransition l Ω X E L h).inv.app K).op =
    (inclusionTransition l Ω X E L h).hom.app ((B.finite.datum E).dual.obj (op K)) ≫
      (B.comparison E).hom.app (op K)) ∧
  (∀ (E : Index l Ω),
    SfClassEvaluationCompatible (inclusion (Y := X) E) (B.finite.datum E).dual B.duality.dual
      (B.finite.datum E).bidual.hom B.duality.bidual.hom (B.comparison E)) ∧
  (∀ (E L : Index l Ω) (h : E ≤ L),
    (inclusion (Y := X) L).map (B.finite.scalar E L h).omega.hom ≫ (B.omegaComparison L).hom =
      (inclusionTransition l Ω X E L h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
          (B.finite.omega E).omega) ≫ (B.omegaComparison E).hom) ∧
  (∀ (E : Index l Ω) (K : Stage l Ω X E),
    (tensorInclusion D l hl Ω X E K ((B.finite.datum E).dual.obj (op K))).hom ≫
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 ((inclusion (Y := X) E).obj K)) ((B.comparison E).hom.app (op K))) ≫
      B.evaluation ((inclusion (Y := X) E).obj K) =
    (inclusion (Y := X) E).map ((B.finite.datum E).evaluation K) ≫ (B.omegaComparison E).hom) ∧
  (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (f : K ⟶ M),
    (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom f (𝟙 (B.duality.dual.obj (op M)))) ≫ B.evaluation M =
      (CoefQbarTensor D l hl Ω X).map
        (Prod.mkHom (𝟙 K) (B.duality.dual.map f.op)) ≫ B.evaluation K))
      (_linearInst := B.linearCategory)
```

The completion signatures and completeCore body are exactly the ones above.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CoefQbarVerdier | no current claim found | Existing names and statements remain available through the item's public reexport. Compile unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdierDualizing | no current claim found | Same core_descent and completeCore APIs. Compile unchanged. |

These are all direct importers of the item in the current sources. No consumer
source is adapted, and the source-library boundary is preserved.

## Status

landed 20261027T210253-L-1681976 2026-10-27 (merge of deliver/U4/Sheaf.SixFunctors.CoefQbarVerdierCore)
