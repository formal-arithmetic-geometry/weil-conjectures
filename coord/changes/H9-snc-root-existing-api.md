# Algebra.root_basis and root evaluation API

## Reason

Repair the returned SNCRootStageSystem delivery at cd41909f028. Its private
normal-form lemmas duplicated the already proved private implementation of
HenselianParameterRootRegularity. That module is currently unclaimed. Expose its
six existing generic helpers so the stage-system proof uses the existing
construction and basis. This removes the duplicate normal-form block rather
than reproducing its proofs. Keep every type, universe, body, import and existing
public declaration unchanged. Add source docstrings to the exposed helpers.

The other returned duplicate, regular_localization, is private in the adopted
source library. Leave that module verbatim, delete our private duplicate, and
apply the existing public RingTheory.isRegularRing_of_localization at both uses,
supplying its standard localization hypotheses.

## Old

```lean
private theorem rootCoordinate_pow {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) :
    parameterRootCoordinate t n i ^ n = algebraMap R _ (t i)
```

```lean
private theorem root_basis {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) :
    ∃ b : Module.Basis (Fin r → Fin n) R (pthRootAlgebra n r R t),
      ∀ a, b a = ∏ i, parameterRootCoordinate t n i ^ (a i).val
```

```lean
private def rootEval {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) :
    pthRootAlgebra n r R t →+* S
```

```lean
private theorem rootEval_scalar {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) (a : R) :
    rootEval t f x hx (algebraMap R _ a) = f a
```

```lean
private theorem rootEval_coordinate {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) (i : Fin r) :
    rootEval t f x hx (parameterRootCoordinate t n i) = x i
```

```lean
private theorem rootHom_ext {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S]
    (f g : pthRootAlgebra n r R t →+* S)
    (hc : ∀ a : R, f (algebraMap R _ a) = g (algebraMap R _ a))
    (hx : ∀ i, f (parameterRootCoordinate t n i) = g (parameterRootCoordinate t n i)) :
    f = g
```

## New

```lean
theorem rootCoordinate_pow {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) :
    parameterRootCoordinate t n i ^ n = algebraMap R _ (t i)
```

```lean
theorem root_basis {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) :
    ∃ b : Module.Basis (Fin r → Fin n) R (pthRootAlgebra n r R t),
      ∀ a, b a = ∏ i, parameterRootCoordinate t n i ^ (a i).val
```

```lean
def rootEval {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) :
    pthRootAlgebra n r R t →+* S
```

```lean
theorem rootEval_scalar {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) (a : R) :
    rootEval t f x hx (algebraMap R _ a) = f a
```

```lean
theorem rootEval_coordinate {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) (i : Fin r) :
    rootEval t f x hx (parameterRootCoordinate t n i) = x i
```

```lean
theorem rootHom_ext {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S]
    (f g : pthRootAlgebra n r R t →+* S)
    (hc : ∀ a : R, f (algebraMap R _ a) = g (algebraMap R _ a))
    (hx : ∀ i, f (parameterRootCoordinate t n i) = g (parameterRootCoordinate t n i)) :
    f = g
```

All six existing proof/construction bodies are byte-for-byte unchanged. The root
coordinate and pthRootAlgebra definitions remain unchanged. SNCRootStageSystem
uses their definitionally identical sncRootLevel/sncRootCoordinate presentation.
The target statement and its four public definitions remain unchanged.

## Users

Inventory: tools/downstream.py Sheaf.RingTheory.HenselianParameterRootRegularity
--uses Algebra.henselian_parameter_root_regularity, plus all direct importers
and the two edited modules. The change adds names to the API; it changes no
existing public meaning. Only the two named edited modules are delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SNCFiniteFibreClassification | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SNCFiniteFibreData | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SNCFiniteTameSheaves | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SNCRootStageSystem | H9 | Replace duplicated private root algebra with the existing API; statement unchanged. |
| Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FullParameterRootTower | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.FullRootRotationTorsor | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveChart | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveCoordinates | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveMorphism | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveScalarMorphism | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerRefinement | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerStratumScalarMaps | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerStratumScalarMateDetection | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.KummerSuccessiveDescent | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ParameterRootIntegralNilFibre | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.RootTowerProfiniteBaseChange | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.StrictLocalPrimeToPKummerSplitting | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.RingTheory.HenselianParameterRootDomainTower | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |
| Sheaf.RingTheory.HenselianParameterRootRegularity | unclaimed | Expose six existing proved helpers; all bodies and types unchanged. |
| Sheaf.RingTheory.ParameterRootBoundaryDvrs | unclaimed | Additive API only; existing statements and definitions unchanged; no adaptation. |

The three existing direct importers are HenselianParameterRootDomainTower,
ParameterRootBoundaryDvrs, and StrictLocalPrimeToPKummerSplitting. No source
under WeilConjectures is changed. The existing henselian node records the six
newly public helpers; the stage-system node records its use of their existing
proof. No new node, assumption, or hole is introduced.

All three existing direct importers compiled against the changed API, without
warnings (42.4, 39.6 and 45.0 seconds respectively). Their byte-identical validation
copies were then removed from the sandbox; no consumer adaptation is delivered.
The exposed API itself compiled in 24.5 seconds and the stage-system module in
57.0 seconds (final version). Import-pruning/duplicate checks passed for both changed modules.

The private stage-system rootEvalAlg, rootTransition, rootInclusion and
localizedMap definitions retain their signatures and constructions, and gain
`@[irreducible]`. Their coefficient/coordinate APIs are used by later proofs;
only the formula lemmas unfold them explicitly. This addresses the first
delivery compile's 60-second timeout. No public definition changes, consumer
adaptation, file splitting or time-limit increase is involved.

## Status

landed 20261024T015006-L-2308572 2026-10-24 (merge of deliver/H9/Sheaf.AlgebraicGeometry.SNCRootStageSystem)
