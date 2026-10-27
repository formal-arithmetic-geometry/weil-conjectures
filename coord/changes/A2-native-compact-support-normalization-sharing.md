# WeilConjectures.LocallyFiniteAdicCompactSupport.IntegralNormalization

## Reason

Restore the quarantined item named by coord/rework.tsv (build 2026-10-24).
The recorded failure is a deterministic whnf timeout at the last rationalization
application in IntegralNormalization, followed by unknown IntegralNormalization
and CompactSupportComparison declarations. The archived file currently compiles,
but simply restoring an unchanged file would not address its elaboration cost.

Share the finite-stage rationalized object and its common-stage inclusion with
local let bindings. This preserves the definition by zeta reduction, while avoiding
repeated elaboration of the rationalization and common-stage inclusion. Measured
with Mathlib.Util.CountHeartbeats: the archived normalization uses 81,504 heartbeats;
the shared version uses 52,347, with the same 200,000-heartbeat limit. Diagnostic
imports and commands are not part of the delivery. No compilation limit is raised.

## Old

```lean
def IntegralNormalization [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (alpha : stage.system.functor ⋙ target.J ≅ source.J ⋙ actual l c) : Prop :=
  ∀ (E : Index l (PadicAlgCl l))
      (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    ∃ (A B : sfRationalConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y)
      (r : A ⟶ B),
      HEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app
        ((rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K)) ∧
    ∃ (M₁ M₂ M₃ M₄ M₅ : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y)))
      (a₀ : (sections l Y).mapDerivedCategory.obj
        ((stage.system.functor ⋙ target.J).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
            ((rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K))) ⟶ M₁)
      (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃) (a₃ : M₃ ⟶ M₄) (a₄ : M₄ ⟶ M₅)
      (a₅ : M₅ ⟶ (sections l Y).mapDerivedCategory.obj
        ((source.J ⋙ actual l c).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
            ((rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K)))),
      HEq a₀ ((sections l Y).mapDerivedCategory.map
        (target.J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r))) ∧
      HEq a₁ ((target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient.{u} l (PadicAlgCl l) E)).obj
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₂ ((pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient.{u} l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₃ ((PurCompactSupport.comparison (change E) c).app K.obj) ∧
      HEq a₄ ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₅ ((operationTransport l c).inv.app (source.J.obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
            ((rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K)))) ∧
      (sections l Y).mapDerivedCategory.map (alpha.hom.app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
            ((rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K))) =
        a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅

```

## New

```lean
def IntegralNormalization [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (alpha : stage.system.functor ⋙ target.J ≅ source.J ⋙ actual l c) : Prop :=
  ∀ (E : Index l (PadicAlgCl l))
      (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
    let rationalInput :=
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K
    let input := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj rationalInput
    ∃ (A B : sfRationalConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y)
      (r : A ⟶ B),
      HEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app rationalInput) ∧
    ∃ (M₁ M₂ M₃ M₄ M₅ : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y)))
      (a₀ : (sections l Y).mapDerivedCategory.obj
        ((stage.system.functor ⋙ target.J).obj input) ⟶ M₁)
      (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃) (a₃ : M₃ ⟶ M₄) (a₄ : M₄ ⟶ M₅)
      (a₅ : M₅ ⟶ (sections l Y).mapDerivedCategory.obj
        ((source.J ⋙ actual l c).obj input)),
      HEq a₀ ((sections l Y).mapDerivedCategory.map
        (target.J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r))) ∧
      HEq a₁ ((target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient.{u} l (PadicAlgCl l) E)).obj
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₂ ((pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient.{u} l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₃ ((PurCompactSupport.comparison (change E) c).app K.obj) ∧
      HEq a₄ ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₅ ((operationTransport l c).inv.app (source.J.obj input)) ∧
      (sections l Y).mapDerivedCategory.map (alpha.hom.app input) =
        a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅

```

## Users

`python3 tools/downstream.py Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization
--allow-missing --uses IntegralNormalization operationTransport` reports zero current
Lean importers. This is a restoration, not a withdrawal. The DAG parents
lem-sf-native-geometric-brown-constructible-comparison,
lem-sf-locally-finite-adic-compact-support-sums and
lem-sf-adic-proper-adjunction-realization remain attached to this node, with all
its statements, public imports and dependencies retained. No user adaptation is
needed: the definition is definitionally equal to the archived formula.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | A2 (dispatched repair) | Restore all declarations; share repeated input terms in IntegralNormalization. |

All public signatures, the six-arrow normalization, and the target meanings stay
identical. A temporary private copy of the archived formula was compared with the
new definition by a theorem proved with rfl; that diagnostic is removed before
delivery. No mathematical statement or DAG route changes.

## Status

landed 20261024T184515-L-3058061 2026-10-24 (merge of deliver/A2/Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization)
