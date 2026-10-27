# AffineIntegrationCoefficient.trace and AffineIntegrationCoefficient.unitIso

## Reason

The original bodies repeatedly ask the kernel to compare the generic coefficient-category
monoidal instance with the concrete module-category instance. Profiling the original
bodies measured approximately 15 seconds each for `trace` and `unitIso`. The definitions
alone compiled in 42.8 seconds; the full proof exceeded 60 seconds. The shared irreducible
`ordinaryUnitIso` checks this comparison once, preserving the actual degree-zero unit
isomorphism. A definitions-only diagnostic with the shared interface compiled in 17.9
seconds. After extracting the trace calculation over generic finite coefficient rings as a
private proved helper, the full actual module compiled cleanly in 18.5 seconds.

## Old

```lean
def trace (N : ℕ) (hN : 0 < N) (R : Type (u + 1)) [CommRing R] [Finite R]
    (hR : (N : R) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
      (compactification S d)).obj (coefficient R N hR S d) ⟶
        𝟙_ (DerivedCategoryModule R S) :=
  by
  unfold coefficient
  exact affineScalarCompactificationCounit N hN R hR S hS d (compactification S d)
    (ordinaryFiniteUnit R S) ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} R) S).hom

def unitIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) :
    (scalarExtension φ S).obj (ordinaryFiniteUnit A S) ≅ ordinaryFiniteUnit B S :=
  (scalarExtension φ S).mapIso (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S) ≪≫
    ExceptionalCoefficients.unitIso φ S ≪≫
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} B) S).symm
```

## New

```lean
def ordinaryUnitIso (R : Type (u + 1)) [CommRing R] (S : Scheme.{u}) :
    ordinaryFiniteUnit R S ≅ 𝟙_ (DerivedCategoryModule R S) :=
  singleFunctorObjUnitIso (ModuleCat.{u + 1} R) S

def trace (N : ℕ) (hN : 0 < N) (R : Type (u + 1)) [CommRing R] [Finite R]
    (hR : (N : R) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R)
      (compactification S d)).obj (coefficient R N hR S d) ⟶
        𝟙_ (DerivedCategoryModule R S) :=
  by
  unfold coefficient
  exact affineScalarCompactificationCounit N hN R hR S hS d (compactification S d)
    (ordinaryFiniteUnit R S) ≫ (ordinaryUnitIso R S).hom

def unitIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (S : Scheme.{u}) :
    (scalarExtension φ S).obj (ordinaryFiniteUnit A S) ≅ ordinaryFiniteUnit B S :=
  (scalarExtension φ S).mapIso (ordinaryUnitIso A S) ≪≫
    ExceptionalCoefficients.unitIso φ S ≪≫
    (ordinaryUnitIso B S).symm
```

`ordinaryUnitIso` is exactly the original `singleFunctorObjUnitIso` specialization.
Unfolding it recovers each original body. All original declaration signatures,
attributes, visibility and public imports are unchanged. No coefficient object or
normalization changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | W6 | Both bodies use the shared isomorphism; its proof uses the same interface. |

`tools/downstream.py` reports no external Lean importers; a direct search of both Lean
roots finds no external uses of the namespace. The quarantine copy is preserved. DAG
parents continue to use the unchanged equation statement. No forced adaptations are
needed. Definitions used by targets remain definitionally equal, with the same maps.

## Status

landed 20261025T002541-L-3133578 2026-10-25 (merge of deliver/W6/Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation)
