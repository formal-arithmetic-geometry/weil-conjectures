# operationScalarFunctor, operationScalarComplex, operationScalarCounit, operationUnitComplex and operationUnit

## Reason

The complete module exceeded the fixed 60-second compile limit. Its large law structures repeatedly unfolded the scalar-complex wrappers and regular single-complex unit aliases during elaboration and kernel checking. Declare those same five terms with `def`. Keep the two unit definitions locally irreducible while declaring the law structures and restore their ordinary reducibility before proving the laws. The scalar functor and complex wrappers retain ordinary reducibility throughout because their cochain maps must match the recorded models in the law structures. Their values, types, universes, visibility and mathematical meaning are unchanged. There is no axiom or opaque definition, and no new proof obligation in their bodies.

The sheaf monoidal instance is locally irreducible during the law declarations and restored before their proofs. Generic sheafification is disabled while elaborating the abstract-sized structures, using the existing coefficient-sized instance, then restored for the concrete schemes. Both adjustments are local instance/elaboration controls. The unit proof applies the existing bounded-above flat-complex criterion at bound zero after proving flat terms, avoiding expansion of the total-complex unitor. The complete three-module proof compiled with this route in 55.2 seconds for the item module.

## Old

```lean
abbrev operationScalarFunctor {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :
    Mod.{c, v, max c v r} J R ⥤ Mod.{c, v, max c v r} J S :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.E
    C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
    (abelianSheafify.{c, v, max c v r} J) R S φ
    (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model

abbrev operationScalarComplex {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :=
  letI : (operationScalarFunctor.{c, v, r} J φ A).Additive :=
    @SheafOfModules.DerivedChangeOfRingsCochainModel.additive
      C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
      (abelianSheafify.{c, v, max c v r} J) R S φ
      (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model
  (operationScalarFunctor.{c, v, r} J φ A).mapHomologicalComplex (.up ℤ)

abbrev operationScalarCounit {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :
    DerivedCategory.Q ⋙ A.T ⟶
      operationScalarComplex.{c, v, r} J φ A ⋙ DerivedCategory.Q :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.ε
    C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
    (abelianSheafify.{c, v, max c v r} J) R S φ
    (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model

abbrev operationUnitComplex :=
  (CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj
    (SheafOfModules.unit (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing.{c,
      v, max c v r} J B τ)))

abbrev operationUnit : DS.{c, v, max c v r} J B τ :=
  DerivedCategory.Q.obj (operationUnitComplex.{c, v, r} J B τ)
```

## New

```lean
def operationScalarFunctor {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :
    Mod.{c, v, max c v r} J R ⥤ Mod.{c, v, max c v r} J S :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.E
    C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
    (abelianSheafify.{c, v, max c v r} J) R S φ
    (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model

def operationScalarComplex {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :=
  letI : (operationScalarFunctor.{c, v, r} J φ A).Additive :=
    @SheafOfModules.DerivedChangeOfRingsCochainModel.additive
      C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
      (abelianSheafify.{c, v, max c v r} J) R S φ
      (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model
  (operationScalarFunctor.{c, v, r} J φ A).mapHomologicalComplex (.up ℤ)

def operationScalarCounit {R S : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (A : ScalarData.{c, v, max c v r} φ) :
    DerivedCategory.Q ⋙ A.T ⟶
      operationScalarComplex.{c, v, r} J φ A ⋙ DerivedCategory.Q :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.ε
    C _ inferInstance J inferInstance (locallyBijective.{c, v, max c v r} J)
    (abelianSheafify.{c, v, max c v r} J) R S φ
    (hasDerived.{c, v, max c v r} J R) (hasDerived.{c, v, max c v r} J S) A.model

def operationUnitComplex :=
  (CochainComplex.singleFunctor (Systems.{c, v, max c v r} J B τ) 0).obj
    (SheafOfModules.unit (ring.{c, v, max c v r} (coefficientSequenceTopology J) (systemRing.{c,
      v, max c v r} J B τ)))

def operationUnit : DS.{c, v, max c v r} J B τ :=
  DerivedCategory.Q.obj (operationUnitComplex.{c, v, r} J B τ)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedOperationSystemModels | J6 | Definition bodies unchanged; local unfolding control while checking structures; all proofs compiled in the same module. |

The shared source scan and `tools/downstream.py Sheaf.Paper.NormalizedOperationSystemModels --uses operationUnitComplex` and the same command with `--uses operationUnit`, `--uses operationScalarComplex` and `--uses operationScalarCounit` and `--uses operationScalarFunctor` find zero downstream Lean modules. Direct searches for the five changed names likewise find only this module. DAG parents retain the same statements and definitions up to definitional equality; no target meaning changes and no forced adaptation is needed.

## Status

landed 20261022T011850-L-3225647 2026-10-22 (merge of deliver/J6/Sheaf.Paper.NormalizedOperationSystemModels)
