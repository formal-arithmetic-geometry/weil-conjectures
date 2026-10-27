# WeilConjectures.RationalSmoothPurityCanonical.ordinarySource

## Reason

Write the existing return types of `orientation`, `ordinarySource`, `projection`,
`integralIso`, and `modelBack` explicitly. Their bodies are unchanged. The
annotations retain the canonical integral derived/full-subcategory and rational
scalar categories directly, rather than inferring them through selected witnesses,
large tensor/projection presentations, or scalar-extension implementations.
The `projection` declaration locally unfolds `PurCompactSupport.image` while
checking its existing composite against the concise image/tensor type. The
resulting constant hides the expanded functor combinators from later uses.
Give `ConstructibleExceptionalCoefficients.category` local instance priority 0,
so the native category instances are tried first on concrete categories. Its
matched category structures are precisely those native structures; no data or
exported instance attribute changes.
These are the original inferred types, up to definitional equality; Lean checks
the same bodies at them. No target statement, hypothesis, data, map, normalization,
or mathematical meaning changes.

## Old

```lean
def orientation (d : ℕ) [SmoothOfRelativeDimension d f] :=
  (orientation_existsUnique P f c S d).exists.choose

def ordinarySource (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  tensorToOrdinary P.coefficients.l P.extension X
    (twist P X (X ↘ Spec (.of P.field.k)) d)
    ⟨_,pullFiniteTor P f d K⟩ ≪≫
    (ordinaryModel P.coefficients.l P.extension X).tensor.mapIso
      (Iso.prod (Iso.refl _) (smoothPullToOrdinary P f d K))

def projection (d : ℕ) (K : finiteTorConstructibleIntegralCategory
    P.coefficients.l P.extension Y) :=
  ((PurCompactSupport.projectionMap
    (PurCompactSupport.completed P.coefficients.l P.extension) c
    (ordinaryModel P.coefficients.l P.extension X)
    (ordinaryModel P.coefficients.l P.extension c.Z)
    (ordinaryModel P.coefficients.l P.extension Y)
    (PurCompactSupport.completedPull_comp P.coefficients.l P.extension c.i c.g)).app
      (twist P X (X ↘ Spec (.of P.field.k)) d).obj).app K.obj

def integralIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  @asIso _ _ _ _ (integralMap P f c S d K) (integralMap_isIso P f c S d K)

def modelBack (T : Scheme.{u}) :=
  sfRationalScalarExtension P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) T 0
      (Fact.out : P.coefficients.l.Prime).ne_zero P.extension (modelInverse P)
```

## New

```lean
def orientation (d : ℕ) [SmoothOfRelativeDimension d f] :
    twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0) :=
  (orientation_existsUnique P f c S d).exists.choose

def ordinarySource (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (integralSource P f d K).obj ≅
      (ordinaryModel P.coefficients.l P.extension X).tensor.obj
        ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
          (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
            f).obj K.obj) :=
  tensorToOrdinary P.coefficients.l P.extension X
    (twist P X (X ↘ Spec (.of P.field.k)) d)
    ⟨_,pullFiniteTor P f d K⟩ ≪≫
    (ordinaryModel P.coefficients.l P.extension X).tensor.mapIso
      (Iso.prod (Iso.refl _) (smoothPullToOrdinary P f d K))

attribute [local semireducible] PurCompactSupport.image in
def projection (d : ℕ) (K : finiteTorConstructibleIntegralCategory
    P.coefficients.l P.extension Y) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      (((PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).obj (twist P X (X ↘ Spec (.of P.field.k)) d).obj), K.obj) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).obj ((ordinaryModel P.coefficients.l P.extension X).tensor.obj
          ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
            (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
              f).obj K.obj)) :=
  ((PurCompactSupport.projectionMap
    (PurCompactSupport.completed P.coefficients.l P.extension) c
    (ordinaryModel P.coefficients.l P.extension X)
    (ordinaryModel P.coefficients.l P.extension c.Z)
    (ordinaryModel P.coefficients.l P.extension Y)
    (PurCompactSupport.completedPull_comp P.coefficients.l P.extension c.i c.g)).app
      (twist P X (X ↘ Spec (.of P.field.k)) d).obj).app K.obj

def integralIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralSource P f d K ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  @asIso _ _ _ _ (integralMap P f c S d K) (integralMap_isIso P f c S d K)

def modelBack (T : Scheme.{u}) :
    sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) T ⥤
      sfRationalConstructibleCategory P.coefficients.l P.extension T :=
  sfRationalScalarExtension P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) T 0
      (Fact.out : P.coefficients.l.Prime).ne_zero P.extension (modelInverse P)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalSmoothPurityCanonical | S3 | The same constructions have their existing types explicit. No adaptation beyond the annotations. |
| Sheaf.Paper.TowerTracePurityComparison | P4 | The basename search for `orientation` also lists this module. Its references are to its own `WeilConjectures.TowerTracePurityComparison.orientation`, so no adaptation. |

`tools/downstream.py --uses` lists only the item for the other four names.
No external signature or source adaptation is necessary.

## Status

landed 20261026T070945-L-3715061 2026-10-26 (merge of deliver/S3/Sheaf.Paper.RationalSmoothPurityCanonical)
