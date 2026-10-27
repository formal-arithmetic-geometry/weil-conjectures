# WeilConjectures.SfPackageIntegralTraceReduction

## Reason

Restore the archived timeout item. Profiling isolated the original stall at
SfPackageIntegralTraceReduction, after predecessors finished in less than four seconds each. The two
reduction squares compose independently chosen presentations: PurCompactSupport.comparison uses
pbcDerivedExtend along the quotient projection, while the reconstructed purity reductions use
scalarReductionDerivedExtension.

Insert the existing canonical PurCompactSupport.finiteReductionIso inversely at Y and forwards at X,
inside support. This is the tensor-unit normalized comparison fixed by the adjunctions to the same
restriction functor. It is already recorded by lem-pur-compact-support-integral-coefficient-
comparison. The same transports appear in PurCompactSupport.IsRecordedIdentification and in
NormalizedIntegralPurityTrace.supportComparison. Inputs, finite purity maps, counits, traces and
finite quotients remain the original ones.

The two integral trace constructions have explicit result types; their composite bodies are
unchanged and the integral counit trace is irreducible. Protect the large chosen constructions
locally. Further profiling found repeated reconstruction of category instances at the
rational/field/common projections. Supply the native category and projection parameters explicitly,
retaining all original arrows and equations. FieldComparison.b/q have their existing implicit
arguments fixed once in local let bindings. The common finite-stage purity term reduces only its
field-model wrappers; its counit composite uses the proved commonCategory_eq before inclusion. The
new sfPackageTransportHomCategory implements that equality substitution in full, without a choice or
proof obligation. Six projection abbreviations are exactly the corresponding Mathlib object, map,
hom, inv, transformation-component and isomorphism-component operations, with ordinary implicit
category parameters inferred from the supplied functor or isomorphism. This avoids reconstructing an
instance-implicit category through the coefficient object type. sfPackageCompose is
CategoryStruct.comp with the native category supplied explicitly, avoiding the same inference at
composition notation. Both transparency-respecting options are true.

The changed definitions lie on the target route, so this packet requires statement review of their
meaning. No target declaration is edited. The original theorem statement and every original public
declaration are retained. The node attachment gains only the eight fully constructed generic helpers
and a note; the mathematical statement and planned proof dependencies stay.

## Old

### SfPackageIntegralTraceReduction

```lean
def SfPackageIntegralTraceReduction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hTor : finiteTorConstructibleIntegral C.l E Y K)
    (t : (PurCompactSupport.image (PurCompactSupport.completed C.l E)
      (integralExceptionalCompactification D f)).obj (purAdicSource D C E f d K) ⟶ K) :
    Prop :=
  ∀ n : ℕ,
    (scalarReductionDerivedExtension C.l E Y n).map t =
      (PurCompactSupport.comparison
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
        (integralExceptionalCompactification D f)).app (purAdicSource D C E f d K) ≫
      (PurCompactSupport.finiteImageIso C.l E n
        (integralExceptionalCompactification D f)).hom.app _ ≫
      ((purAdicFiniteSetting D C E n).smoothCompactSupport f).map
        (purAdicSourceReduction D C E f d K hTor n) ≫
      (purAdicFiniteSetting D C E n).coefficientValuedSmoothTrace f d
        ((scalarReductionDerivedExtension C.l E Y n).obj K)
        (purAdicReductionFiniteTor D C E Y K hTor n) ∧
    SfPackageFiniteOrientationTrace (purAdicFiniteSetting D C E n) f d
      ((scalarReductionDerivedExtension C.l E Y n).obj K)
      (purAdicReductionFiniteTor D C E Y K hTor n)
```

### SfPackageIntegralCounitReduction

```lean
def SfPackageIntegralCounitReduction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hTor : finiteTorConstructibleIntegral C.l E Y K)
    (epsilon : (PurCompactSupport.image (PurCompactSupport.completed C.l E)
      (integralExceptionalCompactification D f)).obj (purAdicTarget D C E f K) ⟶ K) :
    Prop :=
  ∀ n : ℕ,
    (scalarReductionDerivedExtension C.l E Y n).map epsilon =
      (PurCompactSupport.comparison
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
        (integralExceptionalCompactification D f)).app (purAdicTarget D C E f K) ≫
      (PurCompactSupport.finiteImageIso C.l E n
        (integralExceptionalCompactification D f)).hom.app _ ≫
      ((purAdicFiniteSetting D C E n).smoothCompactSupport f).map
        (purAdicTargetReduction D C E f d K hTor n) ≫
      (purAdicFiniteSetting D C E n).smoothExceptionalCounit f
        ((scalarReductionDerivedExtension C.l E Y n).obj K)
```

### sfPackageIntegralCounitTrace

```lean
def sfPackageIntegralCounitTrace
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  (S.ring.left c (.integral (AdicSmoothDualizing.fieldStage P))).inv.app
      (integralSource P f d K) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι.map
      ((operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).F.map
          (integralMap P f c S d K) ≫
        (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app K)
```

### sfPackageReconstructedIntegralTrace

```lean
def sfPackageReconstructedIntegralTrace
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y)
    (eR : purAdicSource P.field P.coefficients P.extension f d K.obj ≅
      purAdicTarget P.field P.coefficients P.extension f K.obj)
    (b : purAdicTarget P.field P.coefficients P.extension f K.obj ≅
      ((operation P f (integralExceptionalCompactification P.field f) S
        (.integral (AdicSmoothDualizing.fieldStage P))).G.obj K).obj) :=
  (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
    (integralExceptionalCompactification P.field f)).map eR.hom ≫
    sfPackageReconstructedIntegralCounit P f S K b
```

### SfPackageRationalOrientationTrace

```lean
def SfPackageRationalOrientationTrace
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) : Prop :=
    ∃ e : _ ≅ _, e = (rationalIso P f c S d K).symm ∧
      (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F.map e.inv ≫
          (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app
            K =
        (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F.map
            (rationalSourceComparison P f d K).hom ≫
          (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).q.inv.app
            (integralSource P f d (representative P K)) ≫
          (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P) Y).map
              (integralTraceTranspose P f c S d (representative P K)) ≫
          eqToHom (representative_eq P K)
```

### SfPackageFieldOrientationTrace

```lean
def SfPackageFieldOrientationTrace
    (L : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (a : P.extension →ₐ[Padic P.coefficients.l] L.val)
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) : Prop :=
    ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) (AdicSmoothDualizing.fieldStage (stageSetting P L))
      a X).map (rationalIso P f c S d K).hom ≫
        (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
          (AdicSmoothDualizing.fieldStage (stageSetting P L)) a).b.hom.app K =
      (sourceScalar P.coefficients.l P.extension L.val a f d K).hom ≫
        (rationalIso (stageSetting P L) f c S d
          ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y).obj K)).hom) ∧
    (ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) (AdicSmoothDualizing.fieldStage (stageSetting P L))
      a Y).map
        ((operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).F.map
            (rationalIso P f c S d K).hom ≫
          (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app
            K) =
      (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
          (AdicSmoothDualizing.fieldStage (stageSetting P L)) a).q.hom.app
            ((rationalSource P.coefficients.l P.extension f d).obj K) ≫
        (operation P f c S
          (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))).F.map
            (sourceScalar P.coefficients.l P.extension L.val a f d K).hom ≫
        (operation P f c S
          (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))).F.map
            (rationalIso (stageSetting P L) f c S d
              ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
                P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
                (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y).obj K)).hom ≫
        (operation P f c S
          (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))).adjunction.counit.app
            ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
              P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
              (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y).obj K) ∧
    (ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) (AdicSmoothDualizing.fieldStage (stageSetting P L))
      a X).map (rationalIso P f c S d K).inv ≫
        (sourceScalar P.coefficients.l P.extension L.val a f d K).hom =
      (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
        (AdicSmoothDualizing.fieldStage (stageSetting P L)) a).b.hom.app K ≫
        (rationalIso (stageSetting P L) f c S d
          ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y).obj K)).inv
```

### sfPackageCommonStagePurity

```lean
def sfPackageCommonStagePurity
    (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) :
    (rationalSource P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
        P.coefficients.Qbar K.stage) f d).obj K.obj ≅
      (S.ring.operation c (.rational (ConstructibleExceptionalCoefficients.commonField
        P.coefficients.l P.coefficients.Qbar K.stage))).G.obj K.obj :=
  smallModelIso (stageSetting P K.stage) f c S d K.obj
```

### SfPackageCommonOrientation

```lean
def SfPackageCommonOrientation (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) : Prop :=
    ∃ e : (S.ring.operation c .closed).G.obj K ≅
      (commonSource P.coefficients.l P.coefficients.Qbar f d).obj K,
      e.inv = (commonIso P f c S d K).hom ∧
      (S.ring.operation c .closed).F.map e.inv ≫
          (S.ring.operation c .closed).adjunction.counit.app K =
        (S.ring.operation c .closed).F.map
            (commonSourceComparison P.coefficients.l P.coefficients.Qbar f d K).hom ≫
          (S.common.commonComparison c K.stage).q.inv.app
            ((rationalSource P.coefficients.l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
                P.coefficients.Qbar K.stage) f d).obj K.obj) ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := Y) K.stage).map
              ((S.ring.operation c (.rational (ConstructibleExceptionalCoefficients.commonField
                  P.coefficients.l P.coefficients.Qbar K.stage))).F.map
                  (sfPackageCommonStagePurity P f c S d K).hom ≫
                (S.ring.operation c (.rational (ConstructibleExceptionalCoefficients.commonField
                  P.coefficients.l P.coefficients.Qbar K.stage))).adjunction.counit.app K.obj)
```

## New

### SfPackageIntegralTraceReduction

```lean
def SfPackageIntegralTraceReduction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hTor : finiteTorConstructibleIntegral C.l E Y K)
    (t : (PurCompactSupport.image (PurCompactSupport.completed C.l E)
      (integralExceptionalCompactification D f)).obj (purAdicSource D C E f d K) ⟶ K) :
    Prop :=
  ∀ n : ℕ,
    (scalarReductionDerivedExtension C.l E Y n).map t =
      (PurCompactSupport.finiteReductionIso C.l E Y n).inv.app
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E)
          (integralExceptionalCompactification D f)).obj (purAdicSource D C E f d K)) ≫
      (PurCompactSupport.comparison
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
        (integralExceptionalCompactification D f)).app (purAdicSource D C E f d K) ≫
      (PurCompactSupport.finiteImageIso C.l E n
        (integralExceptionalCompactification D f)).hom.app _ ≫
      ((purAdicFiniteSetting D C E n).smoothCompactSupport f).map
        ((PurCompactSupport.finiteReductionIso C.l E X n).hom.app (purAdicSource D C E f d K) ≫
          purAdicSourceReduction D C E f d K hTor n) ≫
      (purAdicFiniteSetting D C E n).coefficientValuedSmoothTrace f d
        ((scalarReductionDerivedExtension C.l E Y n).obj K)
        (purAdicReductionFiniteTor D C E Y K hTor n) ∧
    SfPackageFiniteOrientationTrace (purAdicFiniteSetting D C E n) f d
      ((scalarReductionDerivedExtension C.l E Y n).obj K)
      (purAdicReductionFiniteTor D C E Y K hTor n)
```

### SfPackageIntegralCounitReduction

```lean
def SfPackageIntegralCounitReduction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hTor : finiteTorConstructibleIntegral C.l E Y K)
    (epsilon : (PurCompactSupport.image (PurCompactSupport.completed C.l E)
      (integralExceptionalCompactification D f)).obj (purAdicTarget D C E f K) ⟶ K) :
    Prop :=
  ∀ n : ℕ,
    (scalarReductionDerivedExtension C.l E Y n).map epsilon =
      (PurCompactSupport.finiteReductionIso C.l E Y n).inv.app
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E)
          (integralExceptionalCompactification D f)).obj (purAdicTarget D C E f K)) ≫
      (PurCompactSupport.comparison
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
        (integralExceptionalCompactification D f)).app (purAdicTarget D C E f K) ≫
      (PurCompactSupport.finiteImageIso C.l E n
        (integralExceptionalCompactification D f)).hom.app _ ≫
      ((purAdicFiniteSetting D C E n).smoothCompactSupport f).map
        ((PurCompactSupport.finiteReductionIso C.l E X n).hom.app (purAdicTarget D C E f K) ≫
          purAdicTargetReduction D C E f d K hTor n) ≫
      (purAdicFiniteSetting D C E n).smoothExceptionalCounit f
        ((scalarReductionDerivedExtension C.l E Y n).obj K)
```

### sfPackageIntegralCounitTrace

```lean
def sfPackageIntegralCounitTrace
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
      c).obj (integralSource P f d K).obj ⟶ K.obj :=
  (S.ring.left c (.integral (AdicSmoothDualizing.fieldStage P))).inv.app
      (integralSource P f d K) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι.map
      ((operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).F.map
          (integralMap P f c S d K) ≫
        (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app K)
```

### sfPackageReconstructedIntegralTrace

```lean
def sfPackageReconstructedIntegralTrace
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y)
    (eR : purAdicSource P.field P.coefficients P.extension f d K.obj ≅
      purAdicTarget P.field P.coefficients P.extension f K.obj)
    (b : purAdicTarget P.field P.coefficients P.extension f K.obj ≅
      ((operation P f (integralExceptionalCompactification P.field f) S
        (.integral (AdicSmoothDualizing.fieldStage P))).G.obj K).obj) :
    (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
      (integralExceptionalCompactification P.field f)).obj
        (purAdicSource P.field P.coefficients P.extension f d K.obj) ⟶ K.obj :=
  (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
    (integralExceptionalCompactification P.field f)).map eR.hom ≫
    sfPackageReconstructedIntegralCounit P f S K b
```

### SfPackageRationalOrientationTrace

```lean
def SfPackageRationalOrientationTrace
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) : Prop :=
  let CY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y (.rational (AdicSmoothDualizing.fieldStage P))
  let H := rationalSource P.coefficients.l P.extension f d
  let A := operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))
  let gamma := rationalIso P f c S d K
  let source := rationalSourceComparison P f d K
  let q := (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).q
  let RY := ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P) Y
  let lattice := representative P K
  let latticeSource := integralSource P f d lattice
  let trace := integralTraceTranspose P f c S d lattice
  ∃ e : @Iso _ (ConstructibleExceptionalCoefficients.category P.coefficients.l
        P.coefficients.Qbar X (.rational (AdicSmoothDualizing.fieldStage P)))
      (sfPackageFunctorObject A.G K)
      (sfPackageFunctorObject H K),
    e = (@Iso.symm _ _ _ _ gamma) ∧
    sfPackageCompose CY (sfPackageFunctorMap A.F (sfPackageIsoInv e))
      (sfPackageNatTransApp A.adjunction.counit K) =
      sfPackageCompose CY (sfPackageFunctorMap A.F (sfPackageIsoHom source))
        (sfPackageCompose CY (sfPackageIsoInv (sfPackageIsoApp q latticeSource))
          (sfPackageCompose CY (sfPackageFunctorMap RY trace)
            (@eqToHom _ CY.toCategoryStruct _ _ (representative_eq P K))))
```

### SfPackageFieldOrientationTrace

```lean
def SfPackageFieldOrientationTrace
    (L : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (a : P.extension →ₐ[Padic P.coefficients.l] L.val)
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) : Prop :=
  let CY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y (.rational (AdicSmoothDualizing.fieldStage P))
  let DX := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar X (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
  let DY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
  let A := operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))
  let B := operation (stageSetting P L) f c S
    (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
  let TX := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
    (AdicSmoothDualizing.fieldStage (stageSetting P L)) a X
  let TY := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
    (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y
  let gamma := rationalIso P f c S d K
  let gamma' := rationalIso (stageSetting P L) f c S d (sfPackageFunctorObject TY K)
  let source := sourceScalar P.coefficients.l P.extension L.val a f d K
  let H := rationalSource P.coefficients.l P.extension f d
  let comparison := S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
    (AdicSmoothDualizing.fieldStage (stageSetting P L)) a
  let b := ConstructibleExceptionalCoefficients.FieldComparison.b
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (X := X) (Y := Y)
    (s := .rational (AdicSmoothDualizing.fieldStage P))
    (t := .rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
    (A := A) (B := B) (TX := TX) (TY := TY) comparison
  let q := ConstructibleExceptionalCoefficients.FieldComparison.q
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (X := X) (Y := Y)
    (s := .rational (AdicSmoothDualizing.fieldStage P))
    (t := .rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
    (A := A) (B := B) (TX := TX) (TY := TY) comparison
  sfPackageCompose DX (sfPackageFunctorMap TX (sfPackageIsoHom gamma))
      (sfPackageIsoHom (sfPackageIsoApp b K)) =
    sfPackageCompose DX (sfPackageIsoHom source) (sfPackageIsoHom gamma') ∧
  sfPackageFunctorMap TY
    (sfPackageCompose CY (sfPackageFunctorMap A.F (sfPackageIsoHom gamma))
      (sfPackageNatTransApp A.adjunction.counit K)) =
    sfPackageCompose DY (sfPackageIsoHom (sfPackageIsoApp q (sfPackageFunctorObject H K)))
      (sfPackageCompose DY (sfPackageFunctorMap B.F (sfPackageIsoHom source))
        (sfPackageCompose DY (sfPackageFunctorMap B.F (sfPackageIsoHom gamma'))
          (sfPackageNatTransApp B.adjunction.counit (sfPackageFunctorObject TY K)))) ∧
  sfPackageCompose DX (sfPackageFunctorMap TX (sfPackageIsoInv gamma))
      (sfPackageIsoHom source) =
    sfPackageCompose DX (sfPackageIsoHom (sfPackageIsoApp b K)) (sfPackageIsoInv gamma')
```

### sfPackageCommonStagePurity

```lean
def sfPackageCommonStagePurity
    (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) :
    @Iso _ (ConstructibleExceptionalCoefficients.category P.coefficients.l
      P.coefficients.Qbar X (.rational (ConstructibleExceptionalCoefficients.commonField
        P.coefficients.l P.coefficients.Qbar K.stage)))
    ((sfPackageFunctorObject (rationalSource P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
        P.coefficients.Qbar K.stage) f d)) K.obj)
      ((sfPackageFunctorObject (S.ring.operation c (.rational
        (ConstructibleExceptionalCoefficients.commonField
        P.coefficients.l P.coefficients.Qbar K.stage))).G) K.obj) := by
  have e := smallModelIso (stageSetting P K.stage) f c S d K.obj
  dsimp only [stageSetting, AdicSmoothDualizing.fieldIndex,
    commonModelField, commonModelAlgebra, commonModelFinite] at e
  exact e
```

### SfPackageCommonOrientation

```lean
def SfPackageCommonOrientation (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) : Prop :=
  let CX := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar X .closed
  let CY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y .closed
  let DY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y (.rational (ConstructibleExceptionalCoefficients.commonField
      P.coefficients.l P.coefficients.Qbar K.stage))
  let A := S.ring.operation c .closed
  let B := S.ring.operation c (.rational (ConstructibleExceptionalCoefficients.commonField
    P.coefficients.l P.coefficients.Qbar K.stage))
  let H := commonSource P.coefficients.l P.coefficients.Qbar f d
  let HY := rationalSource P.coefficients.l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
      P.coefficients.Qbar K.stage) f d
  let J := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := Y) K.stage
  let q := (S.common.commonComparison c K.stage).q
  ∃ e : @Iso _ CX (sfPackageFunctorObject A.G K) (sfPackageFunctorObject H K),
    sfPackageIsoInv e = sfPackageIsoHom (commonIso P f c S d K) ∧
    sfPackageCompose CY (sfPackageFunctorMap A.F (sfPackageIsoInv e))
        (sfPackageNatTransApp A.adjunction.counit K) =
      sfPackageCompose CY
        (sfPackageFunctorMap A.F
          (sfPackageIsoHom (commonSourceComparison P.coefficients.l
            P.coefficients.Qbar f d K)))
        (sfPackageCompose CY
          (sfPackageIsoInv (sfPackageIsoApp q (sfPackageFunctorObject HY K.obj)))
          (sfPackageFunctorMap J
            (sfPackageTransportHomCategory _ _ (commonCategory_eq P Y K.stage)
              (sfPackageCompose DY
                (sfPackageFunctorMap B.F (sfPackageIsoHom (sfPackageCommonStagePurity P f c S d K)))
                (sfPackageNatTransApp B.adjunction.counit K.obj)))))
```

### sfPackageFunctorObject

```lean
abbrev sfPackageFunctorObject {B : Type a} {C : Type b}
    {bcat : Category.{v} B} {ccat : Category.{w} C}
    (F : @CategoryTheory.Functor B bcat C ccat) (K : B) : C :=
  @CategoryTheory.Functor.obj B bcat C ccat F K
```

### sfPackageFunctorMap

```lean
abbrev sfPackageFunctorMap {B : Type a} {C : Type b}
    {bcat : Category.{v} B} {ccat : Category.{w} C}
    (F : @CategoryTheory.Functor B bcat C ccat) {K L : B}
    (t : @Quiver.Hom B bcat.toQuiver K L) :
    @Quiver.Hom C ccat.toQuiver (sfPackageFunctorObject F K) (sfPackageFunctorObject F L) :=
  @CategoryTheory.Functor.map B bcat C ccat F K L t
```

### sfPackageIsoHom

```lean
abbrev sfPackageIsoHom {B : Type a} {cat : Category.{v} B} {K L : B}
    (e : @Iso B cat K L) : @Quiver.Hom B cat.toQuiver K L :=
  @Iso.hom B cat K L e
```

### sfPackageIsoInv

```lean
abbrev sfPackageIsoInv {B : Type a} {cat : Category.{v} B} {K L : B}
    (e : @Iso B cat K L) : @Quiver.Hom B cat.toQuiver L K :=
  @Iso.inv B cat K L e
```

### sfPackageNatTransApp

```lean
abbrev sfPackageNatTransApp {B : Type a} {C : Type b}
    {bcat : Category.{v} B} {ccat : Category.{w} C}
    {F G : @CategoryTheory.Functor B bcat C ccat}
    (t : @CategoryTheory.NatTrans B bcat C ccat F G) (K : B) :
    @Quiver.Hom C ccat.toQuiver (sfPackageFunctorObject F K) (sfPackageFunctorObject G K) :=
  @CategoryTheory.NatTrans.app B bcat C ccat F G t K
```

### sfPackageIsoApp

```lean
abbrev sfPackageIsoApp {B : Type a} {C : Type b}
    {bcat : Category.{v} B} {ccat : Category.{w} C}
    {F G : @CategoryTheory.Functor B bcat C ccat}
    (e : @Iso (@CategoryTheory.Functor B bcat C ccat)
      (@CategoryTheory.Functor.category B bcat C ccat) F G) (K : B) :
    @Iso C ccat (sfPackageFunctorObject F K) (sfPackageFunctorObject G K) :=
  @CategoryTheory.Iso.app B bcat C ccat F G e K
```

### sfPackageCompose

```lean
abbrev sfPackageCompose {B : Type a} (cat : Category.{v} B) {K L M : B}
    (t : @Quiver.Hom B cat.toQuiver K L) (s : @Quiver.Hom B cat.toQuiver L M) :
    @Quiver.Hom B cat.toQuiver K M :=
  @CategoryStruct.comp B cat.toCategoryStruct K L M t s
```

### sfPackageTransportHomCategory

```lean
def sfPackageTransportHomCategory {B : Type a} (cat cat' : Category.{b} B)
    (h : cat = cat') {K L : B} (t : @Quiver.Hom B cat.toQuiver K L) :
    @Quiver.Hom B cat'.toQuiver K L := h ▸ t
```

## Users

The downstream scans with --allow-missing and --uses for all eight changed
definitions report zero current downstream Lean modules. A separate lean/ and
quarantine/ search finds no Lean importer or consumer. The DAG parent
prop-functor-package still requires this node; its attachment and unit route are
preserved. The archive is restored, not withdrawn or deleted. There are no forced
consumer adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | V6 | Restore and repair reduction coordinates and native category elaboration. |

## Status

landed 20261026T024150-L-642524 2026-10-26 (merge of deliver/V6/Sheaf.Paper.NormalizedOrientationPerfectDuality)
