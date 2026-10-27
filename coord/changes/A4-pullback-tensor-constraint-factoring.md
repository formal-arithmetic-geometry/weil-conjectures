# Derived pullback tensor constraint module factoring

## Reason

While A4 was verifying its item, the D2 landing was reverted after the global build
reported the obsolete private identifier `semilinearTensorIso_localize`. The missing
split modules made the first delivery fail its import-source check. This packet is
rebased onto the reverted live item. It factors the existing 59 constraint declarations
into a publicly re-exported module and the proved generic reduction calculations into
a proof-only module. The rational comparison proof uses the existing public
`OperationsScalarLocalization.bilinearComparison_existsUnique`.

Every data definition was checked as a verbatim substring of the original source.
All 59 public signatures below are verbatim and remain publicly available through
`Sheaf.Paper.DerivedPullbackTensorIso`. No data construction, reducibility attribute,
simp attribute, instance, hypothesis or conclusion changes. The new irreducibility
annotations are local proof-cache settings, not exported changes. No target statement
or adopted source-library declaration changes.

## Old

Owner: `Sheaf.Paper.DerivedPullbackTensorIso`, namespace `WeilConjectures`.
The section parameters `l`, `E`, `Ω`, universes and instances are unchanged.

```lean
def pullbackTensorIntegralComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    (@constructibleIntegralPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY) ≅
      (@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY) ⋙ (@constructibleIntegralPullback l _
        E _ _ _ Z X h hZ hX)

theorem pullbackTensorRationalComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y) :
    ∃! e : ((@rationalDerivedPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@rationalDerivedPullback l _ E _ _ _ Z X h hZ hX)).obj (((@rationalDerivedPullback l _ E _ _
        _ X Y f hX hY)).obj M),
      HEq e.hom ((sfRationalConstructibleLocalization l E Z).map
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M.obj))

def pullbackTensorRationalComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y)

theorem pullbackTensorCommonComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    ∃! e : ((@commonStageDerivedPullback l _ Ω _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).obj (((@commonStageDerivedPullback l _
        Ω _ _ _ X Y f hX hY)).obj M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L),
        HEq e.hom (ofHom (commonStagePullbackObject l Ω (h ≫ f) M)
          (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f M)) L hM hM
          ((commonStagePullbackComparison l Ω (h ≫ f) M L hM).hom ≫
            ((@pullbackTensorRationalComposition l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X
              Y Z f h hX hY
              hZ)
              (M.toStage hM)).hom ≫
            ((@rationalDerivedPullback l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ Z
              X h hZ hX)).map
              (commonStagePullbackComparison l Ω f M L hM).inv ≫
            (commonStagePullbackComparison l Ω h
              (commonStagePullbackObject l Ω f M) L hM).inv))

def pullbackTensorCommonComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)

def canonicalIntegralPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop

def canonicalRationalPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfRationalConstructibleCategory l E Y) : Prop

def canonicalCommonStagePullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y) : Prop

def pullbackTensorIntegralReductionTensor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (pullbackTensorCalculus l E W).reduction.obj
      (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)).obj ≅
    (pullbackTensorCalculus l E W).systemClosed.tensor.obj
      ((pullbackTensorCalculus l E W).reduction.obj M.obj,
       (pullbackTensorCalculus l E W).reduction.obj N.obj)

def pullbackTensorIntegralReductionPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M : sfIntegralConstructibleCategory l E Y) :
    (pullbackTensorCalculus l E X).reduction.obj
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M).obj ≅
    (pullbackTensorSequenceDerived l E f).obj
      ((pullbackTensorCalculus l E Y).reduction.obj M.obj)

def canonicalIntegralPullbackTensor_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop

theorem pullbackTensorIntegralAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (((@constructibleIntegralTensor l _
      E _ _ _ W hW)).obj (M,N),P)
      ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,((@constructibleIntegralTensor l _ E
        _ _ _ W hW)).obj (N,P)),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M
          (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,P))).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N P).hom) =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW)
        (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)) P).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom (𝟙 _)) ≫
        ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator
          ((pullbackTensorCalculus l E W).reduction.obj M.obj)
          ((pullbackTensorCalculus l E W).reduction.obj N.obj)
          ((pullbackTensorCalculus l E W).reduction.obj P.obj)).hom

def pullbackTensorIntegralAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W)

theorem pullbackTensorRationalAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (((@rationalDerivedTensor l _ E _ _ _ W
      hW)).obj (M,N),P) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,((@rationalDerivedTensor l _ E _ _ _ W
        hW)).obj (N,P)),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralAssociator l _ E _ _ _ W hW) M.obj N.obj P.obj).hom)

def pullbackTensorRationalAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W)

theorem pullbackTensorIntegralBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,M),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N M).hom =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom ≫
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel).hom.app
            ((pullbackTensorCalculus l E W).reduction.obj M.obj,
             (pullbackTensorCalculus l E W).reduction.obj N.obj)

def pullbackTensorIntegralBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W)

theorem pullbackTensorRationalBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (N,M),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralBraiding l _ E _ _ _ W hW) M.obj N.obj).hom)

def pullbackTensorRationalBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W)

def pullbackTensorCommonLeft (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W
      (commonStageTensorObject l Ω W M N) P).stage ≤ L)

def pullbackTensorCommonRight (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W M
      (commonStageTensorObject l Ω W N P)).stage ≤ L)

theorem pullbackTensorCommonAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
      _ W hW)).obj (M,N),P) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,((@commonStageDerivedTensor l _ Ω _ _ _
        W hW)).obj (N,P)),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P).stage ≤ L) (hT :
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
          (((@pullbackTensorCommonLeft l _ Ω _ _ _ W hW) M N P L hS).hom ≫
            ((@pullbackTensorRationalAssociator l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (N.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (P.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).2.trans hS))).hom ≫
            ((@pullbackTensorCommonRight l _ Ω _ _ _ W hW) M N P L hT).inv))

def pullbackTensorCommonAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)

theorem pullbackTensorCommonBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,N) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (N,M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W M N).stage ≤ L) (hT : (commonStageTensorObject l Ω W N
          M).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M N)
          (commonStageTensorObject l Ω W N M) L hS hT
          ((commonStageTensorComparison l Ω W M N L hS).hom ≫
            ((@pullbackTensorRationalBraiding l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                hS)) (N.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                N.stage).2.trans hS))).hom ≫
            (commonStageTensorComparison l Ω W N M L hT).inv))

def pullbackTensorCommonBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W)

theorem pullbackTensorIntegralUnit_constructible (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit)

def pullbackTensorIntegralUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] : sfIntegralConstructibleCategory l E W

theorem pullbackTensorIntegralUnit_counit (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] : IsIso ((pullbackTensorCalculus l E
      W).adjunction.counit.app
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit)

def pullbackTensorIntegralUnitReduction (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    (pullbackTensorCalculus l E W).reduction.obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W
      hW)).obj ≅
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit

def pullbackTensorRationalUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]

theorem pullbackTensorIntegralLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorIntegralUnit l _ E
      _ _ _ W hW),M) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) ((@pullbackTensorIntegralUnit l _
          E _ _ _ W hW)) M).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom

def pullbackTensorIntegralLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W)

theorem pullbackTensorRationalLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorRationalUnit l _ E _ _ _
      W hW),M) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ W hW) M.obj).hom)

def pullbackTensorRationalLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W)

theorem pullbackTensorIntegralRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorIntegralUnit l _
      E _ _ _ W hW)) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M ((@pullbackTensorIntegralUnit l
          _ E _ _ _ W hW))).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom

def pullbackTensorIntegralRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W)

theorem pullbackTensorRationalRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorRationalUnit l _ E _ _
      _ W hW)) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ W hW) M.obj).hom)

def pullbackTensorRationalRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W)

theorem pullbackTensorRationalScalarUnit_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    ∃! e : (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((@pullbackTensorRationalUnit l _ E _ _ _ W hW)) ≅ (@pullbackTensorRationalUnit l _ L _ _
            _ W hW),
      ∀ M : sfRationalConstructibleCategory l E W,
        ((rationalTensorScalarComparison l E L ι W).hom.app ((@pullbackTensorRationalUnit l _ E _ _
          _ W hW),M) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom e.hom (𝟙 _)) ≫
          ((@pullbackTensorRationalLeftUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalLeftUnitor l
              _ E _ _ _ W hW) M).hom) ∧
        ((rationalTensorScalarComparison l E L ι W).hom.app (M,(@pullbackTensorRationalUnit l _ E _
          _ _ W hW)) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom (𝟙 _) e.hom) ≫
          ((@pullbackTensorRationalRightUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalRightUnitor l
              _ E _ _ _ W hW) M).hom)

def pullbackTensorRationalScalarUnit
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]

def pullbackTensorCommonUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
      generalAlgebraicallyClosedConstructibleCategory l
      Ω W

def pullbackTensorCommonUnitStage (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage ≤ L) :
    ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).toStage h ≅
      (@pullbackTensorRationalUnit l _
        (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W hW)

theorem pullbackTensorCommonLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)),M) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW)) M) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω _ _ _
            W hW)).stage
          M.stage).2.trans h)
          ((commonStageTensorComparison l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω
                  _ _ _ W hW)).stage M.stage).1.trans h)).hom (𝟙 _)) ≫
            ((@pullbackTensorRationalLeftUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage M.stage).2.trans h))).hom))

def pullbackTensorCommonLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W)

theorem pullbackTensorCommonRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (M,((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW))) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage ((@pullbackTensorCommonUnit l _
            Ω _ _ _ W hW)).stage).1.trans h)
          ((commonStageTensorComparison l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom (𝟙 _) ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                  ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).2.trans h)).hom) ≫
            ((@pullbackTensorRationalRightUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).1.trans h))).hom))

def pullbackTensorCommonRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W)

def canonicalIntegralPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

def canonicalRationalPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

def canonicalCommonStagePullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

def canonicalIntegralPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

theorem canonicalIntegralPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_associative l _ E _ _ _ X Y f hX hY)

def canonicalRationalPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

theorem canonicalRationalPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_associative l _ E _ _ _ X Y f hX hY)

def canonicalCommonStagePullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

def canonicalIntegralPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

theorem canonicalIntegralPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_braiding l _ E _ _ _ X Y f hX hY)

def canonicalRationalPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

theorem canonicalRationalPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_braiding l _ E _ _ _ X Y f hX hY)

def canonicalCommonStagePullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop
```

## New

The same signatures and definition bodies now belong to
`Sheaf.Paper.DerivedPullbackTensorConstraints`; the item publicly imports it.

```lean
def pullbackTensorIntegralComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    (@constructibleIntegralPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY) ≅
      (@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY) ⋙ (@constructibleIntegralPullback l _
        E _ _ _ Z X h hZ hX)

theorem pullbackTensorRationalComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y) :
    ∃! e : ((@rationalDerivedPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@rationalDerivedPullback l _ E _ _ _ Z X h hZ hX)).obj (((@rationalDerivedPullback l _ E _ _
        _ X Y f hX hY)).obj M),
      HEq e.hom ((sfRationalConstructibleLocalization l E Z).map
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M.obj))

def pullbackTensorRationalComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y)

theorem pullbackTensorCommonComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    ∃! e : ((@commonStageDerivedPullback l _ Ω _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).obj (((@commonStageDerivedPullback l _
        Ω _ _ _ X Y f hX hY)).obj M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L),
        HEq e.hom (ofHom (commonStagePullbackObject l Ω (h ≫ f) M)
          (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f M)) L hM hM
          ((commonStagePullbackComparison l Ω (h ≫ f) M L hM).hom ≫
            ((@pullbackTensorRationalComposition l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X
              Y Z f h hX hY
              hZ)
              (M.toStage hM)).hom ≫
            ((@rationalDerivedPullback l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ Z
              X h hZ hX)).map
              (commonStagePullbackComparison l Ω f M L hM).inv ≫
            (commonStagePullbackComparison l Ω h
              (commonStagePullbackObject l Ω f M) L hM).inv))

def pullbackTensorCommonComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)

def canonicalIntegralPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop

def canonicalRationalPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfRationalConstructibleCategory l E Y) : Prop

def canonicalCommonStagePullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y) : Prop

def pullbackTensorIntegralReductionTensor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (pullbackTensorCalculus l E W).reduction.obj
      (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)).obj ≅
    (pullbackTensorCalculus l E W).systemClosed.tensor.obj
      ((pullbackTensorCalculus l E W).reduction.obj M.obj,
       (pullbackTensorCalculus l E W).reduction.obj N.obj)

def pullbackTensorIntegralReductionPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M : sfIntegralConstructibleCategory l E Y) :
    (pullbackTensorCalculus l E X).reduction.obj
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M).obj ≅
    (pullbackTensorSequenceDerived l E f).obj
      ((pullbackTensorCalculus l E Y).reduction.obj M.obj)

def canonicalIntegralPullbackTensor_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop

theorem pullbackTensorIntegralAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (((@constructibleIntegralTensor l _
      E _ _ _ W hW)).obj (M,N),P)
      ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,((@constructibleIntegralTensor l _ E
        _ _ _ W hW)).obj (N,P)),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M
          (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,P))).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N P).hom) =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW)
        (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)) P).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom (𝟙 _)) ≫
        ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator
          ((pullbackTensorCalculus l E W).reduction.obj M.obj)
          ((pullbackTensorCalculus l E W).reduction.obj N.obj)
          ((pullbackTensorCalculus l E W).reduction.obj P.obj)).hom

def pullbackTensorIntegralAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W)

theorem pullbackTensorRationalAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (((@rationalDerivedTensor l _ E _ _ _ W
      hW)).obj (M,N),P) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,((@rationalDerivedTensor l _ E _ _ _ W
        hW)).obj (N,P)),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralAssociator l _ E _ _ _ W hW) M.obj N.obj P.obj).hom)

def pullbackTensorRationalAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W)

theorem pullbackTensorIntegralBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,M),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N M).hom =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom ≫
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel).hom.app
            ((pullbackTensorCalculus l E W).reduction.obj M.obj,
             (pullbackTensorCalculus l E W).reduction.obj N.obj)

def pullbackTensorIntegralBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W)

theorem pullbackTensorRationalBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (N,M),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralBraiding l _ E _ _ _ W hW) M.obj N.obj).hom)

def pullbackTensorRationalBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W)

def pullbackTensorCommonLeft (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W
      (commonStageTensorObject l Ω W M N) P).stage ≤ L)

def pullbackTensorCommonRight (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W M
      (commonStageTensorObject l Ω W N P)).stage ≤ L)

theorem pullbackTensorCommonAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
      _ W hW)).obj (M,N),P) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,((@commonStageDerivedTensor l _ Ω _ _ _
        W hW)).obj (N,P)),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P).stage ≤ L) (hT :
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
          (((@pullbackTensorCommonLeft l _ Ω _ _ _ W hW) M N P L hS).hom ≫
            ((@pullbackTensorRationalAssociator l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (N.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (P.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).2.trans hS))).hom ≫
            ((@pullbackTensorCommonRight l _ Ω _ _ _ W hW) M N P L hT).inv))

def pullbackTensorCommonAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)

theorem pullbackTensorCommonBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,N) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (N,M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W M N).stage ≤ L) (hT : (commonStageTensorObject l Ω W N
          M).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M N)
          (commonStageTensorObject l Ω W N M) L hS hT
          ((commonStageTensorComparison l Ω W M N L hS).hom ≫
            ((@pullbackTensorRationalBraiding l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                hS)) (N.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                N.stage).2.trans hS))).hom ≫
            (commonStageTensorComparison l Ω W N M L hT).inv))

def pullbackTensorCommonBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W)

theorem pullbackTensorIntegralUnit_constructible (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit)

def pullbackTensorIntegralUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] : sfIntegralConstructibleCategory l E W

theorem pullbackTensorIntegralUnit_counit (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] : IsIso ((pullbackTensorCalculus l E
      W).adjunction.counit.app
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit)

def pullbackTensorIntegralUnitReduction (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    (pullbackTensorCalculus l E W).reduction.obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W
      hW)).obj ≅
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit

def pullbackTensorRationalUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]

theorem pullbackTensorIntegralLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorIntegralUnit l _ E
      _ _ _ W hW),M) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) ((@pullbackTensorIntegralUnit l _
          E _ _ _ W hW)) M).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom

def pullbackTensorIntegralLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W)

theorem pullbackTensorRationalLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorRationalUnit l _ E _ _ _
      W hW),M) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ W hW) M.obj).hom)

def pullbackTensorRationalLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W)

theorem pullbackTensorIntegralRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorIntegralUnit l _
      E _ _ _ W hW)) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M ((@pullbackTensorIntegralUnit l
          _ E _ _ _ W hW))).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom

def pullbackTensorIntegralRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W)

theorem pullbackTensorRationalRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorRationalUnit l _ E _ _
      _ W hW)) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ W hW) M.obj).hom)

def pullbackTensorRationalRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W)

theorem pullbackTensorRationalScalarUnit_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    ∃! e : (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((@pullbackTensorRationalUnit l _ E _ _ _ W hW)) ≅ (@pullbackTensorRationalUnit l _ L _ _
            _ W hW),
      ∀ M : sfRationalConstructibleCategory l E W,
        ((rationalTensorScalarComparison l E L ι W).hom.app ((@pullbackTensorRationalUnit l _ E _ _
          _ W hW),M) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom e.hom (𝟙 _)) ≫
          ((@pullbackTensorRationalLeftUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalLeftUnitor l
              _ E _ _ _ W hW) M).hom) ∧
        ((rationalTensorScalarComparison l E L ι W).hom.app (M,(@pullbackTensorRationalUnit l _ E _
          _ _ W hW)) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom (𝟙 _) e.hom) ≫
          ((@pullbackTensorRationalRightUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalRightUnitor l
              _ E _ _ _ W hW) M).hom)

def pullbackTensorRationalScalarUnit
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]

def pullbackTensorCommonUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
      generalAlgebraicallyClosedConstructibleCategory l
      Ω W

def pullbackTensorCommonUnitStage (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage ≤ L) :
    ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).toStage h ≅
      (@pullbackTensorRationalUnit l _
        (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W hW)

theorem pullbackTensorCommonLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)),M) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW)) M) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω _ _ _
            W hW)).stage
          M.stage).2.trans h)
          ((commonStageTensorComparison l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω
                  _ _ _ W hW)).stage M.stage).1.trans h)).hom (𝟙 _)) ≫
            ((@pullbackTensorRationalLeftUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage M.stage).2.trans h))).hom))

def pullbackTensorCommonLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W)

theorem pullbackTensorCommonRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (M,((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW))) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage ((@pullbackTensorCommonUnit l _
            Ω _ _ _ W hW)).stage).1.trans h)
          ((commonStageTensorComparison l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom (𝟙 _) ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                  ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).2.trans h)).hom) ≫
            ((@pullbackTensorRationalRightUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).1.trans h))).hom))

def pullbackTensorCommonRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W)

def canonicalIntegralPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

def canonicalRationalPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

def canonicalCommonStagePullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

def canonicalIntegralPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

theorem canonicalIntegralPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_associative l _ E _ _ _ X Y f hX hY)

def canonicalRationalPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

theorem canonicalRationalPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_associative l _ E _ _ _ X Y f hX hY)

def canonicalCommonStagePullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

def canonicalIntegralPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

theorem canonicalIntegralPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_braiding l _ E _ _ _ X Y f hX hY)

def canonicalRationalPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop

theorem canonicalRationalPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_braiding l _ E _ _ _ X Y f hX hY)

def canonicalCommonStagePullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop
```

## Users

No consumer is adapted. No consumer uses `import all` on the item. The table lists
all direct public/proof importers and additional textual users, whose exported interface stays identical; their
holders are unaffected because their files are not changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.AdicCommonStageHomTranspose | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.AffineSpacePurityComparison | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.ClosedSupportedCupVanishing | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CommonStageFourierTransform | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CommonStageShiftedUnitTensor | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CommonStageTensorBraidingNaturality | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CommonStageTensorLineCoherenceNaturality | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CommonStageTensorRightUnitorNaturality | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CommonTensorBraidingNaturality | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CompactSupportProjectionFormula | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CompletedConstantRightUnit | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CompletedTensorHomTranspose | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CompositionTensorMate | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.ConstantTwistCoefficientComparison | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.ConstructibleProjectionMates | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.CoprojectionCompositionMate | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FiniteCompositorCounit | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FiniteProductNormalForm | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FiniteProperProductMaps | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FiniteProperProductTranspose | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FiniteTripleProductDefinitions | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FixedStalkIdentificationReduction | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FourierArtinSchreierProperties | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FourierTraceFormula | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FourierTrivialCharacterUnit | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.InverseContravariantBidual | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.LisseLocalizationData | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.LisseRationalRealizationData | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.OperationCoefficientActionData | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.OrdinaryDerivedProductLegTransposes | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.PfRefinementCompatibility | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.PodCompletionReindexCoefficientTransition | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.PodCompletionReindexCoherence | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.PodMixedSupportCupProduct | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.ProperProductCounitTranspose | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.PurityCoprojection | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.RationalRealizationTensorComparison | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.RationalTensorSymmetry | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.RationalTwistedPullbackCompositor | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.RegularCoefficientCoherentReduction | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.RelativeKunnethClosedFibre | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.RelativeProductFactors | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.SemilinearExchangeCubeData | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.SemilinearFieldOperationLifts | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.TateTwistIntegralLines | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.TateTwistLocallyFree | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.TensorMateInvertibleInput | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.SixFunctors.CoefVerdierWeilData | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.SixFunctors.OpenBaseChangeSquareData | unchanged; no adaptation | Identical public declarations and definitions |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.AdicProperAdjunctionRealization | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.AdicRealizationFamilyData | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.AdicReindexingCore | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.AdicReindexingFunctoriality | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.AdicReindexingTensor | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.CanonicalTateCommonComparisons | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.CanonicalTateScalarComparisons | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.CommonFrobeniusSquareNormalization | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.CommonStageTensorLineCoherence | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.LisseCohomologyDerivedDual | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.LisseLocalizationLocalFreeness | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.LisseLocalizationRestriction | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.NativeAdicRealizationData | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.ProjectionFormulaCoherence | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.RationalHomScalarTranspose | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.SitePerfectRationalBidual | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.Paper.WeilChosenDualityExchangeData | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.SixFunctors.OpenBaseChangeSquare | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.SixFunctors.RationalRetractEvaluation | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.SixFunctors.TensorExchangePresentation | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unchanged; no adaptation | Transitive textual user; identical re-exported API |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unchanged; no adaptation | Transitive textual user; identical re-exported API |

## Status

landed 20261027T180455-L-3864065 2026-10-27 (merge of deliver/B4/Sheaf.Paper.DerivedPullbackTensorIso)

## Compatibility validation

All 64 direct importers were compiled as unchanged verification copies; no copy
is included in this delivery. Fifty-two ordinary checks passed. The finite Tate
structural coherence check passed diagnostic profiling in 37.5 seconds against
this packet versus 39 seconds against the baseline, after an initial 62-second
run. The eleven other time-limit failures also occur against the published
baseline; report.md names every one. No importer produced a type or signature
error. A concurrent update to ConstantPurityFrobeniusSquare was refreshed and
checked against both environments. No consumer was adapted.

The seven delivered Lean modules compiled. The item has no remaining hole; its
three public theorem signatures are byte-identical to the restored live source.

## Definition node attachments

The following existing records keep their statements, definitions and dependency
fields unchanged; only lean.module and lean.file move to the support module:

- `def-pod-integral-tensor-constraints`
- `def-pod-rational-common-pullback-composition`
- `def-sf-rational-common-tensor-symmetries`
- `def-a1-common-stage-coefficient-unit`

The new unit theorem cites the complete normalized constraint record directly.
Its initial redundant references to the older integral-constraint and unit
records were removed: those records attach the same unchanged declarations and
are retained with corrected module paths. They are not withdrawn or globally
pruned. The redundant references had joined two additional base nodes to a
pre-existing cyclic component and were the six server preflight refusals.
