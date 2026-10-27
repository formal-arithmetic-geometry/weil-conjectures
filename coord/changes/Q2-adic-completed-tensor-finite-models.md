# WeilConjectures.AdicQbarRealization.tensorDescentFiniteRepresentative

## Reason

Separate the finite normalized comparison from common-field descent so the original
one-hole theorem is assembled from two genuine steps of its source argument.
The finite-model step has no common-stage tensorator; the common-lift step takes
all finite chain and derived models as fixed inputs. This is a decomposition,
not a net proof. The old predicates require a complete common-stage realization,
so using them directly would make the finite construction import its own parent.
Transparent parameterized predicates remove this dependency cycle without changing
the original propositions. The archived bad-import error is not reproduced by the current
published build (the unchanged original compiled in 38.4 seconds).

## Old

The original module publicly imported NativeAdicFiniteNormalization, FiniteFieldFiber,
CompletedIntegralConstantMapOfUniverses and CompletedCondensedCoefficients. It defined
tensorStage, tensorIntegralObjectIso and tensorQuotientIso directly, followed by
these three predicates. The relocated comparison definitions were:

```lean
def tensorStage (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⥤
    generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X :=
  sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
    GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E

/-- The recorded object equality between rational tensor on integral objects and
localization of their completed tensor. All maps are the existing operations.
Source: BS Definition 3.4.10 and Remark 6.8.15
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorIntegralObjectIso [∀ x : X, Invertible (l : X.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    (rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K,
       (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L) ≅
    (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) :=
  eqToIso ((rationalDerivedTensor_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).exists.choose_spec.1
    ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K,
     (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L))

/-- Invert precisely the recorded quotient-completion map on constructible pairs.
The four normalization clauses in the presentation fix its entire chain representative.
Source: BS Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorQuotientIso
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (C : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    C.tensor.obj (K.obj, L.obj) ≅
    (integralCompletedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      (K.obj, L.obj) :=
  @asIso _ _ _ _ (C.comparison.app (K.obj, L.obj))
    (C.normalized.2.2.2 K.obj L.obj K.property L.property).2
```

The original predicates were:

```lean
def tensorDescentFiniteBalanceSections (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (_A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) ℤ)
      (p q : ℤ) (U : X.ProEtᵒᵖ) (s : (ring l X R).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((balance.hom.app (P, Q)).f (p + q)).val.app U
      (pbcTensorSection (coefficientMap l X R E)
        (((constructibleTensorTotal l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
            (P, Q)).X (p + q)) U s
        (constructibleTensorTotalSection l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X P Q p q U x y)) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
        ((integralComplex l X R E).obj P) ((integralComplex l X R E).obj Q)
        p q (p + q) rfl U
        (pbcTensorSection (coefficientMap l X R E) (P.X p) U s x)
        (pbcTensorSection (coefficientMap l X R E) (Q.X q) U 1 y)
```

```lean
def tensorDescentFiniteRepresentative (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    (kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj))
    (ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    (pbcDerivedExtend (coefficientMap l X R E)).map
        (completion.model.hom.app (P, Q)) ≫
      ordinary.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      A.closed.tensor.map (Prod.mkHom
        (pbcComplexCounit (coefficientMap l X R E) P.obj)
        (pbcComplexCounit (coefficientMap l X R E) Q.obj)) =
    pbcComplexCounit (coefficientMap l X R E)
        ((constructibleTensorTotal l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
            (P.obj, Q.obj)) ≫
      DerivedCategory.Q.map (balance.hom.app (P.obj, Q.obj)) ≫
      (A.models.iso _ _ _ _ _ (kflat P) (kflat Q)).hom
```

```lean
def tensorDescentFiniteTensorAgreement (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (comparison : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
      ((pbcDerivedExtend (coefficientMap l X R E)).prod
        (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  ∀ K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X,
    HEq (A.tensor.hom.app ((tensorStage l X E).obj K, (tensorStage l X E).obj L))
    (A.closed.tensor.map (Prod.mkHom ((R.integral E).hom.app K) ((R.integral E).hom.app L)) ≫
      comparison.inv.app (K.obj, L.obj) ≫
      (pbcDerivedExtend (coefficientMap l X R E)).map (tensorQuotientIso l X E completion K L).hom ≫
      (R.integral E).inv.app ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) ≫
      (AdicQbarRealization.ordinary l X R).map ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).map (tensorIntegralObjectIso l X E K L).inv) ≫
      (AdicQbarRealization.ordinary l X R).map
        (stageTensor l X (PadicAlgCl l) E
          ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K)
          ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L)).hom)
```

## New

The three comparison definitions tensorStage, tensorIntegralObjectIso and
tensorQuotientIso move verbatim, with their original names, signatures and bodies,
to the new AdicCompletedTensorFiniteModels module. The original module publicly
imports that module, retaining all four of its original public imports.
The three original predicate signatures are identical, and their bodies are
transparent specializations of the new predicates. Their expanded propositions
are definitionally equal to their original propositions:

```lean
def tensorDescentFiniteBalanceSections (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (_A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)) : Prop :=
  tensorFiniteBalanceSections l X R E balance
```

```lean
def tensorDescentFiniteRepresentative (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    (kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj))
    (ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  tensorFiniteRepresentative l X R A.closed A.models E
    completion balance kflat ordinary
```

```lean
def tensorDescentFiniteTensorAgreement (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (comparison : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
      ((pbcDerivedExtend (coefficientMap l X R E)).prod
        (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  tensorFiniteAgreement l X R A.closed A.tensor E completion comparison
```

New public definitions describe finite models before any common-stage tensorator.
CompletedTensorCommonLift retains only common-stage data and its agreement with
the given finite models. The original CompletedTensorRealization,
CompletedTensorFiniteNormalization, CompletedTensorRealizationDescent and final
theorem signatures are unchanged. No target statement or upstream file changes.

## Users

`tools/downstream.py --uses` finds only the item itself for each of the three
predicate names and the three relocated comparison names. The only direct
importer is AdicQbarConstructibleRealization; it sees all existing declarations
through the unchanged original import. The parent copies the normalization
fields, which keep definitionally identical types. No adaptation is required.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | Q2 | Construct original records from finite and common data |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed in the available claim records | Same signatures, transparently equal predicate bodies and reexported comparison definitions; compile unchanged |

## Status

landed 20261027T180734-L-3896912 2026-10-27 (merge of deliver/Q2/Sheaf.Paper.AdicCompletedTensorRealizationDescent)
