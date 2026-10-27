# AlgebraicGeometry.Scheme.pbcPurityTateScalarComponent

## Reason

The complete three-hole proof initially typechecked but took 83.5 seconds. The expensive
naturality step rebuilt the six-factor model comparison and checked it against its
objectwise presentation repeatedly. Assemble those same factors into the natural
isomorphism `pbcPurityTateScalarModel` once and take its components. This is the structured
comparison interface for the existing data, not a change of normalization or proof route.
`purityTateScalarComponent_eq` proves by reflexivity that each new component equals the
previous six-factor preimage expression, including its inverse. No data is taken from a
new unproved existence theorem.

## Old

```lean
def pbcPurityTateScalarComponent (m : ℤ)
    (K : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i W).obj ((pbcTateAmbient l W E m).obj K.obj) ≅
      (pbcTateAmbient l W F m).obj ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) :=
  (purCoefficientModel l F W).functor.preimageIso
    ((purScalarModel l E F i W).app ((pbcTateAmbient l W E m).obj K.obj) ≪≫
      (pbcPurityDerivedScalarModel l E F i W).app
        ((purCoefficientModel l E W).functor.obj ((pbcTateAmbient l W E m).obj K.obj)) ≪≫
      (completedDerivedScalarExtension l E F i W).mapIso
        ((pbcPurityTateModel l E W m).app K.obj) ≪≫
      (integralTwistOrdinaryBeta l E F i W m).app
        ⟨(purCoefficientModel l E W).functor.obj K.obj, pbcPurityModel_mem l E W K⟩ ≪≫
      (integralSheafTwist l F W m).mapDerivedCategory.mapIso
        (((pbcPurityDerivedScalarModel l E F i W).app
          ((purCoefficientModel l E W).functor.obj K.obj)).symm ≪≫
          ((purScalarModel l E F i W).app K.obj).symm) ≪≫
      ((pbcPurityTateModel l F W m).app
        ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj)).symm)
```

The previously inferred ordinary Tate-model type was:

```lean
def pbcPurityOrdinaryTateModel (m : ℤ) :=
  (pbcPurityOrdinaryTateModel_existsUnique l E W m).exists.choose
```

## New

```lean
def pbcPurityTateScalarModel (m : ℤ) :
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) ⋙
        pbcTateAmbient l W E m ⋙ pbcEmbeddingAmbientTensor l E F i W ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) ⋙
        pbcEmbeddingAmbientTensor l E F i W ⋙ pbcTateAmbient l W F m := by
  let I := ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E))
  let PE := (purCoefficientModel l E W).functor
  let PF := (purCoefficientModel l F W).functor
  let S := pbcEmbeddingAmbientTensor l E F i W
  let TE := pbcTateAmbient l W E m
  let TF := pbcTateAmbient l W F m
  let B := (integralSheafTwist l F W m).mapDerivedCategory
  let J := (sfIntegralConstructible l E W).lift (I ⋙ PE)
    (fun M ↦ pbcPurityModel_mem l E W M)
  let e : (I ⋙ TE ⋙ S) ⋙ PF ≅ (I ⋙ S ⋙ TF) ⋙ PF :=
    Functor.isoWhiskerLeft (I ⋙ TE) (purScalarModel l E F i W) ≪≫
      Functor.isoWhiskerLeft (I ⋙ TE ⋙ PE) (pbcPurityDerivedScalarModel l E F i W) ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft I (pbcPurityTateModel l E W m))
        (completedDerivedScalarExtension l E F i W) ≪≫
      Functor.isoWhiskerLeft J (integralTwistOrdinaryBeta l E F i W m) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (I ⋙ PE) (pbcPurityDerivedScalarModel l E F i W).symm ≪≫
          Functor.isoWhiskerLeft I (purScalarModel l E F i W).symm) B ≪≫
      (Functor.isoWhiskerLeft (I ⋙ S) (pbcPurityTateModel l F W m)).symm
  exact Functor.fullyFaithfulCancelRight PF e

def pbcPurityTateScalarComponent (m : ℤ)
    (K : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i W).obj ((pbcTateAmbient l W E m).obj K.obj) ≅
      (pbcTateAmbient l W F m).obj ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) :=
  (pbcPurityTateScalarModel l E F i W m).app K
```

The same inferred type is now written explicitly, avoiding repeated inference through the
normalization predicate of the unique-existence theorem:

```lean
def pbcPurityOrdinaryTateModel (m : ℤ) :
    pbcTateSheafTensor l W E m ⋙ purOrdinaryCoefficientModel l E W ≅
      purOrdinaryCoefficientModel l E W ⋙ integralSheafTwist l E W m :=
  (pbcPurityOrdinaryTateModel_existsUnique l E W m).exists.choose
```

Local irreducibility attributes retain abstract interfaces for this model, its components,
the chosen ordinary Tate model, coefficient-model equivalence, scalar-model bridges,
integral Tate tensor, ambient Tate functor, completed pullback, scalar coefficient map,
and the later stage functors. They affect only this
file's elaboration. Public signatures, public imports and all target statements stay
identical. Three original theorem holes are filled; none are added. The geometric-bounds
proof also reuses the existing `PurCompactSupport.coefficientPrimeUnit` theorem.

## Users

`python3 tools/downstream.py Sheaf.Paper.RationalPurityPresentation --uses
pbcPurityTateScalarComponent pbcPurityTwistedScalarComponent` reports no downstream modules
and only this module as a textual user of either name. The twisted scalar comparison now
uses the coherent Tate model directly. Its displayed components remain definitionally the
same, as checked by the reflexivity lemma. Two proved private generator lemmas and a private scalar-lift record avoid expanding
concrete tensor-Hom operations repeatedly. The record contains the actual Hom map and its
existing functor and generator laws. Its functor keeps those exact object and Hom maps.
A generic naturality theorem for this record is proved over abstract linear categories and
then instantiated with `pbcRationalScalarHom`; no map or proof law is postulated. No consumer adaptation is required. The node
attachment, all planned parent dependencies, and the unit route are preserved. Any target
statement review reopened by this definition refactor has the reflexivity lemma as its
precise equivalence certificate; no target hypothesis or conclusion is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalPurityPresentation | W3 | Same normalized Tate maps via a coherent model; three theorem proofs filled. |

## Status

landed 20261026T071419-L-3927078 2026-10-26 (merge of deliver/W3/Sheaf.Paper.RationalPurityPresentation)
