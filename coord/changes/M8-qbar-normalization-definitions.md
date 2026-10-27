# QbarCoefficientSmoothBaseChange normalization clauses

## Reason

The proof repeatedly expands the four large normalization clauses while checking
record construction. Name precisely those propositions so the records can be
checked through compact interfaces. The operation abbreviations and their bodies
remain verbatim. No mathematical data or proof obligation changes.

## Old

The four original record proof fields, verbatim:

```lean
  push_eq : ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) U,
    HEq (push.hom.app K).hom
      (      (tensorModel l Ω a V).hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) V).map
          ((pushModel l (pbcFiniteField.{u} l Ω E) q).hom.app K.obj) ≫
        (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).hom.app K.obj ≫
        (pushModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).obj K.obj) ≫
        (sbcAmbientPush l (pbcFiniteField.{u} l Ω M) q).map
          ((tensorModel l Ω a U).inv.app K.obj))

  pull_eq : ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) V,
    HEq (pull.hom.app K).hom
      (      (tensorModel l Ω a U).hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).map
          ((pullModel l (pbcFiniteField.{u} l Ω E) q).hom.app K) ≫
        (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).inv.app K.obj ≫
        (pbcActualCompletedPull q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω M))).map
          ((tensorModel l Ω a V).inv.app K.obj) ≫
        (pullModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          (⟨(pbcAmbientScalarExtension l Ω V a).obj K.obj,
            pbcAmbientCompleteTensor_preserves l Ω V a K⟩))

  leftBeta_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (leftBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) f).obj
            ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((cf a).pull.hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K) ≫
            (sbcPull l (pbcFiniteField.{u} l Ω M) f).map ((cg a).push.hom.app K))

  rightBeta_eq : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (rightBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) h).obj
            ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((ch a).push.hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K) ≫
            (sbcPush l (pbcFiniteField.{u} l Ω M) h).map ((ce a).pull.hom.app K))
```

The original module uses the default generated size, injectivity and
constructor-index auxiliaries for `IntegralComparisons` and `Presentation`.

## New

The named propositions contain the same clauses:

```lean
@[irreducible] def IntegralPushNormalization (push : sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω V a ≅
    pbcAmbientCompleteIntegralTransition l Ω U a ⋙
      sbcPush l (pbcFiniteField.{u} l Ω M) q) : Prop :=
  ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) U,
    HEq (push.hom.app K).hom
      ((tensorModel l Ω a V).hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) V).map
          ((pushModel l (pbcFiniteField.{u} l Ω E) q).hom.app K.obj) ≫
        (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).hom.app K.obj ≫
        (pushModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).obj K.obj) ≫
        (sbcAmbientPush l (pbcFiniteField.{u} l Ω M) q).map
          ((tensorModel l Ω a U).inv.app K.obj))

@[irreducible] def IntegralPullNormalization (pull : sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω U a ≅
    pbcAmbientCompleteIntegralTransition l Ω V a ⋙
      sbcPull l (pbcFiniteField.{u} l Ω M) q) : Prop :=
  ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) V,
    HEq (pull.hom.app K).hom
      ((tensorModel l Ω a U).hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).map
          ((pullModel l (pbcFiniteField.{u} l Ω E) q).hom.app K) ≫
        (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).inv.app K.obj ≫
        (pbcActualCompletedPull q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω M))).map
          ((tensorModel l Ω a V).inv.app K.obj) ≫
        (pullModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          (⟨(pbcAmbientScalarExtension l Ω V a).obj K.obj,
            pbcAmbientCompleteTensor_preserves l Ω V a K⟩))

@[irreducible] def LeftBetaNormalization
    (cf : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω f a)
    (cg : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω g a)
    (leftBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)) : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (leftBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) f).obj
            ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((cf a).pull.hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K) ≫
            (sbcPull l (pbcFiniteField.{u} l Ω M) f).map ((cg a).push.hom.app K))

@[irreducible] def RightBetaNormalization
    (ch : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω h a)
    (ce : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω e a)
    (rightBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)) : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (rightBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) h).obj
            ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((ch a).push.hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K) ≫
            (sbcPush l (pbcFiniteField.{u} l Ω M) h).map ((ce a).pull.hom.app K))
```

The four corresponding record fields are now:

```lean
  push_eq : IntegralPushNormalization l Ω q a push
  pull_eq : IntegralPullNormalization l Ω q a pull
  leftBeta_eq : LeftBetaNormalization l Ω cf cg leftBeta
  rightBeta_eq : RightBetaNormalization l Ω ch ce rightBeta
```

Unfolding each predicate gives its old field clause exactly. Every data field
and both original theorem signatures are preserved. This definitional packaging
is submitted for independent target-meaning review.

The module also disables four unused generated auxiliaries:

```lean
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
```

Constructors, recursors, fields and mathematical data remain unchanged. No
external consumer uses the omitted auxiliaries. The declaration-only benchmark
compiled in 17.9 seconds with these options, versus 25.8 seconds with defaults.

## Users

`tools/downstream.py` reported zero importing modules. Its `--uses` checks for
`IntegralComparisons`, `Presentation`, and all three operation abbreviations
found only this item. A full source search found no qualified external use.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | explicitly unfold the named normalization clauses when constructing the same proof fields |

No other module is adapted. No adopted `WeilConjectures` declaration changes.
A compiled compatibility diagnostic recovered all four original clauses verbatim
by unfolding the new predicates. The complete module with both original proofs compiled in 39.6 seconds, with no warnings. The original atStage definition and all original theorem signatures are retained.

## Status

landed 20261022T040208-L-2831428 2026-10-22 (merge of deliver/M8/Sheaf.Paper.QbarCoefficientSmoothBaseChange)
