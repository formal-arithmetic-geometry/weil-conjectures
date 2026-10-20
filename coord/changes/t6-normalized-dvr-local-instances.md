# normalizedDVREffectivityLocal1, normalizedDVREffectivityLocal2, normalizedDVREffectivityLocal3

## Reason

The proof needs canonical size and abelian sheafification instances. Explicit local
names let the declaration checker identify these additions without treating their
entire type as a changed declaration name. Their instance registration is local to
the file. Each reducible abbreviation is the existing canonical instance; no coefficient construction
or target statement changes.

## Old

These three named abbreviations were absent from the item module. The
published definitions used the same canonical global instances.

## New

```lean
abbrev normalizedDVREffectivityLocal1 :
    EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
attribute [local instance 4000] normalizedDVREffectivityLocal1
abbrev normalizedDVREffectivityLocal2 :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
attribute [local instance] normalizedDVREffectivityLocal2
abbrev normalizedDVREffectivityLocal3 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
attribute [local instance] normalizedDVREffectivityLocal3
```

The supporting new modules likewise name their local elaboration instances.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedDVREffectivity | T6 | Uses these canonical local instances for proof elaboration. Existing definitions and signatures stay verbatim. |

No existing module refers to these new names. Their local instance registrations
add no global typeclass search rule to downstream modules.

## Status

landed 20261020T211832-L-3509084 2026-10-20 (merge of deliver/T6/Sheaf.Paper.NormalizedDVREffectivity)
