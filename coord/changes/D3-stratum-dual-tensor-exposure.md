# AlgebraicGeometry.ProEtale.CondensedRing.stratumDualTensor

## Reason

Keep the exact termwise tensor descent behind a module abstraction boundary. This construction
contains the localization functor and its exactness instance. Importers can use the proved
`stratumDualTensor_eq` equation instead of requiring its body to be exposed. The same concrete
functor is constructed, and the equation is proved by reflexivity. No target statement changes.
Fresh profiling of the complete original proof measured roughly 20--27 seconds of kernel checking
for the tensor comparison; complete fresh runs took 40--57 seconds, with development profiling
options enabled. This delivery does not increase the compile limit or split a proof to fit it.
The original imports removed by the proof are listed in report.md.

## Old

```lean
noncomputable def stratumDualTensor
    (S : Scheme.{u}) (L : supportModules Λ S) (hL : IsFiniteLocallyProjective Λ S L) :
    DerivedCategory (supportModules Λ S) ⥤ DerivedCategory (supportModules Λ S) :=
  letI := stratumDualTensor_preservesFiniteLimits Λ S L hL
  (tensorLeft (stratumDual Λ S L)).mapDerivedCategory
```

## New

```lean
@[no_expose] noncomputable def stratumDualTensor
    (S : Scheme.{u}) (L : supportModules Λ S) (hL : IsFiniteLocallyProjective Λ S L) :
    DerivedCategory (supportModules Λ S) ⥤ DerivedCategory (supportModules Λ S) :=
  letI := stratumDualTensor_preservesFiniteLimits Λ S L hL
  (tensorLeft (stratumDual Λ S L)).mapDerivedCategory

theorem stratumDualTensor_eq
    (S : Scheme.{u}) (L : supportModules Λ S) (hL : IsFiniteLocallyProjective Λ S L) :
    stratumDualTensor Λ S L hL =
      letI := stratumDualTensor_preservesFiniteLimits Λ S L hL
      (tensorLeft (stratumDual Λ S L)).mapDerivedCategory := by
  unfold stratumDualTensor
  rfl
```

## Users

The library-wide textual search finds no mention of `stratumDualTensor` outside its own module.
The direct importers below are checked unchanged against the delivered module. The original
four removed public imports do not supply any otherwise missing declaration in either consumer;
ConstructibleExtContinuityStratum explicitly imports the cochain tensor interface itself.
There is no consumer adaptation and no consumer statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3 (not adapted) | No direct reference to the definition; unchanged compile checked. |
| Sheaf.Paper.FormalClosedSupport | Q9 (not adapted) | No direct reference to the definition; unchanged compile checked. |

## Status

landed 20261019T034252-L-415772 2026-10-19 (merge of deliver/D3/Sheaf.AlgebraicGeometry.ClosedSupportStratumHom)
