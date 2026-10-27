# WeilConjectures.PurityFiniteSetting.finiteTensorCochainComparison

## Reason

The old abbreviation exposes the inferred type of a large total-complex natural-
transformation component. The source invertibility proof repeatedly compares this
type with the explicit tensor morphism. Give the identical map its explicit native
morphism type and retain its construction behind a definition. Its one isomorphism
proof unfolds the definition explicitly. The module and node are unclaimed.

## Old

```lean
abbrev finiteTensorCochainComparison {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :=
  (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.sheafExtendScalars φ T)).app C).app D)
```

## New

```lean
@[irreducible] def finiteTensorCochainComparison {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    ((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj (C ⊗ D) ⟶
      ((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj C ⊗
        ((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj D :=
  (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.sheafExtendScalars φ T)).app C).app D)
```

The body is verbatim identical. The displayed type is definitionally its old inferred
type. Source, target, orientation and map are unchanged, with no added hypothesis.
The scalar functor and actual adjunction retain exactly their original bodies.
The separate full signed-line normalization interface is recorded in
`J2-line-comparison-data.md`. This definition is used by targets, so its meaning
review is reopened; the formula remains the original native component.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Gives this same map its explicit morphism type. |
| Sheaf.Paper.FiniteScalarTensorData | J2, new | Stores the native map as its third source factor. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | J2, new | Unfolds the map once to establish invertibility. |
| Sheaf.Paper.FiniteScalarTensorSource | J2, new | Uses the recorded certificate through the generic source method. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed (Y7 landed 2026-10-26) | Its former use is replaced by the shorter native-model braiding proof after the normalization repair. |
| Sheaf.Paper.FiniteTensorSignedReduction | J2 | Uses the unchanged map through its typed diagram and proved source API. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | J2, new | States the same equation using diagram projections. |

The direct identifier users are the defining module, the assigned item and the
newly landed `FiniteTensorSymmetryCoherence` (Y7 delivery, unclaimed after landing).
Its proof now uses the shorter native-model braiding route. There is no
adopted source-tree edit. All other
existing public signatures and bodies stay verbatim apart from the full signed-line
interface recorded in `J2-line-comparison-data.md`; no target signature changes.

## Status

landed 20261026T070008-L-3329438 2026-10-26 (merge of deliver/J2/Sheaf.Paper.FiniteTensorSignedReduction)
