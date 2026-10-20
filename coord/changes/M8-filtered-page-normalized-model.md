# CategoryTheory.finiteFilteredPageFunctor, finiteFilteredPageFirstIso, finiteFilteredPageImageIso

## Reason

The nested choice terms of the normalized page-functor existence theorem repeatedly expand
inside dependent page and comparison types. A first-page naturality proof exceeded the
60-second compiler limit. Repack the proved existence theorem once as a
`FiniteFilteredPageModel`, select one record, and make the three declarations its projections.
The record-valued definition is irreducible and exposes normalization laws as structure fields.
This repairs elaboration without changing any declaration signature or adding assumptions.

The selected functor and comparisons now come from one jointly chosen record. They are
normalized witnesses of the same proved construction, but are not claimed definitionally
equal to the previous nested choices. Their mathematical meaning is the same normalized
filtered-page construction. Any target statement using these definitions must receive the
usual renewed definition review. No declaration of `Challenge.lean` changes.

The original public data and definitions move to `FilteredPageLocalizationSetup`, which the
item publicly imports. The original complete `FilteredPageLocalizationData` is unchanged.
The new descent and stationary structures partition its fields. This module organization
separates data, graded comparison, descent, and stationary comparison; the bundled witness,
not file splitting, fixes the expensive unfolding.

## Old

```lean
noncomputable def finiteFilteredPageFunctor (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleComplex R ⥤
      CohomologicalSpectralSequence (ModuleCat.{u} R) 1 :=
  (boundedFilteredComplex_pageFunctor_normalized (ModuleCat.{u} R)
    (fun U p r hr ↦ finiteFilteredPageTransition R U p r hr)
    (fun U p r hr ↦ finiteFilteredPageTransition_projection R U p r hr)).choose
```

```lean
noncomputable def finiteFilteredPageFirstIso (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) :
    (((finiteFilteredPageFunctor R).obj U).page 1).X (a, b) ≅
      (U.obj.filtration.gradedPiece a).homology (a + b) :=
  (boundedFilteredComplex_pageFunctor_normalized (ModuleCat.{u} R)
    (fun U p r hr ↦ finiteFilteredPageTransition R U p r hr)
    (fun U p r hr ↦ finiteFilteredPageTransition_projection R U p r hr)).choose_spec.choose U a b
```

```lean
noncomputable def finiteFilteredPageImageIso (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t) :
    (((finiteFilteredPageFunctor R).obj U).page t ht).X (a, b) ≅
      image (HomologicalComplex.homologyMap (finiteFilteredPageTransition R U a t ht)
        (a + b)) :=
  ((boundedFilteredComplex_pageFunctor_normalized (ModuleCat.{u} R)
    (fun U p r hr ↦ finiteFilteredPageTransition R U p r hr)
    (fun U p r hr ↦
      finiteFilteredPageTransition_projection R U p r hr)).choose_spec.choose_spec).choose
    U a b t ht
```

## New

```lean
noncomputable def finiteFilteredPageFunctor (R : Type u) [CommRing R] :
    CochainComplex.FiniteFilteredModuleComplex R ⥤
      CohomologicalSpectralSequence (ModuleCat.{u} R) 1 :=
  (finiteFilteredPageModel R).S
```

```lean
noncomputable def finiteFilteredPageFirstIso (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b : ℤ) :
    (((finiteFilteredPageFunctor R).obj U).page 1).X (a, b) ≅
      (U.obj.filtration.gradedPiece a).homology (a + b) :=
  (finiteFilteredPageModel R).e₁ U a b
```

```lean
noncomputable def finiteFilteredPageImageIso (R : Type u) [CommRing R]
    (U : CochainComplex.FiniteFilteredModuleComplex R) (a b t : ℤ) (ht : 1 ≤ t) :
    (((finiteFilteredPageFunctor R).obj U).page t ht).X (a, b) ≅
      image (HomologicalComplex.homologyMap (finiteFilteredPageTransition R U a t ht)
        (a + b)) :=
  (finiteFilteredPageModel R).eI U a b t ht
```

`finiteFilteredPageModel_nonempty` unpacks the already-proved
`boundedFilteredComplex_pageFunctor_normalized` into the model record. The definition
`finiteFilteredPageModel` selects that record and is marked irreducible. It contains no
proof hole. Every clause of the normalized theorem is a field of this jointly normalized
witness: the successor normalization and successor naturality, the first-page image
equation, the map squares, the first differential as connecting map, the cycle-representative
equation, the abutment and the stabilization (reviewer fix 2026-10-21: the delivered record
had dropped successor naturality, the first-page image equation, the first differential and
the abutment, so the selected functor was less pinned than the former choice). The new large witness records suppress
generation of unused constructor injectivity lemmas; the original data structures
retain their generated API.

## Users

Read-only `tools/downstream.py` checks for each changed name reported zero downstream
modules and only the item itself as a user in the published tree. New consumers are listed
below as part of this delivery. Unfinished DAG parents retain the same item declaration;
no module or quarantine archive is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FilteredPageLocalization | M8 | Original signatures reexported; theorem assembles both proved records. |
| Sheaf.Algebra.Homology.FilteredPageLocalizationSetup | M8, new | Stores the data and jointly normalized witness. |
| Sheaf.Algebra.Homology.FilteredPageDescent | M8, new | Uses the witness fields for first-page naturality and localization descent. |
| Sheaf.Algebra.Homology.FilteredPageStationary | M8, new | Uses the representative, successor, map and stabilization fields. |

No source-library module is edited, and no adaptation of another group's module is needed.
The cochain filtration, homotopy relation, weak equivalences, ambient quotient, cohomology
image filtration and full original localization contract retain their previous meanings.

## Status

landed 20261020T221255-L-4167556 2026-10-20 (merge of deliver/M8/Sheaf.Algebra.Homology.FilteredPageLocalization)
