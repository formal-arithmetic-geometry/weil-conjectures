# AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.gluing

## Reason

Package the full sectionwise gluing theorem's witnesses once with a fixed forward functor and their triangle identity. The new public `FixedEquivalence`, its projections, `FixedEquivalence.ofExists`, and `recordedEquivalence` retain the gluing functor and the specified unit and counit from the complete section-and-morphism formula theorem. This uses the already proved gluing theorem; it does not choose an unspecified object from an unproved existence assertion. The source formulas determine the gluing equivalence up to the natural isomorphisms used downstream.

The old nested choices repeatedly exposed the large theorem statement during elaboration and were not a suitable API for the full proof. `moduleUnit` and `moduleCounit` now write their forward functor as the definitionally equal tuple of `restriction` functors. Their mathematical types and all theorem statements are unchanged. The forward tuple is fixed in the type of the packaged data, avoiding expansion of the selected inverse to identify it.

Construct `insertion` directly as coordinate zero insertion followed by this same gluing functor. The added public `CoordinateSums.coordinateTransport` and `CoordinateSums.coordinateInsertion` are ordinary constructions with no postponed data. The counit proves the diagonal identity and off-diagonal zero formulas, so this is the same zero insertion up to the natural isomorphism used by the localization statement. Its exactness and additivity are proved again for this construction. No target statement changes, and `LocalizationStatement` is byte-for-byte unchanged.

## Old

```lean
def gluing : Components.{t, u, v, w} X I Y j R ⥤ Modules.{t, u, v, w} R :=
  Classical.choose (clopen_ringed_module_gluing.{t, u, v, w,
    max v w (t + 1), max v w (t + 1), 0, 0} X I Y j hd hc R hcomm)

def moduleUnit : 𝟭 _ ≅ clopenRestriction.{t, u, max v w (t + 1), w} j R ⋙
    gluing.{t, u, v, w} X I Y j hd hc R hcomm :=
  Classical.choose (Classical.choose_spec
    (clopen_ringed_module_gluing.{t, u, v, w,
      max v w (t + 1), max v w (t + 1), 0, 0} X I Y j hd hc R hcomm))

def moduleCounit : gluing.{t, u, v, w} X I Y j hd hc R hcomm ⋙
    clopenRestriction.{t, u, max v w (t + 1), w} j R ≅ 𝟭 _ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (clopen_ringed_module_gluing.{t, u, v, w,
      max v w (t + 1), max v w (t + 1), 0, 0} X I Y j hd hc R hcomm)))

def insertion : ∀ i, Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R) ⥤
    Modules.{t, u, v, w} R :=
  Classical.choose
    ((Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (clopen_ringed_module_gluing.{t, u, v, w,
        max v w (t + 1), max v w (t + 1), 0, 0} X I Y j hd hc R hcomm)))).the project server.the project server.2.2.1)
```

## New

```lean
def gluing : Components.{t, u, v, w} X I Y j R ⥤ Modules.{t, u, v, w} R :=
  (recordedEquivalence.{t, u, v, w} X I Y j hd hc R hcomm).inverse

def moduleUnit : 𝟭 _ ≅ (Functor.pi' (fun i ↦ restriction.{t, u, v, w} (j i) R)) ⋙
    gluing.{t, u, v, w} X I Y j hd hc R hcomm :=
  (recordedEquivalence.{t, u, v, w} X I Y j hd hc R hcomm).unitIso

def moduleCounit : gluing.{t, u, v, w} X I Y j hd hc R hcomm ⋙
    Functor.pi' (fun i ↦ restriction.{t, u, v, w} (j i) R) ≅ 𝟭 _ :=
  (recordedEquivalence.{t, u, v, w} X I Y j hd hc R hcomm).counitIso

def insertion (i : I) : Modules.{t, u, v, w} ((clopenRingRestriction (j i)).obj R) ⥤
    Modules.{t, u, v, w} R :=
  CoordinateSums.coordinateInsertion
    (fun k ↦ Modules.{t, u, v, w} ((clopenRingRestriction (j k)).obj R)) i ⋙
      gluing.{t, u, v, w} X I Y j hd hc R hcomm

```

The supporting public declarations are attached to the existing localization node; all their proofs and all private helper proofs are complete. `recordedEquivalence` and the selected data retain their irreducible API.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization | Q8 | Proofs use the packaged normalization and explicit insertion. |
| Sheaf.AlgebraicGeometry.ProEtaleClopenDerivedScalarCompositor | P8 | Existing consumer checked unchanged against the repaired definitions. |
| Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent | P9 | Existing consumer checked unchanged against the repaired definitions. |
| Sheaf.Paper.ClopenCompletedOperationTowers | Q5 | Existing consumer checked unchanged against the repaired definitions. |
| Sheaf.SixFunctors.ClopenCompositeCounitNormalization | unclaimed | Existing consumer checked unchanged against the repaired definitions. |

## Status

landed 20261024T190732-L-43719 2026-10-24 (merge of deliver/Q8/Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization)
