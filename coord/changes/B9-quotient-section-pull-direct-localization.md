# AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_pull_normalized_localization_transport_iso

## Reason

The transport lemma has exactly one caller, `section_pull_normalized_localization_descent`.
That caller already selects a flat-term K-flat resolution with an actual cochain
quasi-isomorphism `q : P' ⟶ P`. Applying naturality directly to this augmentation proves
the desired equation and makes the separate transport statement unnecessary.

The old helper's plan applied naturality along an arbitrary isomorphism of derived
objects. The displayed target instead uses ordinary scalar extension on complexes,
which is not assumed to preserve quasi-isomorphisms. There is no need to assert that
stronger transport statement: retain the actual cochain map supplied by the resolution.
Both displayed composites are natural transformations on cochain complexes. Their
source factors through the derived localization, so its image of `q` is invertible.
Naturality, the flat-term hypothesis and cancellation of this source map give the
conclusion. Neither the ordinary target map nor any scalar counit is cancelled.

The parent theorem's entire public statement is unchanged. This is a complete
replacement argument, with no new helper or remaining sorry, rather than a weaker
version of the retired theorem. Its unit's resolution/localization route is preserved.
The proof handles identity maps, zero complexes, unbounded complexes, empty schemes
and zero coefficient rings uniformly, without additional assumptions.

## Old

The withdrawn module declares:

```lean
theorem section_pull_normalized_localization_transport_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T)
    (e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E)
    (P Q : CochainComplex (modules Λ Y) ℤ)
    (i : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q)
    (h :
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)) :
      barLam.hom.app (DerivedCategory.Q.obj Q) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app Q) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj Q) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app Q) =
        (derivedPullback Λ' f).map (cY.model.ε.app Q) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj Q) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app Q)
```

Its parent used it on `asIso (DerivedCategory.Q.map q)` after choosing the resolution.

## New

The helper module is withdrawn through `deleted.txt` and its node's `lean` attachment
is explicitly `null`. No declaration replaces it. The parent drops the private import
of this module and proves the same existing statement directly:

```lean
classical
  let source := (DerivedCategory.Q ⋙ cY.model.T) ⋙ derivedPullback Λ' f
  let target := (pullback Λ f ⋙ cX.model.E).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q
  let α : source ⟶ target :=
    Functor.whiskerLeft DerivedCategory.Q barLam.hom ≫
      Functor.whiskerRight (pullback Λ f).mapDerivedCategoryFactors.hom cX.model.T ≫
      Functor.whiskerLeft ((pullback Λ f).mapHomologicalComplex (.up ℤ)) cX.model.ε ≫
      Functor.whiskerRight (Functor.mapHomologicalComplexCompIso
        (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom DerivedCategory.Q
  let β : source ⟶ target :=
    Functor.whiskerRight cY.model.ε (derivedPullback Λ' f) ≫
      Functor.whiskerLeft (cY.model.E.mapHomologicalComplex (.up ℤ))
        (pullback Λ' f).mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom
        DerivedCategory.Q
  intro P
  let := SheafOfModules.monoidalCategory (ring Λ Y)
  let := SheafOfModules.symmetricCategory (ring Λ Y)
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients
    (R := ring Λ Y)).some
  let := SheafOfModules.hasFunctorialFlatResolution_kfi (ring Λ Y)
  let : IsGrothendieckAbelian.{u + 1} (modules Λ Y) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (Scheme.ProEt.topology Y) _
  obtain ⟨P', q, hq, hflat', hP'⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
  have h' : α.app P' = β.app P' := hflat P' hP' hflat'
  change α.app P = β.app P
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  have : IsIso (source.map q) := by
    dsimp only [source, Functor.comp_map]
    infer_instance
  apply (cancel_epi (source.map q)).mp
  rw [α.naturality, β.naturality, h']
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientSectionPullTransportLocalizationIso | B9 | Withdraw the unused module and its single holed theorem. |
| Sheaf.Paper.QuotientSectionPullTransportLocalization | unclaimed (current server claim records, 2026-10-28) | Replace the use of the retired theorem by the complete direct naturality proof; drop only its private import; preserve all existing signatures. |

`tools/downstream.py --direct --uses section_pull_normalized_localization_transport_iso`
identifies exactly this caller. The DAG has exactly one parent of the retired node,
`lem-sfb-quotient-section-pull-transport-extension-localization`; it is updated to use
the existing closed resolution node `lem-sfb-abstract-kflat-resolution`. No other node
or unit realization cites the retired node. The module's sole importer is updated in
the same delivery. This is the actual replacement required for withdrawal by step 8d.

The parent's direct importer, `Sheaf.Paper.QuotientSectionPullTransportExtension`, is
compiled unchanged against the replacement proof and is not delivered. No source-library
declaration, target statement or definition changes.

## Status

landed 20261028T055619-L-777194 2026-10-28 (merge of deliver/B9/Sheaf.Paper.QuotientSectionPullTransportLocalizationIso)
