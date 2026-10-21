# AlgebraicGeometry.RingedSpace.unboundedDirectImage_sectionPresheaf

## Reason

The first complete preflight requested this record because the static command scan
classifies the new elaborator options and local irreducibility attributes as commands
that may affect importers. These commands improve elaboration of the unchanged derived
functor constructions and keep the private proof at their established API. All attributes
are local, options concern elaboration of this file only, and all original public
signatures, definition bodies and public imports remain verbatim. No target meaning
changes or target review reopens. No source-library file is changed.

## Old

The theorem had the following unchanged signature and a `by sorry` proof:

```lean
theorem unboundedDirectImage_sectionPresheaf (f : X ⟶ Y) (q : ℤ) :
    ∃ e : inverseOpenHypercohomologyPresheaf f q ≅
        sectionDerivedDirectImage f ⋙ localHypercohomologyPresheaf Y q,
      e.hom = localHypercohomologyComparison f q ∧
        ∃ s : (sectionDerivedDirectImage f ⋙ localHypercohomologyPresheaf Y q) ⋙
            presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ≅
          sectionDerivedDirectImage f ⋙
            (DerivedCategory.homologyFunctor (ringedSiteModules.{u} (moduleRings Y)) q ⋙
              SheafOfModules.toSheaf (moduleRings Y)),
          (∀ E : DerivedCategory (ringedSiteModules.{u} (moduleRings X)),
            s.app E = localHypercohomologySheafificationAt q
              ((sectionDerivedDirectImage f).obj E)) ∧
          ∃ t : inverseOpenHypercohomologyPresheaf f q ⋙
              presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ≅
            sectionDerivedDirectImage f ⋙
              (DerivedCategory.homologyFunctor (ringedSiteModules.{u} (moduleRings Y)) q ⋙
                SheafOfModules.toSheaf (moduleRings Y)),
            t = Functor.isoWhiskerRight e
              (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ≪≫ s
```

Before the public constructions the file had only `set_option autoImplicit false`;
there were no local derived-functor irreducibility commands or private proof helpers.

## New

The theorem has exactly the same signature above and a complete proof. The public
construction block is byte-identical to the original. Before it the file now sets:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

After the last public definition, before the private helpers, the file sets:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep proof elaboration at the derived-functor API rather than its chosen construction.
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
  Functor.rightDerivedFunctorOfQuasiIsoResolutionsUnit
```

This restores the strict transparency settings for the proofs and keeps chosen derived
functors irreducible locally. It changes no exported reducibility attribute. New helpers
are private and proved; new imports are private proof imports. The proof gives the
specified Leray map and the specified sheafification components, without changing data.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf --uses
unboundedDirectImage_sectionPresheaf localAbelianSections localHypercohomologySheafificationAt`
finds seven downstream modules and only `DerivedAdjunctionTopEdge` as a downstream
textual user of these declarations. Their types and data are identical. No consumer is
edited. A temporary independent consumer checks all public declarations and the
completed theorem's axioms against the sandbox output; it is not part of the delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf | G1 | Proof filled; local elaboration commands only. |
| Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge | G2 | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBasisBbdDescent | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed | Public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TopBaseChangePresheaf | G1 | Public interface unchanged; no adaptation. |
| Sheaf.TraceFormula.DerivedBasisLocalExtSheaf | unclaimed | Public interface unchanged; no adaptation. |

The full item compiled cleanly in 36.4 seconds. The independent consumer compiled
cleanly against a freshly compiled sandbox item, checked all fourteen public declarations,
and printed only `propext`, `Classical.choice`, and `Quot.sound` as theorem axioms. There are zero remaining holes and no
new public declarations or modules. The DAG proof route and report describe the actual
Sierpiński classifier argument and the naturality of the prescribed components.

## Status

landed 20261021T130020-L-2492629 2026-10-21 (merge of deliver/G1/Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf)
