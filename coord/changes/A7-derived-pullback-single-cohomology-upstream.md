# AlgebraicGeometry.Scheme.Modules.nonempty_homology_derivedPullback_iso_of_locally_single

## Reason

The 2026-10-20 upstream sync quarantined the Sheaf module because importing the old
Sheaf derived-pullback construction together with the adopted source construction
produced a duplicate declaration. The adopted source now contains the entire
single-cohomology theorem and its completed proof. Preserve one declaration per notion:
restore the assigned path as a public compatibility import of that source module and
attach the existing DAG node to the source declaration. This is a repair with zero
initial holes, not a new proof or a statement weakening.

## Old

Quarantined module's public imports:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
```

Its public theorem signature (verbatim):

```lean
theorem nonempty_homology_derivedPullback_iso_of_locally_single
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {T T' : Scheme.{u}} (g : T' ⟶ T) (E : schemeDerivedCategory T) (i : ℕ)
    (hneg : ∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E))
    (hloc : ∀ t ∈ Set.range g.base, ∃ U : T.Opens, t ∈ U ∧ ∃ r : ℕ,
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (Modules.restrictFunctor U.ι).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E)) i r) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) i).obj
        ((derivedPullback g).obj E) ≅ (Modules.pullback g).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj E))
```

## New

The restored module exports the adopted source theorem through:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackSingleCohomology
```

The source declaration has the same full name and signature, with the derived functor
explicitly qualified to retain its original meaning:

```lean
theorem nonempty_homology_derivedPullback_iso_of_locally_single
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {T T' : Scheme.{u}} (g : T' ⟶ T) (E : schemeDerivedCategory T) (i : ℕ)
    (hneg : ∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E))
    (hloc : ∀ t ∈ Set.range g.base, ∃ U : T.Opens, t ∈ U ∧ ∃ r : ℕ,
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (Modules.restrictFunctor U.ι).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E)) i r) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) i).obj
        ((AlgebraicGeometry.derivedPullback g).obj E) ≅ (Modules.pullback g).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj E))
```

The source module, its proof, its public imports and all its declarations are unchanged.
The node's mathematical statement, proof and dependency edges are unchanged. Its `lean`
record now names the source module and records the explicit qualification above.
No target meaning changes.

## Users

`tools/downstream.py` with `--allow-missing --uses` reports zero downstream modules and
zero declaration uses for the absent Sheaf module. Searching both `lean/` and
`quarantine/` also finds no importer of the old Sheaf path. The same search on the
source declaration identifies the existing source theorem and its PerfectLocusOfRank
consumer. The source module's aggregate root import is also listed below. None is
edited. The only DAG parent is `lem-pc-flat-rf-open`; its dependency still resolves to
the same theorem through the updated attachment, so no parent edge is removed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology | A7 | Restored as a compatibility import; duplicate body removed. |
| WeilConjectures.AlgebraicGeometry.DerivedPullbackSingleCohomology | unclaimed | Existing replacement theorem and full proof retained verbatim. |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank | unclaimed | Already imports source replacement; compiled unchanged. |
| WeilConjectures | unclaimed | Already publicly imports the source replacement; unchanged. |

All other transitive users of the source module retain exactly the same source
interface because that module is unchanged.

## Status

landed 20261020T211621-L-3479230 2026-10-20 (merge of deliver/A7/Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology)
