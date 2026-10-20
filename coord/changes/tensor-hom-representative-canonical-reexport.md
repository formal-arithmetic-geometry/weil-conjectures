# AlgebraicGeometry.tensorHomUncurry_representative_coherence

## Reason

Restore the quarantined assigned module after upstream sync 5f7b33eac. Its archived
signature refers to `P.IsAcyclicTensorKFlat`, which its current public imports do not expose.
The adopted source now provides the same named theorem with the canonical
`CochainComplex.IsKFlatTensor` predicate. The old predicate in
`Sheaf.Algebra.Homology.KFlat` and the canonical predicate in
`WeilConjectures.Algebra.Homology.KFlat` have identical definition bodies: total tensor
with every acyclic complex is acyclic. The upstream theorem also has the same proof.
Restore the Sheaf module as a public re-export, avoiding duplicate declarations of the
same fully qualified name. This is an interface restoration, not a deletion or withdrawal.
The node retains its Sheaf module/file attachment and both proof dependencies.

## Old

```lean
theorem tensorHomUncurry_representative_coherence (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M P' L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hP' : P'.IsAcyclicTensorKFlat)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (φ' : P' ⟶ homComplex (R := X.sheaf) L'
      ((schemeHomKInjectiveResolution X).obj M'))
    (hK : DerivedCategory.Q.obj P = DerivedCategory.Q.obj P')
    (hL : DerivedCategory.Q.obj L = DerivedCategory.Q.obj L')
    (hM : DerivedCategory.Q.obj M = DerivedCategory.Q.obj M')
    (hφ : HEq (DerivedCategory.Q.map φ ≫
        (schemeDerivedInternalHomResolutionIso X L M).inv)
      (DerivedCategory.Q.map φ' ≫
        (schemeDerivedInternalHomResolutionIso X L' M').inv)) :
    HEq (pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M)
      (pullbackTensorModelMap X P' L' ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M' φ') ≫
          schemeHomResolutionInverse X M')
```

## New

The declaration is publicly re-exported from
`WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence`:

```lean
theorem tensorHomUncurry_representative_coherence (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L M P' L' M' : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hP' : P'.IsKFlatTensor)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (φ' : P' ⟶ homComplex (R := X.sheaf) L'
      ((schemeHomKInjectiveResolution X).obj M'))
    (hK : DerivedCategory.Q.obj P = DerivedCategory.Q.obj P')
    (hL : DerivedCategory.Q.obj L = DerivedCategory.Q.obj L')
    (hM : DerivedCategory.Q.obj M = DerivedCategory.Q.obj M')
    (hφ : HEq (DerivedCategory.Q.map φ ≫
        (schemeDerivedInternalHomResolutionIso X L M).inv)
      (DerivedCategory.Q.map φ' ≫
        (schemeDerivedInternalHomResolutionIso X L' M').inv)) :
    HEq (pullbackTensorModelMap X P L ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P L M φ) ≫
          schemeHomResolutionInverse X M)
      (pullbackTensorModelMap X P' L' ≫
        DerivedCategory.Q.map (schemeTensorHomUncurry X P' L' M' φ') ≫
          schemeHomResolutionInverse X M')
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence | N4 | Restored module re-exports the canonical declaration and records its signature. |
| Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative | unclaimed in repository; quarantined | Archived direct importer. Mathematical premise and conclusion identical. Its own obsolete K-flat predicate references already fail independently of this repair; it remains quarantined for its own assignment. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative | unclaimed in repository | Uses the canonical upstream theorem and predicate already; unchanged. |

No live Lean module imports the quarantined item. Source searches include quarantine:
the archived descent representative above is the only direct importer and caller.
The parent DAG node `lem-pc-tensor-hom-uncurry-descent-representative` keeps its dependency
and needs the identical mathematical coherence assertion. No unit route is bypassed.
No target signature or definition is changed. No source-library file is edited.

## Status

landed 20261020T151227-L-2649904 2026-10-20 (merge of deliver/N4/Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence)
