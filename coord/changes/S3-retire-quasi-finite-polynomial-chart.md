# AlgebraicGeometry.exists_quasiFinite_polynomial_chart

## Reason

The human-approved retirement table (`coord/retire-items.tsv`, item
`retire:Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart`) identifies this
Sheaf declaration as a duplicate interface for the proved upstream theorem
`WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart`. The upstream
module is retained. The Sheaf duplicate is withdrawn and the remaining Sheaf
importer drops its unused import of the withdrawn module.

## Old

The withdrawn declaration in
`Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart` was:

```lean
theorem exists_quasiFinite_polynomial_chart
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f] (y : X) :
    ∃ (U : X.Opens) (_ : IsAffine U.toScheme) (hy : y ∈ U) (n : ℕ)
      (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T),
      LocallyOfFinitePresentation e ∧ LocallyQuasiFinite e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f ∧
      topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞)
```

## New

The node now records the retained upstream declaration:

```lean
theorem exists_quasiFinite_polynomial_chart
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f] (y : X) :
    ∃ U : X.Opens, IsAffine U.toScheme ∧ y ∈ U ∧
      ∃ (n : ℕ) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T),
      LocallyOfFinitePresentation e ∧ LocallyQuasiFinite e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f ∧
      topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞)
```

The conjunction packaging is propositionally equivalent to the old existential
proof packaging and supplies the same witnesses and hypotheses. No source
library declaration is changed. Both conversions between the old and new
packagings have been checked by Lean in a sandbox scratch file. The retained
theorem uses only `propext`, `Classical.choice` and `Quot.sound` according to
`#print axioms`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart | S3 (assigned item) | Withdraw the duplicate module through deleted.txt. |
| Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension | unclaimed | drop the unused import of the withdrawn module |

`tools/downstream.py Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart --uses
AlgebraicGeometry.exists_quasiFinite_polynomial_chart` lists this sole downstream
module and no application of the theorem outside the retired module. The
consumer has three existing named theorem holes, all unchanged. Its statements
and proofs do not use the withdrawn import or require its upstream twin, so the
unused import is removed without replacement. This repairs point 5 of reviewer
C-c0899's return of delivery c08996ce41. No other module
imports the assigned Sheaf module. The two additional Sheaf consumers listed in
`coord/retire-items.tsv` are already absent from the live library; their upstream
counterparts import the retained upstream module and require no adaptation.
There is no transitive Sheaf consumer beyond the one listed above.

The node's Lean attachment and recorded signature now refer to the upstream
theorem. All parents retain their dependency on this node, and the unit route is
unchanged. Its dimension and chart proof-dependency nodes already attach to
upstream modules, so this retirement introduces no second copy of either
prerequisite. No target definition or statement changes.

## Status

landed 20261020T164228-L-3891038 2026-10-20 (merge of deliver/S3/Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart)
