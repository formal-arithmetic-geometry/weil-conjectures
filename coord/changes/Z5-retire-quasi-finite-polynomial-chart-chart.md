# AlgebraicGeometry.exists_quasiFinite_polynomial_chart_data

## Reason

The human-approved retirement item in `coord/retire-items.tsv` identifies
`Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart` as a duplicate of
`WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart`.
The upstream theorem is already proved. Keeping both modules introduces two
public declarations with the same name. Retire the Sheaf declaration, use the
upstream twin, and redirect the node's Lean attachment.

## Old

From `Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart`:

```lean
theorem exists_quasiFinite_polynomial_chart_data
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f] (y : X) (n : ℕ)
    (hdim : topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞)) :
    ∃ (U : X.Opens) (_ : IsAffine U.toScheme) (hy : y ∈ U)
      (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T),
      LocallyOfFinitePresentation e ∧ LocallyQuasiFinite e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f
```

The sole consumer privately imports that Sheaf module.

## New

Use the existing declaration in
`WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart`:

```lean
theorem exists_quasiFinite_polynomial_chart_data
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f] (y : X) (n : ℕ)
    (hdim : topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞)) :
    ∃ U : X.Opens, IsAffine U.toScheme ∧ y ∈ U ∧
      ∃ e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T,
      LocallyOfFinitePresentation e ∧ LocallyQuasiFinite e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f
```

The upstream signature, attributes, public imports and complete proof are preserved
verbatim. Its existential conclusion packages affineness and point membership as
conjunctions. The previous conclusion instead existentially quantifies proofs of
those same propositions. Both give precisely the same open, affineness proof,
membership proof, morphism, two morphism properties and composite identity.
Unpacking either form gives the identical inputs to the consumer's existing proof.
The old Sheaf module is withdrawn through `deleted.txt`, and no consumer imports it.
The delivery tool represents this withdrawal by an empty module pending pruning.
No target signature or definition changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart | Z5 | Retire the duplicate declaration and its proof imports. |
| Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart | unclaimed | Replace the private chart import with the upstream twin. All declarations, signatures and proof lines stay verbatim; the same `obtain` pattern unpacks the upstream conclusion. |
| Sheaf.AlgebraicGeometry.CohenMacaulayFieldExtension | unclaimed | Sole further transitive importer. It uses the unchanged parent interface; no source change. |

A whole-library reference search finds no other import of the retired module and
no other textual user of `exists_quasiFinite_polynomial_chart_data` in its
consumer closure. The distinct upstream declaration and its upstream parent
remain untouched. All transitive consumers retain the parent's exact signature.
The node `lem-sbc-quasi-finite-polynomial-chart-chart` now records the existing
upstream declaration and its verbatim signature. The same three proof dependencies
and proof steps remain valid for that upstream proof; no unit step is bypassed.

## Status

landed 20261020T141321-L-2036964 2026-10-20 (merge of deliver/Z5/Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart)
