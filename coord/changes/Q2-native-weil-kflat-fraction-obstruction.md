# native_weil_tensor_ringed_kflat_resolution_obstruction

## Reason

The assigned statement is false for every nonempty scheme: its strict right fraction
cancellation axiom would make all native complexes acyclic. Add a proved refutation and
mark the original declaration `STATEMENT-DISPUTED`, retaining its signature and existing
hole as the worker contract requires for disputed statements. No theorem is weakened.

The new generic helper proves the cone obstruction for any abelian category. Its proof
uses the existing source-library cone criterion without changing any source-library file.
The native specialization uses the already proved nonzero ordinary constant sheaf.

## Old

No obstruction declaration existed. The existing
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_resolution`
signature and its `sorry` proof are preserved verbatim.

## New

The added declaration is under `omit [Fact (ringChar k₀ ≠ l)] in`:

```lean
theorem native_weil_tensor_ringed_kflat_resolution_obstruction [Nonempty X] :
    ¬ (let W₀ := HomologicalComplex.quasiIso
        (ProEtaleWeilSheaf k₀ l X) (.up ℤ)
      W₀.HasRightCalculusOfFractions ∧
        let P : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
          NativeTensorKFlat k₀ l X T
        ∀ L : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
          ∃ (P' : P.FullSubcategory) (s : P.ι.obj P' ⟶ L), W₀ s)
```

The helper module adds
`CochainComplex.acyclic_of_quasiIso_hasRightCalculusOfFractions`, with a complete proof.
Three redundant private imports are replaced by the helper, single-homology computation,
and native constant-sheaf module. Public imports and all preexisting declarations stay
identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeWeilTensorRingedKFlatResolution | Q2 | Dispute marker and proved refutation; existing signature unchanged. |
| Sheaf.Paper.NativeWeilTensorRingedKFlatLocalizationEquivalence | unclaimed | Sole direct importer; unchanged; original theorem remains available with its exact type. |
| Sheaf.Algebra.Homology.QuasiIsoFractionObstruction | new in Q2 | New proved helper, privately imported by the item. |

`tools/downstream.py --direct --uses native_weil_tensor_ringed_kflat_resolution_obstruction`
reports this sole direct importer and zero existing users of the added declaration. No
existing module other than the item is modified. No target definition or signature changes.

## Status

landed 20261028T034916-L-3568131 2026-10-28 (merge of deliver/Q2/Sheaf.Paper.NativeWeilTensorRingedKFlatResolution)
