# CategoryTheory.Mod.sheaf_flatScalarTowerCoherence

## Reason

The static checker requests a change record for the new proof-only section commands.
This delivery changes no existing public signature or definition. The commands are
`variable` binders inside new sections and `[local instance]` attributes on
`comp_preservesFiniteLimits` and `comp_preservesFiniteColimits`, used only while proving
private helpers. Each section is closed before the original public theorem. Scoped
`backward.isDefEq.respectTransparency false` options apply to individual private proofs.
No new global instance, notation, option or public declaration is exported.

The proof-only import of MapDerivedCategoryMate supplies the already proved exact-derived
coherence API. The proof-only Mates and GrothendieckAbelian.Sheaf imports are removed.
No existing public import changes.

## Old

```lean
theorem sheaf_flatScalarTowerCoherence
    {S : Type uS} [Category.{vS} S] [EssentiallySmall.{w} S]
    (J : GrothendieckTopology S) :
    @FlatScalarTowerCoherence.{_, _, wA, wB, wC, wR} (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory := by
  sorry

```

## New

```lean
theorem sheaf_flatScalarTowerCoherence
    {S : Type uS} [Category.{vS} S] [EssentiallySmall.{w} S]
    (J : GrothendieckTopology S) :
    @FlatScalarTowerCoherence.{_, _, wA, wB, wC, wR} (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory := by
  let t := sfbSheafTensorStructure (A := Ab.{w}) J
  let : MonoidalCategory (Sheaf J Ab.{w}) := t.monoidal
  let : BraidedCategory (Sheaf J Ab.{w}) := t.symmetric.toBraidedCategory
  have hc : HasCoequalizers (Sheaf J Ab.{w}) := inferInstance
  have hp : ∀ X : Sheaf J Ab.{w}, PreservesColimitsOfSize.{0, 0} (tensorLeft X) ∧
      PreservesColimitsOfSize.{0, 0} (tensorRight X) := by
    intro X
    exact ⟨((sfbSheafTensor_properties (A := Ab.{w}) J).2.2 X).1,
      ((sfbSheafTensor_properties (A := Ab.{w}) J).2.2 X).2.1⟩
  refine ⟨hc, hp, ?_⟩
  intro _ _ _
  refine ⟨?_, unit_laws, tower_laws, derived_tower_laws, ?_⟩
  · intro A B C _ _ _ _ _ _ f _ g _ M
    exact ⟨comp_inv_tensor f g M, comp_hom_tensor f g M, comparison_restricts _⟩
  · exact derived_unit_laws

```

All original definitions and the theorem signature above are verbatim unchanged.
The additional declarations are private proved lemmas, with no holes. Their section
variables and local attributes cannot affect elaboration in an importing module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed in the checked queue | Its proof-only import remains valid; no signature or instance changes, so no adaptation is needed. |

This is the only direct source importer; it currently states its parent theorem with
`sorry` and does not reference a declaration from this module in its definitions or
public signatures. All downstream statements therefore keep exactly their meanings.
No consumer is edited by this delivery.

## Status

landed 20261019T034417-L-430344 2026-10-19 (merge of deliver/Z9/Sheaf.CategoryTheory.FlatScalarTowerCoherence)
