# AlgebraicGeometry.Scheme.Modules.exists_picard_constant_scalar_extension_sections

## Reason

Retire the duplicate Sheaf implementation listed in coord/retire-items.tsv. The adopted
source now constructs the same linear equivalences as
`picardConstantScalarExtensionSections`, with the restriction law
`picardConstantScalarExtensionSections_map`. Use that construction directly in the sole
consumer instead of maintaining a second scalar-extension presheaf and Hom equivalence.
The construction contains actual tensor data; it chooses no arbitrary existence witness.
No adopted-source module is edited, and no target statement or definition changes.

## Old

```lean
theorem exists_picard_constant_scalar_extension_sections
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) :
    ∃ q : ∀ V : Y.Opens,
        (ModuleCat.extendScalars (scalarMap g V)).obj M ≃ₗ[Γ(Y, V)]
          ((PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
            (picardConstantVector k Y M)).obj (op V),
      ∀ {U V : Y.Opensᵒᵖ} (i : U ⟶ V) (a : Γ(Y, U.unop)) (s : M),
        ((PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
          (picardConstantVector k Y M)).map i
            (q U.unop (a ⊗ₜ[k, scalarMap g U.unop] s)) =
          q V.unop ((Y.presheaf.map i a) ⊗ₜ[k, scalarMap g V.unop] s)
```

This declaration and its private implementation leave the library with the retired
`Sheaf.AlgebraicGeometry.PicardConstantScalarExtensionSections` module.

## New

The existing adopted-source construction and its law replace the existential wrapper:

```lean
def picardConstantScalarExtensionSections
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (V : Y.Opens) :
    (ModuleCat.extendScalars (scalarMap g V)).obj M ≃ₗ[Γ(Y, V)]
      ((PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
        (picardConstantVector k Y M)).obj (op V)

theorem picardConstantScalarExtensionSections_map
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k)
    {U V : Y.Opensᵒᵖ} (i : U ⟶ V) (a : Γ(Y, U.unop)) (s : M) :
    ((PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
      (picardConstantVector k Y M)).map i
        (picardConstantScalarExtensionSections k Y g M U.unop
          (a ⊗ₜ[k, scalarMap g U.unop] s)) =
      picardConstantScalarExtensionSections k Y g M V.unop
        ((Y.presheaf.map i a) ⊗ₜ[k, scalarMap g V.unop] s)
```

Both are in `WeilConjectures.AlgebraicGeometry.PicardConstantScalarExtensionSections`.
The scalar-extension DAG node is reattached to these two declarations; its mathematical
statement, hypotheses, dependencies, and unit route are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardConstantScalarExtensionSections | Q1 | Retired; zero original holes. |
| Sheaf.AlgebraicGeometry.PicardConstantTensorBalancedSections | unclaimed | Replace the private import, bind q to the upstream construction, and use its map theorem in the restriction proof. Existing signature and public imports stay identical. |
| Sheaf.AlgebraicGeometry.ExternalConstantSectionsTensorMap | unclaimed | Indirect consumer; its public statement and balanced-sections theorem remain available with identical signatures. No source adaptation needed. |

`tools/downstream.py` lists the two downstream modules above. Its `--uses` search
finds the deleted declaration itself and the balanced-sections consumer only.
An additional search of the quarantine tree finds no import or declaration use.
The sole DAG parent is the balanced-sections node; its first proof step now records
the direct construction and restriction theorem while retaining the same dependency.
The unit record has no realized statement or step attached to this retired module.

## Status

landed 20261020T153018-L-2863582 2026-10-20 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.PicardConstantScalarExtensionSections)
