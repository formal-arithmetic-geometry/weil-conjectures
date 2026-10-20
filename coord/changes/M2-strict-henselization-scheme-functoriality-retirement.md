# AlgebraicGeometry.Scheme.exists_strictHenselizationSchemeMap

## Reason

Retire the proved Sheaf duplicate as assigned in coord/retire-items.tsv.
Repair the conflict with ca565a83de reported for reviewed head 07e72618cb:
the Sheaf core-completion twin is now empty, its node is attached upstream,
and CoreData already transports the upstream presentations. Preserve those
landed changes and remove the stale parent restoration from the packet.

## Old

The withdrawn Sheaf declaration has this signature:

```lean
theorem exists_strictHenselizationSchemeMap
    {S T : Scheme.{u}} {g : T ⟶ S}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (hst : s = t ≫ g) :
    ∃ f : strictHenselizationScheme t ⟶ strictHenselizationScheme s,
      f ≫ strictHenselizationStructuralMap s =
        strictHenselizationStructuralMap t ≫ g
```

## New

The node is attached to the existing, unchanged source theorem:

```lean
theorem exists_strictHenselizationSchemeMap
    {S T : Scheme.{u}} {g : T ⟶ S}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (hst : s = t ≫ g) :
    ∃ f : strictLocalization t ⟶ strictLocalization s,
      f ≫ strictLocalizationToBase s =
        strictLocalizationToBase t ≫ g
```

The Sheaf twin is withdrawn. No adopted source declaration is edited. The
parent compatible-strict-henselization-core-completion already has its exact
upstream attachment and proof. Its upstream module imports and applies the
upstream functoriality theorem. The current CoreData calls that completion
before composing its presentations with localizationComparison; the proved
localizationComparison_base transports every structural equality. These
landed files and the parent node remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality | M2 | Withdraw duplicate; attach its mathematical node to the source theorem. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion | already withdrawn by F1 | Preserve the empty module; discard the old packet's replacement and node edit. |
| WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion | unchanged source | Sole DAG parent; already imports and uses the upstream functoriality proof. |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData | unchanged | Already uses the upstream completion and proves transport to small colimits. |

There are no current Lean importers of the withdrawn module in lean/ or
quarantine/. The reference in Paper.StrictHenselizationMapExists is a docstring,
not an import or a proof dependency. The sole DAG parent retains its dependency
on this node, with the source theorem as replacement. No node or unit step is
removed. No module held by another group is adapted.

## Status

landed 20261020T164227-L-3890832 2026-10-20 (merge of deliver/M2/Sheaf.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality)
