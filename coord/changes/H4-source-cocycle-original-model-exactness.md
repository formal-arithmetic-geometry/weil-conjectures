# sourceCocycleExactRestriction

## Reason

Restore the quarantined item with its original strictHenselizationScheme and
strictHenselizationStructuralMap statement. The upstream sync changed the existing
strictHenselization_globalSections_preservesFiniteColimits theorem to concern
Scheme.strictLocalization s. The archived item still uses the spectrum of the
pointed-affine-neighbourhood colimit. Compiling that archive reproduces the recorded
G.PreservesHomology failure at line 92, followed by missing finite-colimit preservation.
These two Lean models are not definitionally equal.

## Old

The archive has the following sole public import:

```lean
public import WeilConjectures.AlgebraicGeometry.SourceLocalizedCocycleHomology
```

Its statement and proof use this scheme and sections functor:

```lean
let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
  AddCommGrpCat.{v + 1}
letI := strictHenselization_globalSections_preservesFiniteColimits s
```

The last theorem now supplies an instance for a different functor:

```lean
PreservesFiniteColimits
  (Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology AddCommGrpCat.{v + 1})
```

No exactness instance for the displayed original G was available in this import environment.

## New

Retain the entire archived item, including all signatures, definitions, proof bodies,
existing imports, and its DAG Lean attachment. Add this public import, since the
instance is needed when elaborating the public theorem statement:

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact
```

That new module proves and registers the following instance:

```lean
instance strictHenselizationScheme_globalSections_preservesFiniteColimits
    {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1})
```

Its proof obtains the local and strictly henselian structures on this actual colimit
from the adopted source theorem strictHenselizationLocalStructure, transfers terminal
section preservation of epimorphisms through ΓNatIsoSheafSections, and applies the
Mathlib exact-functor API. The local-structure and generic terminal-sections modules
are private proof imports. This is a proof about the original object, not a replacement
of its definition or a hypothesis on the cocycle theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction | H4 | Restored unchanged except for the public instance import; all its declarations compile. |
| Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact | H4, new | Provides the fully proved original-model exactness instance. |
| Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm | unclaimed in the shared claim records; quarantined | Sole archived direct importer; its source remains untouched. Its existing old-model restriction declarations disagree with canonical-model source declarations independently of this repair. |

The read-only tools/downstream.py check with --allow-missing --uses
sourceCocycleExactRestriction reports zero live downstream modules and zero live
users. Scanning both lean/ and quarantine/ finds the sole direct archived importer
listed above and 74 transitive downstream modules. No consumer interface changes:
the original theorem text is byte-identical to its archive. No target statement or
existing definition changes, so no target meaning review is reopened.

A scratch compile of the archived direct importer reaches pre-existing type mismatches
at its lines 57 and 95: strictHenselizationSectionRestriction now lands in sections on
strictLocalization, while its statement and definition expect strictHenselizationScheme.
The archive remains a separate rework item; this delivery does not adapt it. No module
held by another group is changed. An import smoke check synthesizes exactness for the
original scheme through the repaired module's public interface.

## Status

landed 20261020T150644-L-2553664 2026-10-20 (merge of deliver/H4/Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction)
