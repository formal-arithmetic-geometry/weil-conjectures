# Sheaf.Topology.SubspaceRingRestrictionUnitCoherence

## Reason

The common coefficient-category proof makes the previously public set-composition
import unnecessary. Removing it follows stage 3's import-pruning requirement.
The other removed imports are redundant private proof imports. New imports are private.
Backward elaboration options support definitional equalities of TopCat sheaf categories;
the two unused-variable linter settings preserve original bound names in public signatures.
No public declaration signature, definition body, visibility or attribute changes.

## Old

The original import block after `module`, verbatim:

```lean
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Topology.Homeomorph.Lemmas
public import Sheaf.Topology.SetsInverseImageComposition
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.HasLimits
```

The original sections had no local backward-elaboration or linter options.
All existing public signatures and definitions are retained verbatim.

## New

```lean
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Topology.Homeomorph.Lemmas
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
```

Within `Coefficients` and the new `Homeomorphism` section:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

Before each of the two existing restriction-coherence theorem docstrings:

```lean
set_option linter.unusedVariables false in
```

The options affect elaboration and linting only. All new helpers are private and proved.
The actual inclusions, units and section maps are unchanged. The sole public import
removed supplies no declaration occurring in any existing public signature or definition.

## Users

`python3 tools/downstream.py Sheaf.Topology.SubspaceRingRestrictionUnitCoherence --uses
subspaceInclusion subspaceToOpen subspaceSectionMap subspaceOpenUnit openRestrictionGlobal
subspace_ring_restriction_unit_coherence subspace_sets_restriction_unit_coherence
subspaceHomeomorphism homeomorphismOpenSectionMap
subspace_ring_homeomorphism_unit_coherence exists_sets_inverseImage_comp` reports zero
downstream modules, only the item's own uses of its declarations, and zero uses of
`exists_sets_inverseImage_comp`. An independent `rg` import search agrees. No consumer
adaptations are required. This is import pruning, not withdrawal of the item or any node;
its parent proof dependencies and its unit route remain in place.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.SubspaceRingRestrictionUnitCoherence | D8 | All three holes proved; private helpers and proof imports added; unused imports removed; public signatures and definitions preserved. |

## Status

landed 20261023T131509-L-2114513 2026-10-23 (merge of deliver/D8/Sheaf.Topology.SubspaceRingRestrictionUnitCoherence)
