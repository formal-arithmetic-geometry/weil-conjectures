# Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix

## Reason

Complete the retirement in coord/queue.tsv and coord/retire-items.tsv under the
human's hand-off in coord/changes/retire-sheaf-twins-20261020.md. The current item
is a declaration-free reexport with zero holes. Its definition node already names
AlgebraicGeometry.Etale.rawModuleScalarSourcePrefix in the canonical upstream module.
Retire the shim and migrate its sole remaining importer to that same upstream module.

The stale DIFFERENT classification predates P2's canonical-construction migration
and K4's source-factor retirement. No definition changes in this delivery. The
upstream definition remains the explicit abelian source factor followed by derived
abelian pullback of the scalar source factor and forgotten class, for the same ring,
schemes, sheaf, degree, test object, Over-arrow and raw class. All edge cases, including
q = 0, identity arrows, zero classes and empty schemes, retain the identical term.

## Old

Assigned item, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso

/-! The existing canonical source construction and its historical scalar API.
(blueprint: def-sbc-raw-module-scalar-source-prefix). -/

@[expose] public section
```

The sole live importer, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceClassFormula
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso

/-! The existing canonical source construction and its historical scalar API.
(blueprint: lem-sbc-raw-module-scalar-source-class-formula). -/

@[expose] public section
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/RawModuleScalarSourcePrefix.lean through
deleted.txt; landing installs the standard empty module. The consumer becomes:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceClassFormula
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix
public import Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso

/-! The existing canonical source construction and its historical scalar API.
(blueprint: lem-sbc-raw-module-scalar-source-class-formula). -/

@[expose] public section
```

The consumer keeps its explicit public import of
Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso, so the shim's historical
forgetting aliases, instances and inverse comparison remain visible. Every previous
public declaration remains visible through the same defining module; only the
retired intermediate module leaves the import closure. Add a retirement note to the
definition node's existing upstream Lean attachment, keeping every other field.

## Users

The tools/downstream.py scan reports one downstream module and no textual users of
the declaration within that Sheaf consumer. A complete scan of lean/ and the preserved
quarantine/ sources finds exactly the same single importer of the retired path.
Neither the item nor its consumer has a quarantine/rework row. The consumer is
unclaimed at preparation; H9 holds the assigned retirement item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix | H9 | Retire declaration-free shim. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unclaimed | Replace the prefix public import by its canonical twin; keep all other imports. |
| WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix | unchanged | Canonical definition retained verbatim. |
| WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unchanged | Existing proof and direct canonical prefix import retained verbatim. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unchanged | Existing direct canonical prefix import, statement and proof retained verbatim. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unchanged | Existing direct canonical prefix import, statement and proof retained verbatim. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMapNaturality | unchanged | Existing use of the canonical prefix and complete proof retained verbatim. |

All four mathematical parents of def-sbc-raw-module-scalar-source-prefix retain their
references: lem-sbc-raw-module-scalar-source-class-formula,
lem-sbc-raw-module-abelian-hom-source-formula,
lem-sbc-raw-module-abelian-hom-target-formula and
lem-sbc-raw-module-abelian-hom-map-naturality. Their Lean attachments already use
canonical upstream modules; no mathematical node is withdrawn. The unit
sk-lem-failure-field has empty realized.statement and realized.steps entries; neither
its statement nor its proof route changes. No adopted source module, target statement,
construction, instance or theorem proof is changed, and no target definition review
is reopened by a definition change.

The adapted consumer compiles cleanly via lcompile.py --all: exit code 0, no
diagnostics, reported Lean time 8.8 seconds. Comparing both full and public-only
import closures removes exactly the declaration-free shim and adds no module.

## Status

landed 20261025T123111-L-1832605 2026-10-25 (merge of deliver/H9/Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix)
