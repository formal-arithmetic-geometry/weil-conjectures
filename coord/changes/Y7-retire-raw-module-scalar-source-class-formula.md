# Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula

## Reason

Complete the listed retirement in coord/retire-items.tsv, under the human's
hand-off in coord/changes/retire-sheaf-twins-20261020.md. The assigned file is
now a declaration-free reexport with zero holes. Its original DIFFERENT
classification predates P2's canonical-construction migration and G2's
retirement of the former Sheaf consumer. The source-class theorem is already
proved in WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceClassFormula.

Retire only the unused Sheaf import path. Preserve the canonical theorem,
its complete source-square/naturality proof, and every mathematical DAG edge.
No upstream declaration, target statement, definition, comparison, instance,
attribute or public import is edited. No target-definition review is reopened.

## Old

The assigned module, verbatim:

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

The node lem-sbc-raw-module-scalar-source-class-formula already attaches to
AlgebraicGeometry.Etale.rawModuleScalar_source_class_formula in the canonical
WeilConjectures module. That theorem and its complete proof stay verbatim.

## New

Withdraw lean/Sheaf/AlgebraicGeometry/RawModuleScalarSourceClassFormula.lean
through deleted.txt. The delivery installs the standard empty module:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

Append a retirement note to the existing upstream Lean attachment of
lem-sbc-raw-module-scalar-source-class-formula. Keep its declaration, statement,
proof, proof_deps, stmt_deps, source, chapter and unit unchanged.

The unchanged canonical proof first uses rawModuleScalar_sheaf_composition,
upperStarComp naturality and plus_single_source_square_core. Its private
source_class_attach then applies inverse-comparison naturality to the actual
class. Thus the theorem remains available at exactly the current signature;
no coefficient square or additional hypothesis is introduced. This also keeps
zero classes, degree zero, identity arrows, zero sheaves and empty schemes.

## Users

The tools/downstream.py scan reports zero downstream modules and zero textual
users through the assigned Sheaf path. A source scan of lean/Sheaf,
lean/WeilConjectures and quarantine, including ignored Lean files, likewise
finds no import of that path. The retirement manifest's historical sole consumer,
Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula, is already an empty
withdrawn module. No adapted Lean consumer is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula | Y7 (assigned) | Withdraw declaration-free shim. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | already withdrawn | Historical consumer has no imports or declarations. |
| WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceClassFormula | unchanged | Existing theorem, signature, proof and imports retained. |
| WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unchanged | Already imports and applies the canonical theorem directly. |

The actual mathematical parent,
lem-sbc-raw-module-abelian-hom-source-formula, keeps its proof dependency on
lem-sbc-raw-module-scalar-source-class-formula and its upstream Lean attachment.
Its canonical proof applies the theorem, postcomposes the equality with the
coefficient tail using congrArg, and combines it with the composite formula.
No mathematical source-class or generic source-square result is withdrawn
by this packet: only the redundant Sheaf import path is removed. The unit sk-lem-failure-field has empty
realized.statement and realized.steps entries; its route remains unchanged.
The item's path has no quarantine/rework row and there is no open Y7 return.

Optional single-file recompilation of the unchanged source-class proof and
its unchanged parent each reached the 60-second limit. The scratch copies
are excluded from the delivery. The delivered packet changes no Lean proof
or definition and requires no adapted consumer compilation. A separate
import-only check compiled successfully in 7.3 seconds; printed axioms for
both canonical theorems are exactly propext, Classical.choice and Quot.sound.

## Status

landed 20261025T144416-L-1238417 2026-10-25 (merge of deliver/Y7/Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula)
