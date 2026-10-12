## What changed
Removed the circular `GeometricStalk` import. Added a strict-local model comparison theorem and proved the reduction theorem by composing its equivalences with `hLocal`.

## Proved and sorry left
`AlgebraicGeometry.Etale.geometricStalk_projectiveLine_of_strictLocal` is proved without the cycle. `AlgebraicGeometry.Etale.projectiveLine_strictLocal_modelComparison` remains a named `sorry`, node `lem-weil-pbc-p1-strict-local-model-comparison`.

## No longer needed
The circular import and `Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine` are no longer needed.

## Where the brief, the DAG or earlier work was wrong
The prior proof used a declaration from `GeometricStalk`, which imports this reduction module. That reuse creates an import cycle.

## New nodes
`lem-weil-pbc-p1-strict-local-model-comparison` is the strictly smaller model-and-compatibility statement used by the repaired proof.

## Earlier second reading (a previous round; superseded)
The repaired target statement is unchanged. The circular source declaration is removed; the model theorem is a strict substatement and its node records the remaining proof. Both modules compile, and the model theorem's compatibility equations are exactly the data used by the target proof.

Change record: `coord/changes/ProjectiveLineGeometricStalkReduction.md`.

## Second reading by Q1

1. Compared the delivered reduction module with the repository version. The target
   theorem signature is byte-for-byte unchanged; only its proof and a proof-only
   import were changed. The added model theorem is recorded as a new node and
   change record.
2. Compiled both delivered modules with `lcompile.py`; both compile without errors.
   The only remaining `sorry` is the named model-comparison theorem. No forbidden
   declarations or hollow definitions were added; the target proof depends on the
   existing open strict-local premise and standard axioms.
3. Checked the split statement and its node. The model comparison is a genuine
   intermediate existence-and-compatibility result, omitting the strict-local
   exchange premise and conclusion, and its source, proof sketch, dependencies,
   Lean declaration, and unit metadata agree.
4. The proof follows the shortest available route after removing the circular
   `GeometricStalk` dependency: obtain the model, apply `hLocal`, and compose
   additive equivalences. The old circular dependency and unused declaration are
   listed under `No longer needed`; no additional imports were found to prune.
5. The unit route is preserved: the reduction node uses the model-comparison node,
   then the strict-local exchange premise, and the unit's `realized` route is
   unchanged.

Changed report only: documented the second-reading checks above. No Lean proof or
statement changes were needed during this reading.
