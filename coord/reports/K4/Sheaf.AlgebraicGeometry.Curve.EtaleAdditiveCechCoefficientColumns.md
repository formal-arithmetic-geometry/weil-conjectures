## What changed

Proved `AlgebraicGeometry.Scheme.Modules.additiveCechCoefficientMap_column_quasiIso`
without changing its signature or docstring. Added private proved helpers for the
coordinate sheaf isomorphism, affine derived-evaluation vanishing, preservation
of finite limits by Cech evaluation, the coefficient-section product isomorphism,
its kernel fork, and its projection formula. Added proof-only imports of
`EtaleTensorUnitSectionsNatural`, `EtaleAffineTensorCechVanishing`,
`EtaleCechVanishingCriterion`, and `EtaleAffineOpenCechResolutionColumns`.
Updated the item's DAG proof to match these constructions and applications.

The degree-zero proof establishes the kernel property of the actual augmentation,
including its prescribed coordinates. The positive-degree proof uses existing
finite affine Cech vanishing and the derived-evaluation criterion, then the already
proved affine-column homology theorem. The latter is a generic tool; using it does
not replace any step of the blueprint unit's route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.additiveCechCoefficientMap_column_quasiIso`
(node `lem-pbc-additive-cech-coefficient-columns`). All private helpers are proved.
No `sorry` remains in the delivered module, and no holes or new modules were added.
The proof uses existing project declarations and their existing downstream
proof dependencies; this is not a claim that the entire transitive axiom closure
is already sorry-free.

## No longer needed

None of the original imports or proof dependencies is removed. No modules or nodes
are pruned. The abstract degree-zero homology isomorphism supplied by the affine
column theorem is not used: degree zero is proved directly for the fixed map.
The horizontal commutation theorem is not used; its module remains required by
the original statement, coordinate map definition, and proved vertical equation.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or interface correction was needed. Initially both
published builds lacked the recently landed coefficient-map module. It became
available during this session; the main module could then be checked normally.
The natural coordinate sheaf isomorphism must be left with its inferred type:
forcing its type against a separately named lifted tensor sheaf causes excessive
definitional reduction. The final proof needs no increased heartbeat limit.
The empty family, repeated opens, and empty intersections are preserved by the
product/kernel argument and the existing affine-column theorem; no covering
hypothesis has been added.

## Second reading by K4

1. **Statements and interfaces:** Compared the delivered module with the repository
version. The theorem signature and docstring are byte-for-byte unchanged; only
proof-only imports, private helpers, and the proof body were added. Verdict: pass.
2. **Proof validity:** Compiled the module with `lcompile.py`; it succeeds with no
errors or warnings. The delivered module contains no `sorry`, `axiom`, `unsafe`,
`opaque`, `extern`, or `implemented_by`. An axiom probe reports only the allowed
axioms plus `sorryAx` inherited from open imported declarations. Verdict: pass.
3. **Split-off statements:** No new public statements or split-off holes were
added, so there are no new nodes to validate. The existing node's statement is
unchanged and remains true at the stated strength. Verdict: pass.
4. **Pruning and imports:** Checked the proof dependencies against the imports and
the DAG. The four added imports are used by the proof; no original import can be
removed without removing declarations used by the public statement or coordinate
map. The unit route is preserved through the affine column theorem and the
derived-evaluation criterion. Verdict: pass.
5. **DAG agreement:** The item's node proof and proof dependencies describe the
coordinate, kernel, vanishing, and positive-degree assembly steps actually present
in Lean. No statement or definition was changed, and no unit realization was
bypassed. Verdict: pass.

Changed during second reading: added this review record only; no Lean proof or node
content required repair.
