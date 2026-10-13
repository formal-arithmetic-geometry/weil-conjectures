## What changed

Proved `AlgebraicGeometry.noetherian_perfect_compact` by the existing
`AlgebraicGeometry.perfectObjectCompact` theorem, with a proof-only import of
`Sheaf.AlgebraicGeometry.PerfectObjectCompact`.
The second reader also proved `AlgebraicGeometry.noetherian_perfect_representatives`
by `AlgebraicGeometry.Scheme.exists_perfectComplex_representatives`, with a
proof-only import of `Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives`.
All existing signatures, docstrings, definitions, visibility and other proofs are unchanged.
Updated both specialization nodes and synchronized the top representative node's
proof metadata with its already existing four-helper reduction.

## Proved and sorry left

Closed two of the four direct holes in the repository version:
- `AlgebraicGeometry.noetherian_perfect_compact`
  (`lem-sc-derived-qcoh-perfect-compact-noetherian`).
- `AlgebraicGeometry.noetherian_perfect_representatives`
  (`lem-sc-derived-qcoh-perfect-representatives-noetherian`).

Two direct holes remain:
- `AlgebraicGeometry.noetherian_open_derived_categories_exists`
  (`lem-sc-derived-qcoh-compact-open-categories`).
- `AlgebraicGeometry.compact_isPerfect_of_isNoetherian`
  (`lem-sc-derived-qcoh-compact-is-perfect`).

No holes added and no new split-off statements. The existing
`AlgebraicGeometry.derivedQCoh_compact_representatives` already had a reduction proof
in the repository; it is unchanged and is not counted as a newly closed hole.
All five declarations retain `sorryAx` transitively (or directly for the two
remaining holes), besides `propext`, `Classical.choice`, and `Quot.sound`.
These are local proof closures, not a claim that the target import closure is complete;
the ledger determines net progress including the added proof imports.

## No longer needed

No imports or modules pruned. All original imports occur in the public signatures.
The compact-specialization and perfect-representative-specialization nodes had empty
old `proof_deps`, so neither loses an old dependency.
The top representative node no longer directly uses its old proof dependencies
`lem-pc-derived-category-locally-small`, `lem-pc-perfect-complexes-compact-set`,
`lem-pc-perfect-object-compact`, and `prop-pur-kinjective-resolutions-exist`.
Its actual direct dependencies are now the four existing Noetherian helper nodes
and `lem-pc-derived-qcoh-direct-sums`. The two generic perfect results remain used
through the specialization nodes; this metadata correction claims no module pruning.

## Where the brief, the DAG or earlier work was wrong

The compact-specialization plan omitted the available generic `perfectObjectCompact`.
The second reader found the analogous generic theorem
`Scheme.exists_perfectComplex_representatives`, so the perfect-representative hole
was also immediately closable.
The first report incorrectly called `derivedQCoh_compact_representatives` a remaining
sorry, although its proof is already present in the repository version.
Its DAG still described the earlier unsplit route; the second reader synchronized
`proof`, `proof_deps`, and `proof_origin` with its existing Lean reduction.

## Second reading by Q4

1. PASS. Compared the complete module with the read-only repository by `diff`.
   The only Lean edits are two plain proof imports and replacement of two whole
   `sorry` proofs. Every existing signature, binder (including universe `w` and
   all open-derived-category hypotheses), docstring and visibility is byte-identical.
   No definition or target statement changes; no change record required.
2. PASS. Local compilation through `lcompile.py` succeeds. The only direct sorries
   are the two named existing theorems listed above. No axiom, unsafe, opaque,
   implemented_by, extern, hollow definition or new data construction is present.
   A scratch copy with `#print axioms` for all five declarations reports only the
   standard three axioms and `sorryAx` from open statements below.
   The existing local choice of derived models lives inside an existence theorem,
   not inside a public definition.
3. PASS for this delivery: no new split-offs or statements. Read both generic
   theorems and matched their hypotheses and all conclusion clauses. Noetherianity
   supplies precisely CompactSpace and QuasiSeparatedSpace. Both proofs keep the
   specified coproduct instance, indexing universe `u`, and Hom universe `w`.
   Empty schemes, zero objects, and empty coproduct families are not excluded.
   The remaining inherited holes concern open models at the prescribed Hom universe
   and the affine-local compact-to-perfect implication; neither is a restatement of
   the full representative theorem. Repository searches found the generic perfect
   representative theorem, which is now used; Mathlib grep and a LeanFinder search
   for specified-universe open derived models found no immediate closing lemma.
   `HasDerivedCategory.standard` alone does not establish the arbitrary `w` clause.
4. PASS. Each new proof is the direct specialization of an existing result;
   the top proof remains its existing combination of smaller results. Original
   imports are needed by statements, and both added imports are plain proof imports.
   Read `dag/units/sk-thm-picard-duality.json`: its statement and sole step are
   unchanged; its realized statement/step lists are empty, and no realized unit
   node is bypassed. No module pruning is claimed.
5. PASS after repair. The compact-specialization node records the generic compact
   theorem; the perfect-representative node now records the generic representative
   theorem. The top node now records its actual four-helper reduction and coproduct
   instance. Proof dependencies equal the union of uses in their proof steps.
   Existing node statements and all non-owned fields remain unchanged; no new nodes.

Second-reading changes: closed `noetherian_perfect_representatives`; added its
proof-only import; repaired its node and the top node's proof metadata; corrected
hole accounting and dependency-pruning claims in this report. The first worker's
compactness proof is retained unchanged.
