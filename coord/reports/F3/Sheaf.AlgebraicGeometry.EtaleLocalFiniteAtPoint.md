## What changed

Proved `AlgebraicGeometry.exists_etale_finite_open_of_isolated_fiber_point` in
`Sheaf.AlgebraicGeometry.EtaleLocalFiniteAtPoint`, with its signature unchanged.
The affine construction follows Stacks [02LK](https://stacks.math.columbia.edu/tag/02LK)
and the proved algebra lemma [00UJ](https://stacks.math.columbia.edu/tag/00UJ).
The implementation reuses Mathlib's affine construction from
`exists_etale_isCompl_of_quasiFiniteAt`, stopping before its separatedness-dependent
complementary-open argument. It proves uniqueness using 00UJ's uniqueness of primes,
and proves both required residue-field isomorphisms.

Added three proved private helpers: `spec_residueFieldMap_conjugate`,
`isIso_spec_residueFieldMap`, and `isIso_pullback_fst_residueFieldMap`.
The first two translate the algebraic residue-field map into the scheme map using
the existing Spec.residueFieldMap_residueFieldIso_hom. The third proves the base-change residue-field assertion using
`Scheme.Pullback.exists_residueField_equiv_ofPointTensor`, whose current implementation
is proved. Proof-only imports added:
`Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` and
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`.
The latter supplies the existing affine residue-field naturality lemma.
Second reading removed the redundant `Mathlib.RingTheory.Etale.QuasiFinite` import;
its algebra lemma is already available through the retained imports.

Updated the item's DAG proof and proof dependencies to reflect the implemented tensor
argument. The unit `sk-thm-p1` and all its realized statements and steps are preserved.

Validation: the final module compiles without warnings. An explicit `#print axioms`
for the public theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
No new public interface, definition, axiom, or statement change.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_etale_finite_open_of_isolated_fiber_point`
(node `lem-weil-pbc-etale-local-finite-at-point-elementary`).
No `sorry` remains in the item. No holes added or split off.
The three private helpers are fully proved. This is a proof, not a decomposition;
the public theorem's axiom check has no `sorryAx`.

## No longer needed

Removed `lem-weil-pbc-fibre-product-points` from this node's direct proof dependencies.
Its point-classification theorem `Scheme.Pullback.carrierEquiv` is unnecessary:
the point is constructed from 00UJ's prime, and its residue field is recovered from
its canonical tensor map. No existing module import was removed; the existing
`Sheaf.AlgebraicGeometry.FibreProductPointResidueField` remains necessary.
The temporary broad proof import `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`
was replaced by the specific scheme quasi-finite input listed above.
Second reading also removed the redundant proof-only import
`Mathlib.RingTheory.Etale.QuasiFinite`; compilation without it succeeds. No other planned
node or module is declared unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's final step used fibre-product point
classification unnecessarily; its residue-field conclusion follows directly from
the canonical tensor map and the residue-field theorem. Mathlib's weaker scheme
existence theorem cannot be applied as stated, because it assumes separatedness
and does not assert the elementary residue field or uniqueness clauses. Its affine
construction nevertheless applies without separatedness; that assumption is only
needed for the subsequent complementary-open construction, which this item does
not require.

The local clone lacks `literature/stacks-project/more-morphisms.tex`; the source
statements and affine-reduction proof were checked at the official Stacks pages
02LK and 00UJ linked above. No unproved sourced statement was added.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The public theorem signature is unchanged; only its proof, proof-only imports, and private helpers differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and the public theorem uses only the permitted axioms. Verdict: pass.
3. Checked the three private helpers and the updated DAG proof. They are proved, mathematically true, and strictly auxiliary; no statement was split off and no new node was added. Verdict: pass.
4. Checked the downward route and pruning. The proof uses the affine etale construction and the tensor residue-field argument; the unused fibre-product point-classification dependency was removed from the node. The unit `sk-thm-p1` and its realized route remain intact. Verdict: pass.
5. Checked that the DAG proof, proof dependencies, and proof origin agree with the Lean proof, and that the report records the removed dependency and imports. Verdict: pass.

Changed only the proof implementation, added the two proof-only Mathlib imports and three private helpers, updated the node's proof metadata, and recorded the second reading here. No public statement or definition changed.


## Second reading by F3

1. **Interfaces: pass.** Compared the delivered module with the read-only repository
   version by diff and checked the existing public theorem signature byte for byte.
   It is unchanged. The only new declarations are three private proved helpers;
   all added imports are proof-only. No public definition or statement changed and
   no change record is needed.
2. **Proof and axioms: pass.** Independently compiled the module with `lcompile.py`,
   without errors or warnings. A scratch copy checks the public theorem and all
   three helpers with `#print axioms`; only `propext`, `Classical.choice`, and
   `Quot.sound` occur. There is no `sorry`, forbidden declaration, or hollow
   definition. The existential algebra witnesses come from the proved Mathlib
   00UJ theorem, not from an unproved existence assertion.
3. **Split statements: pass (none).** No new public statement, node, or hole is
   introduced. Read each private helper: conjugation by affine residue-field
   identifications preserves bijectivity; base change along an isomorphism of
   residue fields makes the tensor inclusion an isomorphism, so the canonical
   tensor map has zero kernel and the proved residue-field theorem supplies
   surjectivity. This holds for arbitrary field extensions and does not require
   separatedness, reducedness, or a rational original point. Empty schemes have
   no input point. Checked the sources at [02LK](https://stacks.math.columbia.edu/tag/02LK)
   and [00UJ](https://stacks.math.columbia.edu/tag/00UJ).
4. **Route and pruning: pass after import cleanup.** Searched Mathlib and both
   Lean roots for scheme residue-field isomorphisms and the quasi-finite étale
   construction, and read `exists_etale_isCompl_of_quasiFiniteAt`. It requires
   separatedness and lacks the elementary and uniqueness clauses, so it cannot
   directly close this statement. The affine portion reused here requires no
   separatedness. The only removed old proof dependency is
   `lem-weil-pbc-fibre-product-points`, correctly recorded above; the proof retains
   the residue-field theorem. Read `dag/units/sk-thm-p1.json`: this node is not a
   realized unit statement or step, and the unit's route and records are unchanged.
   Tested removal of both new Mathlib imports in scratch copies: removing the
   scheme quasi-finite import fails, while removing the ring quasi-finite import
   succeeds. Removed the latter from the delivery.
5. **Nodes: pass.** Only `proof`, `proof_deps`, and `proof_origin` differ in the
   existing node. The dependency list equals the union of the steps' `uses`.
   The added residue-field naturality dependency names the existing upstream
   declaration actually used, and the final step describes the canonical tensor
   argument actually implemented. No new nodes need validation.

Second reading changed only the redundant proof-only ring quasi-finite import and
this report (including the missing PropertyC import attribution). The proof itself
was retained. Closed one original hole; added zero holes; split off zero statements.
