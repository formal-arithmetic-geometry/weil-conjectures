## What changed

Filled the two proof holes in `lean/Sheaf/Paper/IntegralResiduePullFlatModel.lean`:
`restrict_pull_fac` is proved by transporting the exact derived square through
`exactLeftSquareFac`, and `residueExchangePull_flatModel` is proved using the flat
pullback criterion, derived adjunction unit factorizations, and `mateModel`.
The original imports and public signatures are unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtale.CondensedRing.restrict_pull_fac` (private helper)
and `AlgebraicGeometry.ProEtale.CondensedRing.residueExchangePull_flatModel` (the
item theorem). No `sorry` remains and no new holes were added.

## No longer needed

None. Every existing import is used by the completed proof, and no DAG node or
module is pruned.

## Where the brief, the DAG or earlier work was wrong

Nothing identified. The DAG proof plan matches the completed derived-unit,
exact-square, and mate calculation.

## Second reading by C4

1. **Signatures and accidental changes.** Compared the delivered module with the
   repository version. Existing declaration signatures, definitions, visibility,
   and imports are unchanged; only the two proof bodies were filled.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; the file has no
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The item
   theorem uses only the permitted foundational axioms (apart from any open
   declarations elsewhere in its imports).
3. **Statements and duplicate search.** The private helper calculations are
   intermediate categorical reductions, not restatements of the item. Searches
   with `msearch.py` found only generic mate and derived-category ingredients;
   no existing specialized theorem duplicates either declaration.
4. **Route and pruning.** The proof follows the DAG route through pullback
   flatness, the ordinary scalar-unit compatibility, and the exact derived
   square. Every original import is used, so no import, node, or module is
   pruned.
5. **DAG agreement.** The item's statement and proof dependencies agree with
   the Lean proof, and the unit `sk-thm-properbasechange` remains realized by
   the existing nodes. No node files needed changes.

Changed only this report by recording the second reading; no Lean or DAG repair
was necessary.
