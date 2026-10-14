## What changed

Replaced the original proof hole by a real composition of two strictly smaller
intermediate comparisons. Added `PicardResidueSourceModelHomology` for the
geometric derived-model comparison and `PicardResidueQuotientModelHomology`
for the algebraic quotient-to-homology comparison. The two intermediate proofs
remain named `sorry` declarations with their own DAG nodes.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.picard_residue_homology_source_residue_comparison`
by composing the two intermediate additive equivalences. Added the following
strictly smaller holes:

- `picard_residue_source_model_homology` (`new-picard-residue-source-model-homology`)
- `picard_residue_quotient_model_homology` (`new-picard-residue-quotient-model-homology`)

## No longer needed

None. The original proof-only imports remain available to the intermediate
statements; no planned dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The previous canonical-kernel split was equivalent to the original theorem and
was correctly rejected. The present split separates geometric derived-model
comparison from the independent cycle-quotient algebra.

## New nodes

`new-picard-residue-source-model-homology` and
`new-picard-residue-quotient-model-homology` are added, with one named theorem
and one source-backed proof obligation each.

## Second reading by N1

1. **Repository comparison:** I diffed the delivered item against the repository
   version. The theorem signature and all existing declarations are byte-for-byte
   unchanged; only proof imports and the proof body changed.
2. **Compilation and axioms:** All three sandbox modules compile with
   `lcompile.py --all`. The item has no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`; the two intentionally split declarations retain
   their documented `sorry` holes and corresponding nodes.
3. **Split statements:** The source-model and quotient-model statements are true,
   strictly smaller comparisons with the common homology object, and are not
   duplicates of the original target or existing library declarations. Their
   docstrings, sources, and DAG records agree with their Lean signatures.
4. **Pruning and route:** The proof uses both new comparison modules, so no
   original import or proof dependency can be removed. The composition preserves
   the unit route through the source model and algebraic quotient steps.
5. **DAG agreement:** The target node's proof and `proof_deps` name exactly the
   two declarations applied in the Lean proof; each split node records its
   declaration, source, proof obligation, and `status: split`.

I changed the report only: I replaced the earlier informal paragraph with this
five-point second-reading record. No Lean statements or definitions were changed.
