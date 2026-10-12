## What changed
Proved `AlgebraicGeometry.Scheme.etaleResidueTriples_colimit_simple_roots` by applying the finite-stage construction theorem and projecting its stage element into the colimit. Added the intermediate construction theorem as a named sorry for parallel proof.

## Proved and sorry left
The target theorem is proved. `AlgebraicGeometry.Scheme.etaleResidueTriples_simple_root_stage` remains sorry; it records the finite etale stage construction from Stacks Tags 04GN and 04GP.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The imported DAG proof had no usable lower-level declarations; the finite-stage construction was split into a dedicated intermediate node.

## New nodes
`lem-weil-pbc-etale-triples-colimit-simple-roots-construction`.

## Earlier second reading (a previous round; superseded)
The target proof is unchanged and applies the finite-stage theorem directly. The intermediate
statement has the exact Lean signature and records the Stacks finite-etale construction; its
proof remains a named sorry for follow-up work.

## Second reading by E2

1. **Statements and accidental changes.** Compared both delivered modules with the repository
   versions. The existing target declaration is byte-for-byte unchanged; only its proof and one
   proof-only import changed. The construction theorem is a new, stronger finite-stage
   existential statement and does not alter any existing declaration.
2. **Proof checks.** Compiled all sandbox modules with `lcompile.py --all`; both compile without
   errors or warnings. The target proof directly applies the construction theorem and projects
   through the cocone injection. The sole remaining `sorry` is the named construction theorem,
   with its source, proof sketch, and DAG node recorded; no definition contains `sorry` and no
   forbidden declarations occur.
3. **Split statement review.** The construction statement is true by the finite etale
   construction in Stacks Tags 04GN and 04GP and is strictly stronger than the target because it
   supplies a stage and stage element. Searches of the library and Mathlib found no existing
   declaration duplicating it. Its docstring gives the mathematical route and its node records
   the source and proof dependency data.
4. **Pruning and imports.** The target retains the required public imports and uses the new
   construction module through a plain proof-only import. No old proof dependency or import is
   unused, so there is nothing to prune.
5. **DAG and unit route.** Both node records match the Lean declarations, proof steps, and
   `proof_deps`. The construction node is assigned to unit `sk-thm-p1`, and the target proof
   follows that unit route by applying the finite-stage step and then the colimit injection.

Changed only the required report section; no mathematical or statement changes were needed.
