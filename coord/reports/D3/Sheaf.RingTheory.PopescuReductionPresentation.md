## What changed

Added proof-only imports of two strictly lower decomposition modules and replaced the
original `sorry` with a real composition of their conclusions. The first lower theorem
factors the reduced map through one standard smooth algebra; the second performs the
finite polynomial presentation and coefficient lifting once such a factor is supplied.
Added the corresponding `reducedAlgHom` construction and DAG nodes for both lower
statements. All three sandbox modules compile with `lcompile.py --all`.

## Proved and sorry left

Closed `Algebra.exists_popescu_reduction_presentation` by applying the two lower
statements and returning their polynomial data. The two strictly simpler helper
statements remain `sorry`: `Algebra.exists_popescu_reduction_factor` in node
`new-lem-popescu-reduction-factor`, and
`Algebra.exists_popescu_reduction_presentation_of_factor` in node
`new-lem-popescu-reduction-presentation-from-factor`.

## No longer needed

No existing imports were removed. The direct multi-page factorization and lifting steps
in the original node are delegated to the two new lower nodes; no existing module or
unit-level node is pruned.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan requires two substantial intermediate constructions, but
neither had a Lean declaration available to the target module. They are split into the
reduced factorization and the subsequent polynomial lifting theorem. The target statement
and all existing signatures are unchanged.

## New nodes

`new-lem-popescu-reduction-factor` and `new-lem-popescu-reduction-presentation-from-factor`
are added under `dag/nodes/sec-proper-base-change/`; each has its own module and named
`sorry` as required for the remaining proof work.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged and its proof compiles. The two new declarations are
strictly lower statements: one supplies only a reduced standard smooth factorization,
and the other supplies the polynomial data conditional on that factorization. Their
signatures in the DAG match the Lean declarations, each carries a blueprint tag and a
named remaining `sorry`, and the target combines them by a direct application. The
unit-level route remains represented by the target node; no existing statement or
module was changed.

## Second reading by D3

1. I compared the delivered target module with the repository version. The target theorem
   signature and all existing declarations are unchanged; only proof imports and proof
   text were added. The two helper modules and their DAG nodes are new split-off items.
   Verdict: pass.
2. I compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds.
   The target closes its original `sorry`; the two helper declarations retain named,
   documented `sorry`s and no definition contains `sorry`. Verdict: pass.
3. The helper statements are strictly smaller than the target: one constructs the reduced
   factorization, and the other constructs polynomial data from that factorization. Their
   signatures match their DAG node statements and their docstrings identify Tag 07CK.
   Verdict: pass.
4. The target proof uses both helper declarations directly. The added imports are required
   for those declarations; no existing import was removed or made public solely for proof
   use. The DAG target proof and proof dependencies match this route. Verdict: pass.
5. The unit route is preserved: the target still realizes the polynomial presentation step,
   with the factorization and lifting split into strictly lower nodes. No target statement
   or definition was changed. Verdict: pass.

I added this second-reading record only; no Lean source or DAG repair was needed.
