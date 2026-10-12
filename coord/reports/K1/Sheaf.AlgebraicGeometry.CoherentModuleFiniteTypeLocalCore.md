## What changed

The core theorem is proved by conjunction introduction, using two strictly simpler
intermediate locality statements. Added imports for the two helper modules.

## Proved and sorry left

Proved `AlgebraicGeometry.coherent_module_finite_type_local_core`.
The helper declarations `coherent_module_finite_type_local_restrict` and
`coherent_module_finite_type_local_cover` remain as documented `sorry`s.

## No longer needed

None; both parts of the stated proof are represented by the two helper statements.

## Where the brief, the DAG or earlier work was wrong

The original node had no usable compiled lower declarations for the two elementary
finite-type locality steps, so they were split into separate strictly simpler nodes.

## New nodes

`lem-weil-pbc-coherent-module-finite-type-local-restrict` and
`lem-weil-pbc-coherent-module-finite-type-local-cover`, with matching modules and DAG
records under `dag/nodes/sec-proper-base-change/`.

## Earlier second reading (a previous round; superseded)

Open: both helper nodes. The core conjunction proof applies each helper to exactly
the corresponding implication, preserving the target statement and the unit route.

## Second reading by K1

1. Compared the delivered core module with the repository version. The theorem
   signature and all existing declarations are byte-for-byte unchanged; only proof
   imports and the proof body changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py`. There are no forbidden
   declarations or hollow definitions. The core theorem's only extra axiom is
   `sorryAx` inherited from the two explicitly named helper theorems. Verdict: pass.
3. Checked both split-off statements against the Stacks definitions and searched
   Mathlib and the library for duplicates. Each is a true, strictly simpler
   finite-type locality statement and has its own documented `sorry` and DAG node.
   Verdict: pass.
4. The core proof is the shortest available conjunction introduction and uses both
   helper nodes; no imports or proof dependencies can be pruned, and the unit route
   remains `sk-thm-p1`. Verdict: pass.
5. The core DAG proof and dependencies match the Lean proof, and the helper node
   records match their declarations and modules. Verdict: pass.

Changed only this report: recorded the second reading and its checks.
