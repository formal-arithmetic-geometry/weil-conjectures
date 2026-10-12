## What changed

Proved `Algebra.popescu_lifting_witness` directly from the existing
`Algebra.popescu_lifting` declaration (07CP), applied with `π ^ 4`. A private,
proved cancellation lemma derives the required annihilator equalities for powers
four and eight. The proof constructs the quotient map from `A`, obtains
`algebraMap R D π ∈ singularIdeal R D` from the smoothness-away clause, and
applies the generic diagram comparison in
`Sheaf.RingTheory.PopescuLiftingWitnessControl` for the final ideal inclusion.
The original theorem signature and docstring are unchanged.

The proof-only import of `Sheaf.RingTheory.PopescuLiftingWitnessControl` is added.
That module proves the generic singular-ideal comparison used by the final step.
Both modules compile with `lcompile.py --all`; neither contains a `sorry`.

## Proved and sorry left

Closed the original hole `Algebra.popescu_lifting_witness` (node
`new-popescu-lifting-witness`), one of one. Added no holes. The control theorem
`Algebra.popescu_lifting_witness_control` and the private annihilator helper are
fully proved. Existing `sorryAx` in imported Popescu-lifting declarations remains
outside this delivery's declarations.

## No longer needed

The old proof dependency `lem-weil-pbc-zero-locus-eq-iff-radical-eq` is unused;
the proof uses `Ideal.radical_eq_sInf` and `singularIdeal_zeroLocus` directly.
It is removed from `new-popescu-lifting-witness.proof_deps`. No other imports or
existing modules were removed. The earlier proposed arbitrary-lift core statement
and its module/node are omitted because the final proof constructs the lift directly
from 07CP. No unit-level proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

An earlier proposed control statement claimed that compatibility modulo `π ^ 4`
and membership of `π` in the singular ideal of `D` alone imply the final
singular-ideal inclusion. This is false: for a field `k`, take `R = A = C = Λ = k`,
`π = 0`, and `D = k[ε]/(ε²)` with the augmentation. The source singular ideal is
zero while the target field's singular ideal is the unit ideal. The valid control
statement retains the smoothness-transfer hypothesis supplied by 07CP(c), and is
recorded below.

## New nodes

`new-popescu-lifting-witness-control` records the generic, fully proved comparison
used by the final inclusion. Its Lean statement specifies all rings, ideals, maps,
commuting equations, radical containment, and smoothness-transfer hypotheses. Its
source is Stacks Project Lemmas 07F0 and 07CP; the node records LeanSearch,
LeanFinder/Loogle, and Mathlib grep searches.

## Second reading by G2

1. Compared the delivered `Sheaf.RingTheory.PopescuLiftingWitness` module with the repository version. The theorem signature and docstring are byte-for-byte unchanged; only the proof and its proof-only import were changed. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The proof uses only existing lifting and singular-ideal declarations plus the fully proved control theorem. Verdict: pass.

3. Checked the split-off control statement against its commuting-diagram hypotheses and tested the quotient and prime-ideal argument in the compiled proof. It is strictly more general than the item and retains the smoothness-transfer hypothesis needed for truth; no duplicate declaration was found in the library. Verdict: pass.

4. The proof follows the unit route through `Algebra.popescu_lifting`, constructs the quotient lift directly, and removes the unused zero-locus dependency listed in the old node. Imports are minimal: the control module is proof-only. Verdict: pass.

5. Updated `new-popescu-lifting-witness` proof steps and dependencies to match the proof, and added `new-popescu-lifting-witness-control` with its Lean statement, source, proof, and searches. The unit `sk-thm-p1` remains realized by the item and control node. Verdict: pass.

Changed: added this second-reading record; no mathematical or interface changes were needed.
