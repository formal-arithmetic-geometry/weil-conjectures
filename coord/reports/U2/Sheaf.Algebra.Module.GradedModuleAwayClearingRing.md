## What changed

Proved `LocalizedModule.gradedModuleAwayClearingRing` directly from Mathlib's
homogeneous fraction representation and ordinary localization equations. Constructed
the homogeneous witness explicitly and canceled only units. Added the proof-only
import `Mathlib.Tactic.Ring`; both original public imports are needed by the unchanged
signature. Updated the existing node's proof and proof_origin to the actual argument.
No signatures, definitions, visibility, or unit realizations changed.

## Proved and sorry left

Closed the original hole `LocalizedModule.gradedModuleAwayClearingRing` (node
`lem-weil-pbc-graded-module-away-clearing-ring`): 1 of 1 original holes proved.
Added no holes; none remain in the delivered module. Removed the proposed sandbox
hole `LocalizedModule.gradedModuleAwayClearingRingCore` and its undelivered module
and node. This delivery is a proof, not a decomposition: net one original hole closed.

## No longer needed

No repository imports or old proof-dependency nodes are pruned. The four original
definition dependencies remain necessary to interpret the unchanged signature.
Removed the first worker's proposed import
`Sheaf.Algebra.Module.GradedModuleAwayClearingRingCore`, its module, and new node
`lem-weil-pbc-graded-module-away-clearing-ring-core` before delivery; these never
entered the repository and do not count as library pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's core statement was equivalent to the original conclusion via
value-map injectivity and restriction compatibility, with the same hypotheses.
Calling it strictly weaker was incorrect, and it supplied no genuine reduction.
Mathlib already supplies everything needed for the direct fraction calculation.
The original docstring's nilpotent case is incorporated in Away.mk_surjective.

## Second reading by U2

1. Compared the delivered module with the read-only repository using diff, and
checked the original theorem signature byte for byte through `:=`. Verdict: identical;
only proof, proof-only import, and proof documentation changed. There are no new
public declarations or definitions and no change records are needed.
2. Compiled the final file with lcompile.py, with no errors or warnings. Checked that
there is no sorry or forbidden declaration form. The scratch-copy #print axioms
check reports only propext, Classical.choice, and Quot.sound. Verdict: complete proof.
3. Read the proposed core statement and rejected it as an equivalent restatement;
removed its theorem, module, and node. No split-off statements remain. Searched with
loogle for Away.mk_surjective, leanfinder for degree-zero localization denominator
clearing, and grep for fraction equations and away-map formulas, and read the
upstream homogeneous-localization API. Verdict: the Mathlib representation and
mk'_spec API give the real argument, without new lemmas. Checked n=0, deg(f)=1,
zero numerators, nilpotent g, the zero ring, and zero divisors: the constructor is
valid in each case and cancellation is exclusively by units.
4. Read from the conclusion downward and replaced the restatement by the explicit
witness B/f^(n*deg(g)), with B=g^(n*(deg(f)-1))*b. The two public imports supply
signature types; the sole added import supplies ring and is proof-only. No old
proof-dependency import can be removed. Checked sk-thm-reduction.json: this node
is below its realized unit statements and steps, which are preserved. Verdict:
short direct route, no unit bypass, no library modules pruned.
5. Read the original and proposed nodes against the Lean proof. Removed the invalid
new node; the existing node now records the actual fraction calculation and its
source. Its original definition dependencies remain, and no new node is needed.
Verdict: DAG agrees with Lean; statement and Lean signature records unchanged.

Second reading changed: replaced the equivalent core sorry by a complete direct
proof, deleted its undelivered module and node, narrowed the proof import to
Mathlib.Tactic.Ring, and corrected the proof documentation, node, and report.
