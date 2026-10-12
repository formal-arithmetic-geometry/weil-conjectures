## What changed

Proved `Subalgebra.exists_jacobson_pow_mul_mem_base` in
`Sheaf.RingTheory.FiniteIntegralConductor`, with its signature and visibility unchanged.
Added proof-only imports `Mathlib.RingTheory.FractionalIdeal.Operations` and
`Mathlib.RingTheory.Finiteness.Ideal`. All original public imports remain.
Updated the theorem's proof explanation and the existing node's proof, proof_deps, and
proof_origin to match the compiled argument.

The shorter route clears denominators in the finite submodule A, obtains a nonzero d,
and places a positive power of the Jacobson radical in (d). The final calculation is
b=r*d and d*a=image(c), so b*a=image(r*c). No quotient module is constructed.
The unit record realizes only thm-sc-proper-cohomology, not this intermediate node;
its statement and route are preserved.

## Proved and sorry left

Closed the sole original hole: `Subalgebra.exists_jacobson_pow_mul_mem_base`
(node `lem-sc-finite-integral-conductor`). Added zero holes and split off zero statements.
No sorry remains in the delivered Lean module. The proof uses only proved Mathlib results.
The prescribed local wrapper compiled the module cleanly.

The n=0 outcome of the ideal-power lemma is handled by taking n+1 and using decreasing
ideal powers. If A=B or d is a unit, the same calculation works. No semilocal or
fraction-field hypothesis was removed, although neither the finiteness of MaximalSpectrum B
nor IsFractionRing A K is needed by this shorter proof.

## No longer needed

The proof no longer needs `lem-weil-pbc-finite-module-support-annihilator`, whose Mathlib
realization is `Module.mem_support_iff_of_finite` / `Module.support_eq_zeroLocus` in
`Mathlib.RingTheory.Support`. No `Mathlib.RingTheory.Support` import is added.
The quotient A/B, its annihilator and localized support are unnecessary.
No original import was removed: the original module did not import its planned proof dependencies.
The radical-intersection node `lem-weil-pbc-zero-locus-eq-iff-radical-eq` and the
ideal-power node `lem-weil-pbc-fg-ideal-radical-power` remain used via their Mathlib matches.
No project Sheaf or WeilConjectures module is needed as a proof import.
This is pruning of this node's dependency; no claim is made that other targets do not use it.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or old proof plan. The plan was longer
than necessary, because finite generation already provides a common denominator.
The brief's expectation of an extended argument was unnecessary for this particular module.
The cited local Stacks TeX file is absent on this machine; the cited finite-conductor
paragraph was read at https://stacks.math.columbia.edu/tag/09N2 instead.

## Second reading by U2

1. Compared the delivered Lean module with the repository version. The theorem signature and
all existing declarations are unchanged; only proof text and proof-only imports were added.
Verdict: pass.
2. Compiled the module with the prescribed `lcompile.py` command and checked the theorem's
axioms. It compiles cleanly, has no forbidden declarations or remaining `sorry`, and its axioms
are only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the proof route and node against Mathlib and the repository. The denominator
construction, radical containment, finite-generation power lemma, and final multiplication
calculation are valid; no statement was split off. Verdict: pass.
4. Checked pruning and imports. The two added imports are proof-only and necessary for the
compiled route; the old support-annihilator route is no longer used. The unit record's realized
route is untouched. Verdict: pass.
5. Checked the DAG node's statement, proof, dependencies, and origin against the Lean proof.
The node records the common-denominator route and retains the two Mathlib-matched dependencies;
the statement remains unchanged. Verdict: pass.

Changed after reading: no code or DAG repair was needed; this second-reading record was added.
