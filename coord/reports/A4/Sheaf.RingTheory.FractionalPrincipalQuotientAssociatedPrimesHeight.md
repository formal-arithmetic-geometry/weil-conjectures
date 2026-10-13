## What changed

Proved `Ideal.associatedPrimes_fractionalPrincipalQuotient_height` without changing
its signature. Added the proof-only import
`Sheaf.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight` and updated the
node's proof and proof dependencies to match the Lean argument.

Write y=a/b using Mathlib's fraction representation. Prove c∈J iff bc∈(a),
where J=A∩yA. Multiplication by b descends to an injective linear map A/J→A/(a).
Mathlib transfers associated primes along this injection; the existing principal
quotient theorem then gives height one. The argument handles unit numerators and
the zero quotient without a separate nonzero-quotient assumption.

## Proved and sorry left

Closed the only hole: `Ideal.associatedPrimes_fractionalPrincipalQuotient_height`
(node `lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-height`).
One hole closed, zero added, zero remaining in this delivery. No statements split off.
The existing principal quotient theorem's downstream proof dependencies remain as
before; this delivery does not claim to close their holes.

Validation: single-file compilation through lcompile.py passed without warnings.
LeanFinder, Loogle, and grep searches identified no direct theorem; Mathlib supplies
`IsFractionRing.div_surjective`, `Submodule.mapQ`, `Submodule.ker_liftQ`, and
`associatedPrimes.subset_of_injective` for the elementary reduction.

## No longer needed

None. No original imports were removed; all three public Mathlib imports support
the unchanged statement. No nodes or modules are pruned: this proof realizes the
numerator-reduction route already described in the assigned and parent docstrings.
The fractional minimal-prime sibling is not needed for this height proof and was
never imported here; it remains needed by the parent theorem.

## Where the brief, the DAG or earlier work was wrong

The assigned node's `proof_deps` was empty and its proof had only a placeholder
sentence, despite its docstring describing the principal quotient reduction.
The updated node explicitly records the existing principal quotient height node.
The unit's realized statement and proof steps are unchanged.

The cited local Stacks algebra.tex was absent on this machine. Read Tag 031T at
https://stacks.math.columbia.edu/tag/031T and followed the already recorded direct
numerator reduction rather than adding any unproved source-dependent statements.

## Second reading by A4

1. **Interface: pass.** Compared the sole delivered Lean module with the repository
   using `diff -u`. The universe declarations, namespace, docstring, theorem name,
   and complete signature are byte-for-byte unchanged. Only the proof and a plain
   proof-only import were added. There are no definitions, new declarations,
   public import changes, or change records.

2. **Proof and axioms: pass.** Independently compiled the delivered file with
   `lcompile.py` (exit 0, no warnings). Compiled a scratch copy with `#print axioms`
   for `Ideal.associatedPrimes_fractionalPrincipalQuotient_height` and
   `Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span`: both report exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Scanned the
   delivered Lean for sorry and forbidden declarations; none occur. The witnesses
   `a,b` come from Mathlib's proved fraction representation; J, I, g, and f are
   explicit constructions. No data comes from an unproved existence theorem.
   Checked both directions of hmem: multiplying d*y=c by b gives d*a=b*c;
   dividing d*a=b*c by the nonzero image of b gives d*y=c. The quotient map's
   kernel is the image of J in A/J, hence zero. Mathlib's
   `associatedPrimes.subset_of_injective` has precisely the required direction.

3. **Split statements: pass (none).** No holes or statements were split off, so
   no new nodes or duplicate statements require approval. Checked edge cases of
   the actual reduction: for A=Z and y=2/3, J=(2) and the map is multiplication
   by 3 on Z/(2); for y=1/2, J=A and the source is zero; for A a field and y
   nonzero, J=A as well. A unit numerator makes A/(a) zero, with no associated
   primes. None of these cases needs a nonzero-quotient hypothesis. Read
   [Stacks Tag 031T](https://stacks.math.columbia.edu/tag/031T), clauses (1) and
   (3): the height conclusion and normal Noetherian domain hypotheses agree.

4. **Route and pruning: pass.** Read the principal-quotient height declaration
   and the parent fractional theorem's four-step numerator-reduction docstring.
   Repeated searches with different wording through msearch.py: LeanFinder for
   associated primes of a quotient by an intersection with a cyclic submodule
   of the fraction field, Loogle for `associatedPrimes, Ideal.height`, and grep
   for comap/span and associated-prime injection results. LeanFinder returned
   minimal-prime height bounds, not a theorem that proves this association
   statement; Loogle returned no hits. Also searched the local Sheaf and upstream
   ring-theory sources. No shorter direct theorem was found. The public Mathlib
   imports provide the normality/fraction-ring, associated-prime/quotient, and
   height language in the signature; the principal height import is correctly
   proof-only. The original proof_deps list was empty, so `No longer needed:
   None` is complete. Read `dag/units/sk-thm-p1.json`, including `realized`:
   this auxiliary reduction changes no unit statement or realized step and
   keeps the parent's recorded route. No modules are pruned.

5. **DAG: pass.** Compared the delivered node JSON with the repository. Only
   proof, proof_deps, and proof_origin differ. Its three proof steps describe
   hmem, the injective quotient map, and application of the principal height
   theorem respectively. The union of their uses is exactly the sole recorded
   proof dependency, `lem-weil-pbc-normal-domain-principal-quotient-associated-height`.
   No statement, statement dependency, unit, or Lean signature metadata changed.

Second reading changed only this report: recorded the independent checks and
confirmed the full theorem's standard-axiom certificate. No Lean or DAG repair
was needed. The hole count remains one closed, zero added, with no split-off
statements.
