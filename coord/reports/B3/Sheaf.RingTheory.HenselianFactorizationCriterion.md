## What changed

Proved `henselianRing_iff_factorization_criterion` in
`Sheaf.RingTheory.HenselianFactorizationCriterion`, preserving its signature and public imports.
Added the proved private helper `factorization_of_lifting`, generalizing the quotient/Bezout
calculation already implemented for local rings in `HenselianLocalRootLifting`.
The forward direction applies `Algebra.existsUnique_isIdempotentElem_of_henselianRing`
to the finite algebra `AdjoinRoot f`, then
`Polynomial.exists_monic_factorization_of_idempotent`. The reverse direction proves
Mathlib's simple-root field directly by lifting the linear factor `X - C x`.
Added proof imports `HenselianIntegralIdempotentLifting`, polynomial `FieldDivision`, and
`Mathlib.Tactic.LinearCombination`. Updated the node's proof route and dependency list.

## Proved and sorry left

Proved the module's single original sorry:
`henselianRing_iff_factorization_criterion`
(node `lem-weil-pbc-henselian-factorization-criterion`).
The private helper is also completely proved. No sorry remains in this module, and no
new sorry or module was added. Imported declarations retain their existing proof dependencies.
Single-file compilation passes without warnings. The proof handles the zero ring via
`nontriviality`; for a nonzero ring the Jacobson bound proves the quotient nontrivial before
using preservation of monic degree. Degree-zero factors need no special exclusion in the
forward direction.

## No longer needed

Removed direct proof imports `Sheaf.RingTheory.EtaleSectionLiftingOfGabberRoots` and
`Sheaf.RingTheory.HenselianOfEtaleSectionLifting`. Removed their direct DAG edges
`lem-weil-pbc-gabber-root-criterion-etale-section-lifting` and
`lem-weil-pbc-etale-section-lifting-henselian-pair`: the reverse direction does not need them.
These modules/nodes remain transitively used by the existing integral-idempotent lifting
result, so this delivery does not claim they leave the target closure.
No other planned node is pruned: the monic quotient Mathlib leaf and idempotent-splitting
factorization are used. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan speaks of the idempotent definition of henselian pairs, whereas the
recorded Lean predicate is Mathlib's Jacobson-plus-simple-root class. Its Jacobson bound is
already a field. The existing integral-idempotent lifting theorem provides the bridge needed
for the forward argument. Conversely the factorization hypothesis immediately gives simple
roots by lifting a linear factor; the reverse Gabber chain is unnecessary for this predicate.
The repository's referenced Stacks TeX files are not present on this machine; the proof uses
the source arguments fully recorded in the node and existing module docstrings.

## Second reading by B3

1. Compared the delivered module with the repository using `diff`. The existing theorem's
   signature is byte-for-byte identical, as are all public imports; no definition or statement
   changed, and no change record is needed. The only added declaration is a proved private
   quotient/Bezout helper. Verdict: pass.
2. Compiled the module locally without errors or warnings. Searched its entire Lean source:
   no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. In a scratch copy,
   `#print axioms` for both the helper and the public theorem reports only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. Both imported idempotent theorems also report `sorryAx`; the
   characteristic-polynomial dependencies in particular remain open;
   no new admitted proof is introduced. Verdict: the original sorry is closed by a genuine
   reduction, with existing open dependencies, not an axiom-free closure.
3. No statements are split off and no new nodes are added. Checked the helper's CRT residues
   and the reverse direction's explicit Bezout identity. Edge cases include the zero ring,
   `I = top` (the Jacobson condition then forces the zero ring), `I = bot`, and factors of
   degree zero. The reverse proof establishes quotient nontriviality before using monic
   degree preservation. Independent searches via leanfinder, loogle, and grep for evaluation
   units and linear-factor coprimality find a field-only derivative lemma, which does not
   apply to the arbitrary quotient ring here. The existing local-ring helper has the same
   calculation with stronger local-ring hypotheses, and is private. Verdict: pass.
4. Read the proof from the public theorem downward and checked every import's role.
   `FieldDivision` provides the differentiated division identity; `LinearCombination`
   proves the two Bezout calculations. The forward direction uses the existing integral
   idempotent lifting and monic factorization lemmas; the reverse direction directly proves
   the recorded simple-root predicate. The two old direct proof-dependency edges removed
   are both listed under `No longer needed`; they remain transitively used forward.
   Read `dag/units/sk-thm-p1.json`, including `realized`: neither this node nor the removed
   direct dependencies realize a unit step. The change stays below the fixed unit route.
   Verdict: pass.
5. Compared the old and delivered node JSON: changes are confined to `proof`, `proof_deps`,
   and `proof_origin`. Checked that `proof_deps` is exactly the union of the proof steps'
   `uses`, and the Lean references realize those steps. The original statement, Lean record,
   source, chapter, and unit are unchanged. Verdict: pass.

Second-reading changes: replaced the stale public proof docstring, which still described
an unused reverse Gabber chain, with the actual idempotent/linear-factor argument; added a
source and explanation to the private helper's docstring. No proof term, signature, import,
or DAG route needed repair.
