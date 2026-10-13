## What changed

Proved `Algebra.PopescuLiftPresentation.zero_base_chart_relations`, preserving its
entire signature and public imports. Added the proof-only imports
`Sheaf.RingTheory.PopescuConormalTransitionCoefficients` and `Mathlib.Tactic.Ring`.

The new module `Sheaf.RingTheory.PopescuConormalTransitionCoefficients` proves
`Algebra.PopescuLiftPresentation.conormal_transition_coefficients`: a power of
`a_k` times each transition coefficient belongs to `(f_i) + (C(pi^2))`.
Its proof applies a coordinate of the supplied localized conormal basis to both
prepared relations, clears the localization denominator, and uses
`MvPolynomial.ker_map` and `Ideal.comap_map_of_surjective` to lift the membership.
The main proof evaluates this membership in the localized tensor quotient,
cancels the unit chart element, rearranges the finite sums in the chart equations,
and cancels the chart element once more. No flatness or prime argument is needed.

Updated the original node's proof, proof dependencies and proof origin to match
this Lean proof. The unit's realized statement and steps are unaffected.

Validation: both delivered modules compile together through `lcompile.py --all`
without warnings. The coefficient argument also compiles using only the ring
tactic import instead of the initially attempted linear-combination tactic
import. Removed the experimental local elaboration option. Every introduced
polynomial, quotient, evaluation map and localized module is an explicit object.
The supplied basis is used in a theorem proof; no data is chosen from a holed
existence theorem.

## Proved and sorry left

Closed the one original hole:
`Algebra.PopescuLiftPresentation.zero_base_chart_relations`
(node `lem-weil-pbc-popescu-zero-base-chart-relations`).

Also proved the new theorem
`Algebra.PopescuLiftPresentation.conormal_transition_coefficients`
(node `lem-weil-pbc-popescu-conormal-transition-coefficients`).

Holes closed: 1. Holes added: 0. No `sorry` remains in either delivered module.
This is a proof, not a decomposition into unproved statements.

## No longer needed

No original import or module was pruned. The original node no longer directly
uses `def-weil-pbc-module-localization-away`; that definition remains needed in
the new coefficient lemma. The main proof uses the ring-localization definition
`def-weil-ring-localization-away` directly. No claim is made that the
module-localization node leaves the targets' dependency closure.

The prime-local comparison and pi-divisibility modules are not imported: their
prime and partial-chart interfaces do not fit this arbitrary zero-base quotient.
They were not dependencies of the original node and are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The existing proof plan is realized in full.
The conormal coordinate calculation avoids constructing a double-sum identity in
the conormal module, while proving exactly the coefficient vanishing it requires.
Only `hd.relation` and `hd.conormal` are used; smoothness, normalization,
Noetherianity and scalar-tower compatibility are unnecessary for the auxiliary
coefficient lemma. All hypotheses of the existing item are retained.

LeanSearch returned Internal Server Error; the search log records this as
unavailable. LeanFinder found general cotangent basis results, not the explicit
coefficient comparison. Loogle identified `MvPolynomial.ker_map`, which is used.
Mathlib and both project roots were searched by name and concept. Blueprint
searches for `conormal coefficient` and `07CP` returned no matches. The ancestor
helper did not resolve this module-created node; the new node inherits the
explicit `thm-weil-pbc-finite-etale-lifting` ancestor and extends the existing
node's recorded ancestry.

The source read was the online Stacks Tag 07CP, `lemma-lifting`, specifically the
coefficient comparison and denominator clearing before the expansion modulo pi.
The source clears membership in the smaller selected-relation ideal; the present
zero-base quotient kills all `f_i`, so membership in `(f_i)+(pi^2)` suffices.
Edge cases checked: if `E_k` is empty there is no coefficient assertion to prove
and both chart sums vanish; if the second selected set is empty its sum is zero;
if `r=0` or `m=0`, the corresponding index binders have no values; in the zero
ring the localization unit and denominator-clearing lemmas remain valid. Neither
proof cancels a nonzero element or assumes a nontrivial ring.

## New nodes

`lem-weil-pbc-popescu-conormal-transition-coefficients`, in
`dag/nodes/sec-proper-base-change/`, records the proved coefficient-clearing
lemma and its module
`lean/Sheaf/RingTheory/PopescuConormalTransitionCoefficients.lean`.
It isolates only the coefficient calculation and its ideal-membership transfer;
it contains no tensor quotient, auxiliary variables, or chart-equation conclusion.
It is strictly part of the original argument and is fully proved in this delivery.
There are no statement/definition changes, forced adaptations or change records.

## Second reading by R3

1. Compared both delivered modules with the repository versions. Existing declaration
   signatures and definitions are unchanged; the added coefficient theorem is recorded
   as a new node.
2. Compiled both modules with `lcompile.py --all`; no errors, warnings, `sorry`, or
   forbidden declarations occur. The proofs use only the permitted ordinary axioms.
3. Checked the split-off theorem against the prepared conormal relations and the
   localization argument. Its statement is true, strictly simpler than the target,
   and its source, docstring, node, and declaration agree; no duplicate library result
   was found.
4. Checked the proof downward from Mathlib and existing prepared-presentation
   declarations. The target proof follows the unit route, and the report's dependency
   records identify the proof-only imports; no unused import was found.
5. Checked the DAG nodes' Lean records, proof steps, dependencies, origin, chapter,
   and unit. The realized unit statement and route remain unchanged.

Changed only the report by adding this second-reading record; no proof or statement
repair was needed.
