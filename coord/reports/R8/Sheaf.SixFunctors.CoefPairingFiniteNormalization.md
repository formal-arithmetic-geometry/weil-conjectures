## What changed

Proved the assembly of `WeilConjectures.CoefProjectionEvaluation.pairingFiniteNormalization`
from two strictly smaller statements: simultaneous finite comparison witnesses and evaluation
of the untransported projection word. The assembly expands the actual scalar-Hom transport,
uses naturality of the integral tensor-evaluation isomorphism, and composes the two finite
tensor maps. Existing statements and definition bodies are unchanged. The two new modules
are private proof imports, so the item's public import interface is unchanged.

The split preserves the original six-step argument: constructing normalized comparisons and
evaluating the geometric/scalar word remain separate from the completed final transport.
Neither intermediate asserts PairingEquation or contains ScalarSpecialization.transported.
The witness-existence theorem asserts no equality for Model.beta; the word theorem takes an
arbitrary finite comparison witness and asserts no existence theorem. In particular, its
hypothesis does not package the desired pairing equation.

## Proved and sorry left

Original hole removed by decomposition:
`WeilConjectures.CoefProjectionEvaluation.pairingFiniteNormalization`
(node `lem-coef-pairing-finite-normalization`). The assembly proof has no sorry.

Two holes added, each the entire proof of a public named theorem:

- `WeilConjectures.CoefProjectionEvaluation.finiteEvaluation_exists`
  (`lem-sf-coef-finite-evaluation-existence`): construction of simultaneous normalized
  finite comparisons, with no assertion about the pairing composite.
- `WeilConjectures.CoefProjectionEvaluation.finiteProjectionWord_evaluation`
  (`lem-sf-coef-finite-projection-word-evaluation`): equality for Model.beta before
  scalar-Hom transport, for any finite comparison witness.

This is a decomposition, not a net hole reduction: one original hole closed and two
new holes added. The item module now has zero direct holes. No sorry occurs in a definition.

Edge cases checked at the statement level: the index n=0 means coefficient exponent 1;
arbitrary unbounded K and N, including zero objects, remain allowed; neither helper adds
boundedness, finite-Tor, flatness or a K-injective-evaluation assumption. Empty schemes and
identity compactifications do not introduce extra hypotheses. The word helper has no
geometric finite-type assumptions because its comparison data already carry the required
normalized equations.

## No longer needed

Removed the item's private proof imports:
`Sheaf.Paper.SemilinearDerivedSections`,
`Sheaf.Paper.SemilinearOperationsExistence`,
`Sheaf.Paper.SemilinearSystemsExistence`, and
`Sheaf.SixFunctors.OpenTensorNormalization`.
Their mathematical work remains in the proof plans of the two new obligations; none of
these modules is claimed pruned from the targets' closure.

The item's direct proof dependencies are now just the two new nodes. The old direct proof
nodes `def-coef-semilinear-derived-calculus`, `def-exchange-projection`,
`lem-coef-semilinear-derived-sections`, `lem-coef-semilinear-operations-existence`,
`lem-coef-semilinear-system-existence`, `lem-coef-support-open-tensor-model`,
`lem-coef-system-projection-evaluation`, and `lem-sf-open-tensor-normalization` remain
needed by the lower obligations or statement data. `lem-coef-hom-tower-scalar-model`
remains a statement dependency; the assembly uses the given scalar-Hom comparison directly
and does not invoke that existence theorem. Removed the obsolete direct tool-use approval
for `lem-sf-open-tensor-normalization`; the lower witness-construction argument retains it.
No existing module is withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The shared snapshot did not contain this item's queue row. The current server queue
lists stage-3 proof work with one hole. Its historical build-error file reports a bad
import of CoefFinitePairingEvaluationData, which itself reported a bad dependency import.
The unchanged item successfully compiled against the current published dependency chain
in 10.2 seconds, so no speculative dependency repair was made.

No mathematical statement correction or unit-route change is proposed. The unit's realized
statement and step lists are empty. The original DAG plan described constructions and
normalizations but did not provide a direct ready-made Lean FiniteEvaluation witness or
an equality for the complete word; these are now explicit separately assignable obligations.

## New nodes

`lem-sf-coef-finite-evaluation-existence`, in
`lean/Sheaf/SixFunctors/CoefFiniteEvaluationExistence.lean`, isolates simultaneous
construction of comparison witnesses. Its docstring and node retain the ordinary pure-tensor,
right-derived-unit, adjunction, composition, open-map and cartesian-Hom arguments.

`lem-sf-coef-finite-projection-word-evaluation`, in
`lean/Sheaf/SixFunctors/CoefFiniteProjectionWordEvaluation.lean`, isolates evaluation of
Model.beta before the scalar-Hom isomorphism is inserted. It spells out all three finite
comparison isomorphisms in its statement. Its proof plan retains scalar balancing, signed
symmetry, sections/proper/open projection and finite closed evaluation.

Both nodes cite blueprint latest, prop-coef-integral-dualizing, proof paragraph 2,
and Stacks 07A6/0B56. LeanFinder, Loogle, LeanSearch and Mathlib grep were run; none
returned either specialized derived coefficient-system assertion. Blueprint searches for
finite evaluation and projection word found no duplicate statement. No change record is
needed: all pre-existing declarations and their public imports retain their signatures
and bodies, except the completed proof of the assigned theorem.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefFiniteEvaluationExistence": "fe8f0b48c6b2214819bfbd9ded5c0b59c344e0af", "Sheaf.SixFunctors.CoefFiniteProjectionWordEvaluation": "fe40f56e9f293ea79876b2719b4415b1bb878544", "Sheaf.SixFunctors.CoefPairingFiniteNormalization": "f08531c6ee90fff9f4da1412aa7bc8072a3a16ce"}, "results": {"Sheaf.SixFunctors.CoefPairingCompactificationModels": {"hash": "a9f46981df81aa73b2db7a211ef8cdd039659695", "status": "OK"}}, "seconds": 107, "time": "2026-10-28T14:14:01+0800", "transitive": 0, "version": 1}
```

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
