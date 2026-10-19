# Stage-1 worker report: lem-kun-cd-sep-closed-point

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-cd-sep-closed-point.json`: item, statement, split proof; no new nodes.
- `citations.json`: verbatim quotes for both proof dependencies.

## Attachments

- `AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed` belongs to `lem-kun-03qu-sep-closed` (the declaration is the closed Lean realization of that existing node, not the whole cohomological-dimension item).

## WANTED

None.

## What was checked and corrected

The imported item statement agrees with `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-kun-cd-sep-closed-point.md`, whose proof is the definition of cohomological dimension followed by the separably closed point vanishing lemma. I read `def-kun-cd.json` and `lem-kun-03qu-sep-closed.json` in full before citing them. The imported proof was too compressed about the least-value argument; I expanded it to say that the bound is a nonnegative integer, that 0 is the least possible value, and that every torsion étale sheaf is an abelian étale sheaf to which the cited vanishing applies. The hypothesis that K is separably closed is exactly the item's hypothesis and is also the hypothesis of the cited vanishing statement. No separate node is needed: the only intermediate assertion is an immediate unpacking of the definition.

## Review by NS

I checked the item source and its single proof paragraph, then matched step 1 against the exact statement of `def-kun-cd`: it supplies the least nonnegative d and the vanishing condition for every torsion étale sheaf. I matched the second part against the exact statement of `lem-kun-03qu-sep-closed`: for a separably closed K and any abelian sheaf on `Spec(K)_Et`, all positive cohomology vanishes. Thus the cited statement says the required fact, after the elementary observation that a torsion étale sheaf is an abelian étale sheaf. I verified that `Spec(K)` is quasi-compact and quasi-separated as required by the definition (it is the spectrum of a field), and that 0 is the least element of the defining nonnegative range. The citation quotes are copied verbatim into `citations.json`. I searched the whole DAG and blueprint for duplicate nodes; the existing vanishing node is cited, and no node states the target itself. Mathlib searches (LeanFinder, Loogle, grep, and the unavailable LeanSearch service) found no matching cohomological-dimension theorem. The closed declaration `AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed` was recorded as an attachment to the existing vanishing node; it does not state the target's `kuncd = 0` conclusion.

## What could not be finished

Nothing.

## Second reading by NS

- Item statement: checked against the exact blueprint lemma (order 1534), def-kun-separably-closed and def-kun-cd; PASS, with the missing def-kun-cd statement dependency added. The field hypothesis excludes the zero ring and empty spectrum; no characteristic or perfection hypothesis is imposed.
- Step 1: read both cited statements in full; def-kun-cd requires a quasi-compact quasi-separated scheme and tests all torsion abelian sheaves, while lem-kun-03qu-sep-closed gives positive-degree vanishing for all abelian sheaves over the same separably closed field. PASS after writing the one-point topology check explicitly. The bound 0 is admissible and every nonnegative bound is at least 0. For F=0 the vanishing is consistent; q=1 is covered and q=0 is intentionally unrestricted (a nonzero constant torsion sheaf has nonzero H^0).
- Step 1 source check: read Stacks 03QU, etale-cohomology.tex label lemma-compare-cohomology-point, including the hypotheses of lemma-equivalence-abelian-sheaves-point (a field and its absolute Galois group). For a separably closed field the group is trivial, so invariants are the identity exact functor and all positive derived functors vanish. PASS; the split cites the existing vanishing node rather than introducing a node for this argument. Its closed attachment was checked at FiniteSupport.lean lines 43–51: Field k, IsSepClosed k, arbitrary abelian sheaf, n+1. The recorded closed audit has no open declarations. The attachment proves the vanishing dependency; it does not define or calculate the numerical kuncd invariant.
- New nodes: none; B1–B7 and the removal/Mathlib-leaf checks are vacuous. Independent DAG keyword/tag searches found the existing lem-kun-03qu-sep-closed and lem-weil-pbc-geometric-point-cohomology (the latter assumes algebraic closure and adds H^0). The imported lem-sf-separably-closed-torsion-cd expresses the same numerical bound with another definition, so it is recorded under blueprint.same_as; the present proof retains the source's direct, closed vanishing dependency.
- Independent Mathlib searches: ran LeanFinder with a global-sections-functor phrasing, Loogle with "cohomological", and grep with cohomologicalDimension|CohomologicalDimension|IsSepClosed|isSepClosed. Read the returned types: cotangent cohomology, spectral-sequence data, and field/étale-algebra facts do not state this numerical invariant. PASS; actual search outputs are in searches.jsonl and the item's records. No Mathlib leaf is added.

Changes and reasons:

- Added def-kun-cd to stmt_deps: the statement uses its numerical invariant.
- Expanded step 1 by the one-point quasi-compact/quasi-separated argument: the definition's hypotheses are now justified explicitly; the two verbatim dependency quotations still match the repaired step.
- Recorded lem-sf-separably-closed-torsion-cd in blueprint.same_as: the first review's claim that no equivalent blueprint statement exists was too strong.
- Removed sandbox dag/units/sk-prop-sf-cbc.json: this auxiliary point lemma does not state compact-support base change and cannot realize that unit's whole statement or a fabricated proof step (the unit has no recorded steps). The unit and chapter source routes were read and left to their key nodes.
- Preserved the first worker's report and Review by NS section; no new nodes, no statement dispute, no Lean changes or builds.

Validation: deliver.py NS lem-kun-cd-sep-closed-point --no-push printed OK and preflight passed after these repairs.
