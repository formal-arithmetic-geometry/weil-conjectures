## What changed

Separated the declaration-only Brown entry point from the already proved criteria and
conditional compactness obstructions. BrownHypothesesDefinitions contains the existing
bundle and six canonical instance abbreviations. BrownHypothesesCriteria contains the
existing proved generation, compactness criteria, and Ext obstructions. The original
module keeps the exact arbitrary-field theorem, its named hole and its dispute notice.
Both new modules are independent of that unresolved theorem, so a valid future proof
can import the criteria without a cycle.

BrownHypothesesFiniteField and BrownHypothesesCoefficientIso are the only downstream
textual users of the moved criteria. Both were unclaimed in current server claim records.
Each gains exactly one private proof import; all its existing signatures and proofs
remain unchanged. The two Paper consumers require no source changes. Fifteen existing
node records change only the locations/declarations in their Lean attachments.

All 36 existing declaration signatures, proof/definition terms, keywords and visibility
are preserved by relocation. The only raw parser-body difference is trailing line-comment
markers after the final moved proof. Public source imports are preserved through the
new definition module. No file of WeilConjectures, target, unit statement or unit proof
route changes. The new cache abbreviations in Criteria refer to canonical tensor instances
and exist only to avoid repeating expensive typeclass search; their attributes are local.

Change record: coord/changes/E1-brown-declaration-proof-separation.md.

Final lcompile.py checks, with no profiling options, compiled the declaration module
in 7.3 s, the unchanged assertion in 4.9 s, the criteria in 53.5 s, coefficient-isomorphism
invariance in 9.1 s, and the geometric finite-field specialization in 3.7 s. All returned
exit code 0 without diagnostics. The unchanged LocalizingExceptionalAdjoint consumer
also compiled against the packet in 34.2 s; its temporary unchanged copy was removed.

An initial unchanged ExceptionalInverseImageExistence check exceeded 60 s (78.3 s).
Counterfactual profiling of the same caller against the published library without the
packet took 80.3 s; against the packet it took 79.3 s, with the same two costly refine
steps (about 22 s and 26 s) and 21.2 s of typeclass inference in both cases. This is a
pre-existing timeout, not evidence for a forced source adaptation. The caller is omitted
from the packet, and its temporary profiling copy was removed. The final delivery tool
performs its own related-module comparisons. No timeout limit was changed.

## Proved and sorry left

Closed 0 of the original 1 holes. Added 0 holes. Split off 0 unproved statements.
This is a dependency-pruning partial delivery, not a proof of arbitrary-field compactness.

The only remaining sorry in the packet is CategoryTheory.brownHypotheses,
node sk-lem-brown-hypotheses. Its signature and original proof are unchanged.
Both new modules and both adapted specialization modules contain no sorry.
Every relocated proof stays complete; no proved declaration is replaced by sorry.

## No longer needed

The original assertion and its target-facing callers no longer import the diagnostic
and criterion proofs. The following direct proof imports move out of the item and into
BrownHypothesesCriteria, which uses them with their original declarations:

- Sheaf.SixFunctors.BrownHypothesesSmall
- Sheaf.SixFunctorsBasics.BrownHypothesesStructural
- Sheaf.Paper.PadicConstantLocalModelTor
- Sheaf.Paper.StratifiedTorIntervalDevissage
- Sheaf.Paper.CohomologyTorInterval
- Sheaf.Paper.IntegralConstructibleCompactness
- Mathlib.CategoryTheory.Triangulated.Orthogonal
- WeilConjectures.CategoryTheory.CompactObjectsThick
- WeilConjectures.CategoryTheory.DerivedCategory.Products
- WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
- WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi

Current source-graph traversal of TargetsCheck finds two existing project modules absent
from its new import closure: Sheaf.SixFunctors.BrownHypothesesSmall and
Sheaf.CategoryTheory.WeakSerreBoundedThick. The new declaration module enters that closure.
This is an import-closure observation, not a claim that the corresponding mathematics or
unit step has become unnecessary. No module is withdrawn, no node or mathematical proof
dependency is deleted, and no source-library declaration is removed. The original node
still records the Noetherian compactness criterion, now in the separate criteria module.
All unit-level steps remain in the DAG and retain their existing proved implementations.

## Where the brief, the DAG or earlier work was wrong

The remaining hole is an already-disputed assertion over arbitrary positive-characteristic
fields. Finite type over an arbitrary field does not give finite ell-cohomological dimension.
The geometric finite-field compactness declarations require their finite-field datum,
and the integral theorem requires a uniform Ext bound. The current maintainer rollback
record maintenance-K4-brown-false-split-rollback.md explicitly preserves the original hole
and forbids recreating unrestricted compactness witnesses. This packet follows that record;
it neither weakens the assertion nor introduces a false lemma to prove it.

The two-day-old bad-import build record is still present on the current server. This
packet is checked against the published artifacts through lcompile.py and normal delivery
checks; it does not claim that a local single-file check clears any newer global failure.

## New nodes

def-sfb-brown-hypotheses-for attaches the existing, unchanged BrownHypothesesFor definition
to BrownHypothesesDefinitions. It is a definition-only metadata attachment for a relocation,
not an additional assertion, obligation, or proof split. Its source is the original unit's
conclusion. The existing definition is not duplicated. Existing criterion nodes now
point to BrownHypothesesCriteria, with all their statements and proof plans preserved.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 OK, 1 SLOW.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctorsBasics.BrownHypotheses": "ff773eb91bdd49b3ec06a7e1eddef058e8d71961", "Sheaf.SixFunctorsBasics.BrownHypothesesCoefficientIso": "3e88941ba8a08ff09caa78531b8976313e338427", "Sheaf.SixFunctorsBasics.BrownHypothesesCriteria": "9c0631891978bf580d1111a9f667a9bb80927e7c", "Sheaf.SixFunctorsBasics.BrownHypothesesDefinitions": "9e1c7ea6251fc868e8cfcf9b04cef0d76851e78c", "Sheaf.SixFunctorsBasics.BrownHypothesesFiniteField": "4631bb5554deea7420a4891b81aec3ba809214d0"}, "results": {"Sheaf.Paper.ExceptionalInverseImageExistence": {"hash": "e047ddc64ca96bb191cbf95acc82e09bbcecd38a", "status": "SLOW"}, "Sheaf.Paper.LocalizingExceptionalAdjoint": {"hash": "9b80929ae886e8305a73db59aae3e626c6c33cd3", "status": "OK"}}, "seconds": 190, "time": "2026-10-28T10:28:11+0800", "transitive": 0, "version": 1}
```

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
