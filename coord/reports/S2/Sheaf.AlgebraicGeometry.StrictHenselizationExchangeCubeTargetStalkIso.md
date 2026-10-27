## What changed

Repaired the DIFFERENT retirement item. The current item source was already a withdrawn
stub, while its DAG node still required the original small strict-henselization model.
Kept the collision module withdrawn and restored that exact statement, apart from its
name, as AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_exchangeCube_target_stalkComparison
in Sheaf.AlgebraicGeometry.StrictLocalSmallModel.ExchangeCubeTargetStalkIso.

The proof uses the existing small-model closed-stalk theorem. It transfers invertibility
across the inverse-image/single-complex isomorphism by naturality, then expands the target
and stalk comparison into images of isomorphisms. The original node now attaches to the
restored declaration; its parent edge, mathematical statement, hypotheses, conclusion and
unit route are preserved. No adopted source file changes.

Change record: coord/changes/S2-small-model-exchange-cube-target-stalk.md.

The replacement compiled cleanly in 3.6 seconds; the combined import-order check also
compiled it in 11.3 seconds. A consumer with the exact original signature and both model
variants imported compiled cleanly in 9.1 seconds. Printed axioms of that consumer, the
restored theorem, its small-model closed-stalk dependency and the adopted twin were
exactly propext, Classical.choice and Quot.sound. The compile tool supplied the newly
landed dependency in its private overlay. The consumer is excluded from the delivered
Lean tree; its source is retained in scratchpad/SmallModelTargetConsumer.lean.txt.

## Proved and sorry left

This is a zero-hole retirement repair: the current item stub has zero holes, so zero
existing holes are closed. Zero holes are added and zero results are split off.

Proved the full original small-model target comparison as
AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_exchangeCube_target_stalkComparison
(lem-weil-pbc-strict-henselization-exchange-cube-target-stalk-iso).
No sorry remains in any delivered theorem. This restores a missing statement; it is not
a counted decrease in the sorry ledger.

## No longer needed

No mathematical node or proof dependency is pruned. The old collision path
lean/Sheaf/AlgebraicGeometry/StrictHenselizationExchangeCubeTargetStalkIso.lean
remains withdrawn through deleted.txt. Its parent continues to cite the same node id,
now with a complete proof of the original small-model statement. The downstream census
found zero current Lean importers/callers of the withdrawn module; the parent was also
checked in the DAG and remains a dependency, not a reason to erase the obligation.

No import is removed from the current stub, which has none. The new module's public
imports supply its actual statement. Its only private proof import is
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeClosedStalk. It does not import
the adopted target-stalk theorem or introduce a second proof dependency for transport
between the small and full models: that transport is already proved by the existing
closed-stalk dependency. The stated proof dependencies are all retained and used.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a sorry-bearing item and a repeatedly split obligation, but
the current item has zero holes: it is a retirement row. The old withdrawal alone left
a dangling DAG attachment. The adopted theorem is not a verbatim replacement: it uses
strictLocalization and strictLocalizationToBase, whereas the original uses
strictHenselizationScheme and strictHenselizationStructuralMap. Substituting the adopted
attachment would silently change the model in the required statement.

The existing small-model closed-stalk theorem now supplies precisely the original
first proof step, so the full argument can be completed without another split. The
formal composition/naturality argument reuses the previous T1 proof preserved in the
adopted target-stalk module, specialized back to the original small model. The attached
natural-language source calls Tag 03QO lemma-cohomology-strictly-henselian; the local
Stacks label is lemma-vanishing-etale-cohomology-strictly-henselian. The mathematical
citation is unchanged.

Degree zero, zero sheaves, empty total spaces and arbitrary separably closed point-field
extensions are included: the argument only uses the unchanged qcqs closed-stalk theorem
and functorial isomorphisms, with no torsion, properness or nonemptiness added.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
