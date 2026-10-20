## What changed

Retained the retirement packet and checked it against current sources. The sole
consumer, Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLiftData,
is restored from quarantine with exactly one import replacement: the official
WeilConjectures.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions twin
replaces the Sheaf copy. Its statement and proof remain unchanged.
The transition DAG node points at the twin; only its lean field changes.
The obsolete copy is listed in deleted.txt as explicitly required by RETIRE.
No upstream source, target statement or quarantine file is changed.

The consumer compiled through lcompile.py on this repair attempt: exit code 0,
2.8 seconds, without diagnostics. A fresh normalized comparison confirms identical
public transition theorem signatures in the quarantined root and official twin.
A search of lean/Sheaf and quarantine/Sheaf found no other consumer of the copy.

Change record:
coord/changes/retire-formal-second-ideal-algebraization-transitions-20261020.md.

## Proved and sorry left

This is retirement and quarantine repair, not a proof decomposition.
Quarantined root: 0 holes. Official twin: 0 holes. Restored consumer: 0 holes.
Holes closed: none (0 of 0). Holes added: none. Split off: none.
No sorry declarations remain in the delivered Lean module.
AlgebraicGeometry.formalSecondIdealAlgebraization_transitions is preserved upstream;
AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_lift_data keeps its proof.

## No longer needed

Remove the consumer import of
Sheaf.AlgebraicGeometry.FormalSecondIdealAlgebraizationTransitions and retire
lean/Sheaf/AlgebraicGeometry/FormalSecondIdealAlgebraizationTransitions.lean.
The official twin replaces it. The missing powerSupported_iff was private and
has no consumer use; upstream uses coherentModuleSupportedOn_pow_subschemeι_iff.
No mathematical DAG dependency or unit step is pruned: the node points at the
same public transition theorem in the official library.

## Where the brief, the DAG or earlier work was wrong

The later explicit RETIRE instruction supersedes restoring the duplicate root.
The other cluster modules require no adaptations of root declaration uses:
the consumer uses the unchanged public theorem. Their unrelated quarantine
repairs remain separate tasks, as the cluster instruction requires.

Return C-4ad16 (delivery 4ad16944be, old base e0d550965): the accepted packet
could not land because another landing changed the item after that base. This
repair uses the current quarantined source recorded in coord/rework.tsv, rather
than restoring the pre-quarantine item. The current consumer archive still differs
from the delivered consumer by exactly the transition import replacement. The
current transition node differs from the delivered node only in its lean record.
Its sole DAG parent remains the lift-data node and still uses the same transition
theorem through the upstream attachment; no parent dependency or unit route changes.
The normal delivery tool prepares the new commit on current sheaf-dag.

The previous attempt was blocked because deliver3.py required a deleted module's
original lean/ path to exist. The current tool accepts its quarantine/ path as
the baseline, so this retirement can now be delivered through the normal gate.
No launcher script was edited and no gate was bypassed. The archived root and
consumer are left untouched; the delivery restores the adapted consumer and
withdraws the duplicate root through the required deleted.txt entry.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
