## What changed

Restored Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint at its original
Lean path from the quarantine archive named in coord/rework.tsv. Every byte of its
archived statement, proof, imports and documentation is retained. The three branches
eliminate the coefficient certificate and apply the existing continuous, integral and
algebraic-closure proper-pushforward instances. The DAG and unit route remain accurate.

The preserved earlier packet also held 98 dependency restorations. All those modules
are now present in the shared source tree; 96 were byte-identical. The current source
also contains the relocated-helper import corrections in FormalClosedSupportII and
IntegralModelsGenerators. This delivery therefore contains only the assigned restoration;
it does not overwrite newer repairs or reintroduce existing dependency holes.

Change record: coord/changes/C4-proper-adjoint-quarantine-restoration.md.

## Proved and sorry left

Zero holes before and after restoration; zero holes closed or added; zero split-off
statements. The restored declaration is
AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_isLeftAdjoint_boundedConstructibleLowerStar
(node lem-sfb-adic-bounded-constructible-proper-adjoint). Its proof is complete from the
three existing coefficient-specific instances. Existing holes in imported modules are
not added or changed by this delivery. This is a quarantine build repair, not net proof
progress or a claim that the imported geometric theory is free of sorry.

## No longer needed

No mathematical node, module or import is pruned. All three coefficient cases and both
public imports remain needed. Redundant sandbox copies of already restored dependencies
are excluded from this packet; no library file is withdrawn and there is no deleted.txt.

## Where the brief, the DAG or earlier work was wrong

This is a zero-hole quarantined restoration. The previous attempt's broad closure
restoration is superseded by the current shared sources. Its forbidden-declaration
failure matched sheaf-axiom prose in an unchanged dependency docstring. That dependency
is already present and unchanged in the library and is not part of this delivery. No
launcher script, gate or docstring was changed. tools/downstream.py reports unknown
module because the assigned module is absent from lean/; source and DAG scans retain
its existing attachment and dependencies, and find no consumer requiring adaptation.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
