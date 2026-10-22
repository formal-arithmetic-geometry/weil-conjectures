## What changed

Restored Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization from the quarantine
path in coord/rework.tsv. Replaced the retired public StrictHenselizationRestriction
import by StrictLocalSectionCone and migrated strictLocalSpecialization's first
factor to (strictLocalSectionCone s).existsUnique_restriction. Added the explicit
public UpperLowerStarCoherence import required by the public derived-image statement.
All other factors, declaration signatures, docstrings and theorem proofs are unchanged.

The archive fails compilation on hidden strict-local and derived-category names and
on the removed existsUnique_strictHenselizationStalkRestriction identifier. The repaired
module compiles cleanly through lcompile.py in 4.3 seconds. The complete existing proof
uses the same local-constancy datum, prime annihilator, residue-characteristic argument,
smooth local acyclicity, locally constant torsion local acyclicity and proper
specialization theorem. Its final exact hsp checks equality with the specified map.

Change record: coord/changes/A4-restore-smooth-proper-prime-specialization.md.

## Proved and sorry left

This is a zero-hole restoration and definition/interface repair. The archive has zero
sorries; the restored module has zero sorries. Holes closed: none. Holes added: none.
Split off: none. The existing complete proof of
AlgebraicGeometry.Etale.isIso_strictLocalSpecialization_smooth_proper_prime is preserved.
No hollow definition or arbitrary existential witness is introduced: the restriction
is uniquely determined by all its pointed-neighbourhood germ components.

## No longer needed

Removed the obsolete import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction,
which was already withdrawn; its replacement supplies the same canonical restriction
from the generic section-cone API. No further module or DAG dependency is pruned.
All three mathematical proof dependencies are still used. The existing DAG statement,
Lean attachment, proof and unit route remain unchanged; no new node is needed.
The archived ModuleSpecializationAbelianIso and ProperSmoothCurvesPrimeCoefficients
parents are retained and remain mathematically dependent on this item.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned restoration repair with zero holes, rather than a new proof.
The archived module predates the generic section-cone migration. The landed A3 change
record describes this exact migration, but it is absent from the archive. The archive
also relied on private imports for public derived-image names. Both defects are now
repaired; no mathematical statement is disputed.

Read Stacks etale-cohomology.tex, lemma-sp-isom-proper-loc-cst-torsion (0GKD), and the
three named dependency signatures. They match the unchanged proof route. The
sk-thm-properbasechange unit route is untouched. Mathlib leanfinder and loogle searches
return no direct theorem about this specified etale specialization; the existing
library proof already implements the source's three-lemma argument. No new statement
needs an edge-case test, and no consumer requires a forced adaptation.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
