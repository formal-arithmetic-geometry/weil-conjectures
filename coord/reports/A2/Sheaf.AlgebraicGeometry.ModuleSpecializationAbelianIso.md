## What changed

The current item was already restored and completely proved by D3 before this
assignment. This delivery prunes an unnecessary mathematical dependency from that
proof: replace the public import of SmoothProperPrimeSpecialization by the existing
EtaleStalkSpecialization module. The hypothesis and all proof formulas now use
Etale.etaleStalkSpecialization, which is definitionally the same map as
Etale.strictLocalSpecialization. InverseImageStalkGerm is now a private proof import.
The full germ/colimit comparison proof and both private helpers remain complete.
No definition, target, binder, universe or mathematical hypothesis is changed.

The node lem-weil-pbc-module-specialization-abelian-iso records the canonical map
and replaces its smooth-proper theorem dependency by
 def-weil-pbc-etale-stalk-specialization. Its mathematical statement and the
blueprint unit route stay intact. Change record:
coord/changes/A2-module-specialization-canonical-dependency.md.

Searches: msearch leanfinder for module/abelian specialization compatibility found
only Zariski structure-sheaf and tilde-germ statements. Loogle sheafFiberCompIso and
msearch grep identified the general Mathlib stalk/coefficient comparison and germ
identity already used by the proof. Direct source search found the lighter
EtaleStalkSpecialization definition and its identical defining composite.

## Proved and sorry left

Zero-hole dependency repair: 0 holes closed, 0 added, 0 split off, 0 remaining.
AlgebraicGeometry.Etale.bijective_moduleSpecialization_of_abelianIso and the private
pullback_germ and strictLocal_germ helpers are completely proved. No sorry
occurs in any delivered Lean module. This is pruning, not a new hole closure.

The delivered item compiled with lcompile.py in 6.0 seconds. A separate consumer
probe compiled in 4.4 seconds, proved the two specialization definitions equal by
rfl, and applied the revised theorem directly to the original
IsIso (strictLocalSpecialization s t A) hypothesis. Its #print axioms contains
exactly propext, Classical.choice and Quot.sound. The probe is kept under
scratchpad, outside the delivered Lean modules.

## No longer needed

Removed public import Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization;
removed node dependency
lem-weil-pbc-smooth-proper-specialization-prime-to-characteristic from this item.
Only its duplicated specialization definition was used; the smooth-proper theorem
never participated in the comparison proof. The canonical map comes from
Sheaf.AlgebraicGeometry.EtaleStalkSpecialization instead. The required inverse-image
germ identities have an explicit private import. All other imports remain needed.

No module or declaration is withdrawn. In particular, smooth-proper specialization
remains needed by the quarantined parent ProperSmoothCurvesPrimeCoefficients,
which imports its module independently and combines that theorem with this
coefficient comparison. No unit statement or proof step is bypassed. The other
four declared proof dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The rework row still refers to the older quarantine failure, but the current source
already contains D3's compiling restoration. Copying that file unchanged would be
a no-op; this delivery instead removes its unnecessary smooth-proper dependency.
The DAG had attributed the duplicated map definition to the smooth-proper theorem
node although the canonical definition has its own existing node.

The source downstream scan finds no live importer. The quarantined direct parent
still uses this item at its original call; that call needs no adaptation because
the new hypothesis is definitionally equal to the old one. The compatibility
consumer checks this directly. No new nodes, definitions, or unproved lemmas were
introduced, and no source-library declarations were edited.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
