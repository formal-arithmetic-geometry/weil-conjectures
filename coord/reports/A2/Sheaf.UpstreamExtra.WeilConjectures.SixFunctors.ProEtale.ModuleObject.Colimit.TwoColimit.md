## What changed

Restored `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`
from its `coord/rework.tsv` quarantine archive. This is a zero-hole compilation repair.
Added `import all Sheaf.Paper.CondensedFiniteModelProofAPI` so the extracted private
factorization helpers and `bounded_tri_of_serre` are visible. Kept its original public
import, together with every other archived public import.

Added six proved private instance wrappers for graded-tensor compatibility and
preservation of integer-indexed colimits by tensoring, and functorial flat resolutions,
for the exact-derived comparison used by `algClDerivedIso`. Removed the dangling scoped option before
`end TwoColimit`, which otherwise opens an unnamed scope and prevents the sections
from closing. Made `autoImplicit false` explicit, wrapped the overlong extraction
comment, and disabled the private-module linter for this intentionally private
support module. All archived declaration signatures, definition bodies and proof
routes remain unchanged. No upstream source file was edited.

Added private imports of the existing flat-resolution and module Grothendieck-abelian
instances to make their source explicit.

Change record: `coord/changes/A2-restore-two-colimit-proof-helpers.md`.

## Proved and sorry left

The archived item has zero `sorry`s, and the restored item has zero `sorry`s.
Holes closed: none (0 of 0). Holes added: none. Split-off statements: none.
The new private instances `moduleTensorFour`, `moduleTensorLeft`,
`moduleTensorRight`, `moduleTensorColimits`, `moduleTensorFlipColimits` and
`moduleFlatResolution` are proved from existing instances. No theorem has been
replaced with an assumption. Existing dependencies may still rely on their own
upstream proof obligations; this repair does not claim those obligations closed.

## No longer needed

None. All archived declarations and public imports are retained. The item is
restored rather than withdrawn. No DAG attachment, proof dependency, module or
unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined repair, not a module with open proof holes. Its archive
uses private declarations from `CondensedFiniteModelProofAPI` with an ordinary
public import. That import does not expose private helpers; a separate proof-only
`import all` is necessary. The archive also lacks the higher-order tensor instances
at the exact-derived comparison and ends with `set_option ... in` applied to an
`end` command. The first server compile exposed those latter errors after the
private import was fixed.

There is no DAG node whose Lean attachment is this private-only extraction module,
and the file has no blueprint tags of its own. Original public two-colimit statements
and their existing attachments remain in the unchanged upstream module. No new node
or mathematical route is required for these import/elaboration repairs.

Consumer search across live and quarantined sources finds direct importer
`Sheaf.Paper.CoefficientFiniteDescentHom`; it requires no interface adaptation.
The change record lists all seven transitive consumers from `tools/downstream.py
--allow-missing`. The item compiled cleanly through `lcompile.py --all` in 24.8 seconds, with zero
warnings. The unchanged full direct consumer exceeded the 60-second compile limit;
this packet does not change it. A focused consumer importing only the restored module compiled cleanly in 3.1
seconds. It restates the exported Hom-surjectivity theorem and the finite-field
triangulated-property theorem, checking both the upstream and shared-API exports.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
