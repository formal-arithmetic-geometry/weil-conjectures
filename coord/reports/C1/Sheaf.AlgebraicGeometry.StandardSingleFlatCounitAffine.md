## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitAffine.lean`
from the precise archive named by its current `coord/rework.tsv` row. Preserved
`AlgebraicGeometry.standardSingleFlatCounitOnOpen_affine` with its complete public
signature, original docstring, visibility and public presentation import.

Added the proof import
`WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` for the
existing pinned counit and additive tensor-pullback instance. The unmodified
archive fails with unknown `SingleComplexBaseChange.counit` and missing
`(Scheme.Modules.tensorPullback g).Additive`. The private comparison proof uses
explicit standard derived-category universes and packages the source comparison
as the composite of two existing isomorphisms. This is the same actual affine
single-complex construction and canonical counit equation as in the archive.

The item node `lem-pc-standard-single-flat-counit-affine`, all seven declared
proof dependencies and the unit `sk-thm-picard-coherence` retain their existing
attachments and proof plans. The affine direct-image module is flat by its
sectionwise relative flatness. The Cech dimension-shifting argument proves
acyclicity; the canonical single comparison, ordinary affine exchange and
`derivedBaseChange_unit_compatibility` provide the two isomorphisms and their
commuting counit equation. The single complex is zero away from degree zero.
The proof continues to cover empty affine opens and the zero module without
assuming flatness of the base-change morphism.

The import-direction check permits the upstream counit provider. A source
comparison confirms the public signature is preserved verbatim. The live-source
consumer inventory is empty; the reverse scan including quarantine finds the
one direct consumer `StandardSingleStalkFlatCounitModel` and its affine-induction
use, with 76 transitive consumers. No consumer signature or proof is adapted.

Validation through `lcompile.py`: the final restored source compiles without
errors or warnings (48.6 seconds). A separate scratch module repeats the archived
parent's exact affine-induction application with its original binders; it compiles
against the restored module (2.5 seconds). Its `#print axioms` for
`standardSingleFlatCounitOnOpen_affine` lists exactly `propext`, `Classical.choice`
and `Quot.sound`. Scratch checks remain outside the delivered `lean/` directory.
Profiling options were removed. No file or proof was split and no time limit was
raised. Explicit universe annotations fix the implicit category choices which
caused the initial repaired-import compile to exceed the file limit.

Change record:
`coord/changes/C1-standard-single-flat-counit-affine-restoration.md`.

## Proved and sorry left

This is an assigned zero-hole quarantine restoration. The archived module has
zero `sorry`; the restored theorem and every private helper have complete proofs.
Holes closed: none (0). Holes added: none (0). Split-off statements: none (0).
Every `sorry` remaining in the item or added elsewhere: none.
The restored theorem is `AlgebraicGeometry.standardSingleFlatCounitOnOpen_affine`
(node `lem-pc-standard-single-flat-counit-affine`). No new theorem proof is
claimed as net hole reduction.

## No longer needed

No mathematical node, module, import or unit step is pruned. All archived proof
imports are retained for the actual argument. The explicit proof import of the
current counit provider restores visibility of the existing recorded dependency.
The quarantine archive and its dependencies remain intact. No `deleted.txt` or
new node is needed.

The fresh LeanFinder search returned ordinary scheme-module pushforward,
pullback adjunctions and scheme-morphism flatness results, rather than the
canonical derived presentation. The Loogle query for `rightAcyclic` and the
Mathlib grep for an affine counit returned no exact replacement. Local searches
find the existing proof tools already used by the archive. The complete existing
argument is retained rather than replaced by another split-off obligation.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with an unfinished theorem, but the
current assignment is a quarantine rework item whose archived proof already has
zero holes. Its absence from `lean/` does not mean the result is unnecessary:
the quarantined parent still cites it in its DAG proof and applies it in the
affine branch of source-open induction. The repair restores that exact result.
The archived code also relies on counit visibility which was not supplied
by the compiled presentation import at the initial check; the explicit provider
import fixes this. The separately repaired presentation root has since been
verified, and the private import keeps this proof's own dependency explicit.
No false statement, target change or departure from the unit route was found.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
