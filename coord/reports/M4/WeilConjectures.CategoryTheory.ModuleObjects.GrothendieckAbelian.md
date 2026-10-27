## What changed

Filled both original instance bodies in
WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian, retaining current upstream
statements and text. The closedness proof restores the saved coequalizer/adjoint-functor
argument with fully qualified module actions. The functorial flat resolution uses the proved
split free-tensor comparison from the existing extracted helper module, private helpers,
and the explicit composite forget/resolution/free with free(pi) followed by the counit.
Only the needed TensorRegular and FreePresentation proof imports were added.

Both proofs derive ambient tensor additivity internally, preserving the original elaborated
interfaces which omit the section's unused MonoidalPreadditive parameter. No public helper,
consumer edit or mathematical definition change was made. The route follows the existing
lem-weil-pbc-module-relative-tensor-adjoint and
lem-weil-pbc-module-functorial-flat-resolution plans; no DAG route changes are needed.

Validation: the item and the unchanged consumers
Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom,
Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian,
and WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory compile together in import
order against this packet (9.3, 5.0, 8.0, 5.1 seconds). Consumer verification copies were
removed from the delivery. Separate source probes confirm identical original and completed
elaborated types. Both completed instances have exactly propext, Classical.choice and
Quot.sound as axioms. The final direct source probe compiled in 9.8 seconds.

Change record: coord/changes/M4-module-grothendieck-upstream-proof-restoration.md.

## Proved and sorry left

Closed 2 of 2 original holes:
- CategoryTheory.Mod.monoidalClosed.
- CategoryTheory.Mod.hasFunctorialFlatResolution.

Added 0 holes; split off 0 statements. No sorry remains in any declaration of the item or
elsewhere in the delivery. The unchanged historical module docstring still describes the
original holes; it was retained under the source-library boundary.

## No longer needed

None. No pre-existing import, module, declaration or DAG dependency was withdrawn.
The saved TensorRegular import is required by the free-tensor proof. The extracted
UpstreamExtra module cannot be imported because it imports this item; its public theorem
and current consumers remain intact. The separate equalizer internal-Hom module remains
needed for its stronger explicit equalizer specification and is not claimed as pruned.

Searches used launcher LeanFinder (free internal flat modules: only concrete module hits),
Loogle (the special adjoint functor theorem), launcher grep, and local source searches.
The successful shorter argument already existed in the saved proof and extracted helpers.

## Where the brief, the DAG or earlier work was wrong

The saved preferred-upstream file restored only monoidalClosed; hasFunctorialFlatResolution
was still sorry. The saved action notation was out of scope, causing the sync's parse error;
fully qualified ModObj.smul fixes it. The original elaborated instances have no
MonoidalPreadditive binder despite that hypothesis appearing in the surrounding context;
deriving it inside both proofs avoids silently strengthening their interfaces.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
