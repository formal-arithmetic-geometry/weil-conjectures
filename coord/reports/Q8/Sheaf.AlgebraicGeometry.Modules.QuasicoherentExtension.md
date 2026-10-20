## What changed

Retired Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension, a depth-zero retire
item listed in coord/retire-items.tsv. The source library already proves precisely
AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_shortExact in
WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension; the official
Modules.QuasicoherentExtension twin publicly reexports it. The removed Sheaf file
only reexports this result and retains two unused private proof declarations.

Updated the three current consumers. DerivedDirectImageBoundedBelowQCoh and
LocalizedComplexQCHomologyExtension import the official twin instead.
FiniteFreeHomComplexQCCohomology drops the redundant import because it already
imports the canonical cohomology module. Consumer declarations and proof bodies,
all upstream files, and all target statements are unchanged.

Reattached node lem-pc-quasi-coherent-extension to the official twin, recording its
canonical declaring module in lean.note. The node statement and its mathematical
proof plan remain unchanged; this delivery retires an unused implementation.
Change record: coord/changes/retire-quasicoherent-extension-Q8.md.

Validation: lcompile.py --all compiled all three adapted consumers successfully
in 19.0, 21.7 and 28.7 seconds, with no diagnostics. Source diffs confirm that
only the three proof-import lines changed in these consumers.

Searches actually run with msearch.py: LeanFinder for extension closure returned
quasi-coherent definitions and the abelian-category instance, not this theorem;
Loogle for its full name reported unknown identifier; grep for its short name
returned zero indexed hits. Direct source rg found the exact proved theorem and
confirmed that both helpers removed from the Sheaf file were private.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero holes left in the
withdrawn module or the three adapted consumers. This is a retirement, not a new
proof or a decomposition. The existing canonical theorem is preserved verbatim.
Removed already-proved private helpers tilde_preservesKernel and
isQuasicoherent_of_shortExact_via_tilde; neither was a public declaration.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension.
Removed its import from all three remaining consumers.
With the unused private tilde proof, its imports of
WeilConjectures.AlgebraicGeometry.Modules.AffineExtensionSectionSurjectivity and
Mathlib.CategoryTheory.Preadditive.LeftExact are no longer needed through this
wrapper. The other imports removed with the wrapper are
WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension,
WeilConjectures.AlgebraicGeometry.Coherent,
Mathlib.Algebra.Homology.ShortComplex.ShortExact and
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel.
All adopted source modules and declarations are preserved; no global retirement
of their modules or DAG nodes is claimed.

The canonical theorem remains needed. Its node lem-pc-quasi-coherent-extension
therefore remains attached to the upstream twin. No new nodes or proof dependencies
were introduced. The original DAG proof dependencies remain as the mathematical
plan, not new work imported by this retired implementation.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module with sorry; this assigned item is
actually listed as retire and already has zero sorry. The retirement queue lists
five consumers, but two have already migrated; source search found exactly three.
Its API-difference note lists tilde_preservesKernel and
isQuasicoherent_of_shortExact_via_tilde as missing upstream, but both are private
and have no external users. They require no replacement API.
The DAG's Lean attachment still pointed to the obsolete Sheaf wrapper; it now
points to the upstream compatibility module providing the same public theorem.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
