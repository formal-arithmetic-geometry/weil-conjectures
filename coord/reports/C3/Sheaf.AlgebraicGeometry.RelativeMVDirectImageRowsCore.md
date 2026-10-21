## What changed

Restored `lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageRowsCore.lean`
from the complete archive named in `coord/rework.tsv`. The public theorem
`AlgebraicGeometry.relativeMV_direct_image_rows_core`, its entire proof,
its docstring, and the private proved helper `roof_mate_transport` are
unchanged from the archive. Both public imports are preserved and placed
before the two private proof imports. Four unused private imports are removed.

The proof obtains a normalized roof of short exact rows from
`relativeMV_direct_image_row_roof`, then applies
`relativeMV_homotopyPullback_row_strictify`. The localized projection supplies
three source vertex isomorphisms. The private helper cancels the invertible
roof denominator and applies `Adjunction.homEquiv_naturality_left` to transport
all three mate equations. Target vertices and target exactness are retained.
No statement, definition, unit route, DAG attachment or target changes.

Change record:
`coord/changes/C3-relative-mv-direct-image-rows-core-restoration.md`.
The operative repair restores the missing library module; it is not a rebase
or an edit of an already present proof.

Validation through `lcompile.py`: the restored item compiled without errors
or warnings in 13.7 seconds. The sole direct archived consumer,
`Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsPreoverlap`, compiled
unchanged against the restoration in 5.3 seconds. A separate axiom probe
reports exactly `propext`, `Classical.choice` and `Quot.sound` for the theorem.
The public declaration and proof, and the private helper, were compared with
the archive and are textually identical. Every Lean line is at most 100
characters. Validation sources under `validation/` and `scratchpad/` are not
delivered.

The published compiled row-roof dependency initially imported the retired
`Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap`, conflicting with the
current public source-library import. Compiling the unchanged current
`RelativeMVDirectImageRowRoof.lean` alongside the item resolves this stale
compiled dependency. That source is included in the compilation set and is
byte-identical to the live library file, so it contributes no delivered diff.

## Proved and sorry left

Assigned zero-hole restoration. Holes closed: none (0 of 0).
Holes added: none. Split off: none. Sorries left: none.
`AlgebraicGeometry.relativeMV_direct_image_rows_core` and the private helper
`roof_mate_transport` are fully proved. The public theorem has no dependency
on `sorryAx`.

## No longer needed

Removed these unused private imports from the archived item:

- `WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare`
- `WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisPresentation`
- `WeilConjectures.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`

The item uses only the row-roof theorem, generic strictification, adjunction
naturality and isomorphism cancellation. The removed imports concern the
construction already encapsulated by the roof dependency. This does not
withdraw any source-library declaration or assert that those nodes or their
modules are globally unused. No module or node is pruned, and the DAG's
existing dependencies and Lean attachment are preserved. Both private
imports retained in the file are used directly by the proof.

## Where the brief, the DAG or earlier work was wrong

The rework row, rather than an open `sorry`, specifies the actual repair:
the module was quarantined after a failed cluster restore. The archive has
zero holes and already proves the exact recorded statement. The current
`coord/returns/C3.md` has no return specific to this item.

The existing node describes resolved rows and strictification, while the
archive factors the resolved-row construction through the already restored
row-roof theorem. As noted in the B2 roof restoration report, the archive's
`lem-pc-relative-mv-direct-image-row-roof` tag lacks a DAG node in the current
snapshot. This delivery preserves that pre-existing proof route and all
existing attachments; it introduces no new declaration or proof obligation.

The required searches ran through `msearch.py`. LeanFinder returned general
localization and derived-adjunction lemmas, rather than this specialized
row construction. Loogle did not recognize the unqualified
`Adjunction.homEquiv_naturality_left` query. Grep located the naturality API;
inspection of Mathlib's actual declaration confirms the exact equation
used by `roof_mate_transport`. Searches of both library roots found no
shorter theorem with the item's unrestricted hypotheses. The source SES
presentation is not a replacement: it assumes affine bases and qcqs
morphisms and presents rows on the target, whereas this item retains a
source row before derived pullback. No new edge-case hypothesis is needed:
empty or repeated opens, zero coefficients and zero coefficient maps are
handled by the same archived functorial construction.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
