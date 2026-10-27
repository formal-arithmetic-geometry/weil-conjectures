## What changed

Proved `AlgebraicGeometry.Scheme.relation_incidence_open_model` in
`Sheaf.AlgebraicGeometry.RelationIncidenceOpenModel`, with its signature and public
imports unchanged. Constructed the actual open image and its surjective flat locally
finitely presented incidence morphism. Used the existing kernel-pair theorem and
Mathlib's subsheaf API to prove the representing property, then obtained all base
changes by pasting Yoneda pullback squares. Naturality follows by cancelling the
open inclusion. Four proved private helpers handle image membership, local
surjectivity from the specified sheafification universal property, and singleton
fppf coverings over the base.

Updated the item's proof docstring and DAG proof to describe these arguments.
Added only private proof imports for `LocallySurjective`, `Types.Pullbacks`, and
`SubcanonicalOver`. No other module, declaration signature, definition, public
import, or target changed. No new nodes or unfinished intermediate results.

Searches used the supplied msearch LeanFinder, Loogle and grep services, plus local
search of Mathlib, WeilConjectures and Sheaf. No existing incidence-model theorem
was found. The useful results were flat-lfp universal openness, the kernel-pair
statement already assigned as a dependency, and Mathlib's sheaf-image API.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.relation_incidence_open_model`
(node `lem-trf-relation-incidence-open-model`), one of one original holes.
Added: zero holes. Remaining in the delivered module: zero holes.
The existing `AlgebraicGeometry.Scheme.etale_relation_kernel_pair` is used as
intended; its unfinished proof remains in its own unchanged module, and is not
counted as closed by this delivery.

Validation: the final module compiled cleanly through `lcompile.py` in 13.9 seconds.

The new private helpers `locallySurjective_of_universal`, `range_closed`,
`yoneda_locallySurjective_of_cover` and `over_cover` are fully proved.

## No longer needed

Removed direct private imports:
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the proof uses Mathlib's ordinary
  Grothendieck-topology sheaf and subsheaf API; its alternative precoverage
  convention is unnecessary here.
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`: local
  surjectivity follows directly from the specified universal property via the
  image subsheaf, in the value universe of the statement.

Removed this item's proof dependencies
`lem-weil-pbc-site-sheafification-sections-local` and
`lem-trf-fppf-covering-base-change`, and the former's obsolete top-level tool-use
approval. Cover pullback stability is used directly through the definition of a
Grothendieck topology, rather than through a separate indexed-cover theorem.
The local-representative theorem may still be needed by the unchanged kernel-pair
module and elsewhere: no declaration or module is withdrawn, and no claim is made
that it has left the overall target closure. All other original dependencies
remain in the updated DAG and are used by the geometric/sheaf argument.

## Where the brief, the DAG or earlier work was wrong

The original Step 5 instructed applying the large-valued sheafification local
sections theorem although the item specifies Type u-valued sheafifications on the
big site. This does not provide a direct instantiation of that theorem. The
specified universal property itself suffices: close the image of η' inside F',
extend to this subsheaf, and use uniqueness to prove the inclusion has a section.
This proves local surjectivity in the stated universe, without changing any
hypothesis or assuming a global small-valued sheafification functor.

The original geometric and kernel-pair argument is otherwise correct. The
closed-range form of sheaf descent avoids a separate pointwise joint-surjectivity
argument. Edge cases remain covered, including empty U', empty test schemes,
g = identity, and the diagonal relation. The unit route is preserved.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
