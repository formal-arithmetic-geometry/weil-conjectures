## What changed

Replaced the sorry in `Algebra.improve_presentation_smooth_conormal_free` with a compiling
proof constructing the symmetric algebra of a small copy of the presentation's conormal.
The proof establishes finite projectivity directly from Mathlib's formal-smooth cotangent
splitting, obtains smoothness over A from `SymmetricAlgebra.smooth_of_finite_projective`,
constructs the augmentation, and proves surjectivity of the explicit finite polynomial map
by module-span induction followed by symmetric-algebra induction. Its original signature
and its public imports are unchanged. Both its docstring and DAG proof now follow this route.

A new module `Sheaf.RingTheory.SymmetricConormalFreePresentation` states only the remaining
conormal freeness of that explicit evaluation map. It allows the coefficient quotient to
be identified with A and the conormal to be replaced by a linearly equivalent module in
another universe. Its dependency on the existing symmetric-projective conormal calculation
is retained. No definitions or interfaces of existing dependencies were changed.

## Proved and sorry left

Closed: `Algebra.improve_presentation_smooth_conormal_free`
(node `lem-weil-pbc-improve-presentation-smooth-conormal-free`). No sorry remains in the
item module.

Added: `Algebra.Presentation.symmetric_conormal_free_presentation`
(node `lem-weil-pbc-symmetric-conormal-free-presentation`), exactly `:= by sorry`.
This is a decomposition: one upper hole closed and one strictly smaller lower hole added,
net zero holes. The lower theorem only asserts freeness for the explicitly specified map;
it contains no smoothness assumption on A, no existential algebra C, no relative smoothness,
no retraction, and no surjectivity conclusion. All those other parts are proved in the item.
No other holes or data definitions were added.

The item and new module compile through lcompile.py. A separate scratch experiment also
compiled the extraction of a free extension conormal from the two equivalences provided by
`Algebra.symmetric_projective_presentation_conormal`; the unfinished part is transport
from its literal-quotient, iterated-polynomial interface to the new theorem's interface.

## No longer needed

Removed the item's proof import `Sheaf.RingTheory.SmoothLocalizationConormalSplit` and its
node `lem-weil-pbc-smooth-localization-conormal-split`: Mathlib directly splits the
unlocalized conormal differential. Its auxiliary principal-localization construction and
Jacobi--Zariski route are unnecessary for this proof.

Removed the direct proof import `Sheaf.RingTheory.SymmetricAlgebraFinitePresentation` and
the direct proof dependency `lem-weil-pbc-symmetric-algebra-finite-presentation`: the
polynomial map is explicit, and the item proves its surjectivity by induction. This module
is still needed through the smoothness theorem, so no global pruning of it is claimed.

Removed the item's direct import and direct proof dependency of
`Sheaf.RingTheory.SymmetricProjectivePresentationConormal` /
`lem-weil-pbc-symmetric-projective-presentation-conormal`; they remain needed through the
new remaining conormal theorem. They are not globally pruned. The other original
statement-definition dependencies and the symmetric-algebra universal property remain.
No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing conormal lemma is valid but returns extension conormals over a literal
polynomial quotient, with iterated polynomial variables and a single ring universe. The
item needs an arbitrary presented A, a Type v algebra even when R is in Type u, and an
ideal conormal over its own quotient ring. The new theorem isolates those conversions
and the finite-variable reindexing, without altering the old statement.

The old localization-at-one step is unnecessary: the formal-smooth criterion already
provides the conormal split injection, and the finite-presentation relations prove
finiteness. The concrete Shrink construction uses a proved Mathlib smallness theorem,
not arbitrary data chosen from an unproved existence claim.

LeanSearch was attempted twice and returned an Internal Server Error. LeanFinder, Loogle,
and source searches were completed and recorded; no verdict was inferred from the failed
service. The source file literature/stacks-project/smoothing.tex is absent on this machine;
the referenced proof was read from https://stacks.math.columbia.edu/tag/07CE.

## New nodes

`lem-weil-pbc-symmetric-conormal-free-presentation` states freeness of the kernel conormal
of the explicit map to the symmetric algebra of a projective presentation conormal.
Its source is Stacks 07CE's polynomial surjection and conormal sequence, specialized to
no localization. Its complete proof in words uses the existing symmetric-projective
conormal lemma, transports the coefficient and module equivalences, flattens/reindexes
variables, and transports the kernel quotient scalar structure. The existing lemma is
not duplicated: this node is its interface conversion to the exact finite evaluation map.
Edge cases checked mathematically: zero rings, n = 0, m = 0, and differing universes;
empty relation families give zero conormal and an isomorphism presentation, while the
zero-ring case gives zero conormal modules. No change record is needed.

## Second reading by G2

1. Compared the delivered item with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof text, proof imports, and the documented route differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no errors, forbidden commands, or `sorry` in the item; the sole remaining `sorry` is the named theorem `Algebra.Presentation.symmetric_conormal_free_presentation`, with its matching node and proof docstring. Verdict: pass.
3. Checked the split statement against the explicit evaluation map, including zero and empty-index cases and universe changes. It is a true, strictly smaller interface-conversion lemma and is not duplicated in the library or Mathlib. Verdict: pass.
4. Checked the proof route from the target downward and the removed imports/dependencies. The direct formal-smooth splitting and explicit symmetric-algebra induction are shorter; the old localization and finite-presentation imports are unnecessary. Verdict: pass.
5. Checked the DAG proof, `proof_deps`, `proof_origin`, new-node metadata, and unit route against the Lean proof. The unit and its realized route remain intact. Verdict: pass.

Changed during second reading: no mathematical or interface changes; the report and this review section were completed. The delivered files remain the compiled versions described above.
