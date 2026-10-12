## What changed

Replaced the hole in `CategoryTheory.exists_cartanEilenberg_resolution` with a complete
Lean proof assembling alternating exact rows into a bicomplex and transporting their
injectivity and quasi-isomorphism properties. Its signature, visibility and existing
public imports are unchanged. No existing definition or statement was changed.

Added three modules:

- `Sheaf.CategoryTheory.CartanEilenbergRows` defines genuine diagram data for the two
  alternating short exact rows, constructs the horizontal complex by the composite
  through boundaries and cycles, proves square zero, and constructs its augmentation.
  It assumes no injectivity, quasi-isomorphism or boundedness properties.
- `Sheaf.CategoryTheory.CartanEilenbergRowsExists` states the remaining construction of
  compatible injective resolution rows. This is the original argument's first two
  steps and their augmentation squares; it does not assert the bicomplex's cycles,
  boundaries or homology properties.
- `Sheaf.CategoryTheory.CartanEilenbergRowsIdentifications` proves, without holes, the
  generic identifications and their compatibility with all induced augmentations.
  The proof constructs kernel and cokernel universal properties as left homology
  data and uses an epi-mono factorization for images. It uses no enough-injectives
  hypothesis and no injectivity or quasi-isomorphism hypotheses.

The original theorem obtains rows, uses their explicit complex and augmentation,
transfers injectivity with evaluation isomorphisms, and cancels the identification
isomorphisms from the three quasi-isomorphism equations. The delivery is a decomposition
with a proved generic verification, not an axiom-free proof of existence.

Read Stacks Tags 015H and 015I at https://stacks.math.columbia.edu/tag/015H and
https://stacks.math.columbia.edu/tag/015I. The fetched Stacks source is not present in
this clone. Read the prescribed horseshoe signature and proof in the current library,
and Mathlib's kernel, image, left homology and quasi-isomorphism APIs. Searches made
through msearch.py are in searches.jsonl: LeanFinder finds ordinary object resolutions;
Loogle finds cyclesMap and LeftHomologyData.homologyIso; grep finds generic homology
machinery but no Cartan--Eilenberg construction. LeanSearch returned Internal Server
Error and is recorded as unavailable, without a claimed mathematical verdict.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.exists_cartanEilenberg_resolution`
(node `lem-sp-cartan-eilenberg-exists`). Its proof contains no `sorry`.

Added one hole:
`CategoryTheory.exists_cartanEilenberg_rows`
(node `lem-sp-cartan-eilenberg-rows-exists`). This is the sole `sorry` in all delivered
modules. It has an explicit source and complete construction in its docstring and node.
The main theorem still depends on this hole. Holes closed minus holes added is zero;
this is a decomposition, not a claim of a net decrease in the target closure.

Also proved `CategoryTheory.cartanEilenberg_rows_identifications`, and the explicit
complex, adjacent differential formula and augmentation in `CartanEilenbergRows`.
The private `rowHomologyData` construction is fully proved and contains no hole.

All four delivered modules compile together in dependency order, without warnings.
The kernel/image/cokernel proof treats every integer p uniformly. Checked the proposed
row-existence statement at K=0, p<0, and the seam p=0: negative columns and D^0 must
be chosen zero, H^0 is identified with Z^0, and the first nonzero row uses that same
Z^0 resolution. Ordinary arbitrary resolutions of zero would not suffice for the
negative-column vanishing clause; the docstring specifies the required zero choices.
No arbitrary object is defined by choosing a witness of the unproved existence lemma:
its rows are eliminated only inside the proposition proving existence.

## No longer needed

Removed `import Sheaf.CategoryTheory.DoubleComplexTotal` from the item's module.
Its filtration, totalization, diagonal coproduct and graded-piece constructions are
unused: this existence statement only needs Mathlib's bicomplex type. The proof no
longer needs the proof dependency `def-sp-double-complex-total` or its module
`Sheaf.CategoryTheory.DoubleComplexTotal`; its bicomplex notion remains in the unchanged
statement and is represented directly by Mathlib. No assertion is made that other
project targets cease importing this module.

Removed the direct proof import of
`Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions` from the item's module.
It remains imported by `CartanEilenbergRowsExists` and remains a needed dependency:
`lem-sp-horseshoe-prescribed-resolutions` is NOT pruned. Its own lower construction
modules are likewise not pruned.

The original ordinary resolution dependency
`lem-weil-pbc-left-exact-injective-resolution-degree-zero` and injective-resolution
notion remain needed by the row-existence node. The abelian-category dependency remains
needed by the diagram and generic identification node. No other original dependency
is declared unnecessary. No blueprint unit statement or realized proof step is bypassed:
`sk-prop-av-pqf-finite` has no realization entry for this auxiliary existence lemma.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The planned verification needed generic
kernel/image/cokernel glue not bundled in any recorded declaration. That glue is now
proved, rather than postponed. Mathlib's ComplexShape.next/prev are chosen indices,
not definitionally p+1 and p-1; the proof uses sc' and its canonical cycle/homology
isomorphisms, with explicit arithmetic proofs for the neighboring indices.

The resolution-row construction remains the unfinished portion, with its induction,
negative-degree choices and the exact single-degree-zero identifications named explicitly.
The parent node's proof and proof dependencies now match the Lean reduction.

## New nodes

`def-sp-cartan-eilenberg-rows` records the alternating exact diagram, its four compatible
augmentations and the explicit associated complex. Its module contains no hole and
introduces no alternative definition of an injective resolution or bicomplex.

`lem-sp-cartan-eilenberg-rows-exists` records the remaining compatible-row construction
from Stacks 015I Steps 1--4 and the prescribed horseshoe form of 013T. It is strictly
part of the original argument: no bicomplex homology identification is in its conclusion.

`lem-sp-cartan-eilenberg-rows-identifications` records the generic, fully proved
kernel/image/cokernel argument in the conclusion of Stacks 015I. It has weaker category
requirements and no resolution hypotheses. Its augmentation equations are checked by
cancelling monic cycle/image inclusions and the epic source homology projection.

All new nodes carry the three search kinds; the unavailable LeanSearch is recorded
honestly. No change record or forced adaptation is necessary.

## Second reading by S2

1. Compared the delivered `CartanEilenbergExists` module with the repository version.
   The theorem signature and all existing declarations are byte-for-byte unchanged;
   only proof imports and proof bodies changed.
2. Compiled all four delivered modules with `lcompile.py --all`. There are no compiler
   errors, forbidden declarations, or unlisted `sorry`s; the sole remaining hole is
   `CategoryTheory.exists_cartanEilenberg_rows`, with the matching node and source
   docstring. Scratch `#print axioms` checks confirm that the generic constructions
   and identification theorem use only the permitted ordinary axioms; the existence
   theorem also depends on `sorryAx`, precisely through the listed row-construction hole.
3. Checked each split statement against its Lean declaration and the Stacks 015H/015I
   route. The rows-existence statement is a strict decomposition of the target, while
   the rows structure and identification theorem are generic and have weaker
   hypotheses than the target. No duplicate Mathlib or library declaration was found.
4. Checked pruning and imports. `DoubleComplexTotal` and the direct horseshoe import
   are no longer used by the target proof; the horseshoe dependency remains a proof import in
   `CartanEilenbergRowsExists`. The DAG proof and `proof_deps` follow the imports and
   applications in the delivered Lean code, and the unit route is retained.
5. Checked edge cases in the rows statement (zero complex, negative columns, and the
   degree-zero seam) and the augmentation equations in the identification theorem.
   The theorem is mathematically appropriate for the remaining construction and no
   target statement was weakened.

Changed only the report by adding this second-reading record; no Lean statement or
definition was altered during review.
