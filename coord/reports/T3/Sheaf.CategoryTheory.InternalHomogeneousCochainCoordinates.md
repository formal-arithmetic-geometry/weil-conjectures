## What changed

The original theorem `CategoryTheory.CondensedBar.exists_internalHomogeneousCochainCoordinates`
is proved from two strictly smaller construction lemmas. The given inhomogeneous bar
complex itself presents the homogeneous complex: its inclusion is the successive-quotient
map from `BarHomogeneousInclusion`. The coordinate isomorphism is the identity on this
presentation. The original specifications permit this because they require a sectionwise
injective inclusion with exactly the homogeneous sections as image and the deletion
differential; they do not require a particular implementation of the subobject.

The combination proof establishes the prefix/quotient cancellation for arbitrary
noncommutative groups, both coordinate formulas, both degree-zero formulas, homogeneous
restriction evaluation from inhomogeneous restriction evaluation, both restriction
squares, and the derived representatives after extension by zero. The degree-zero internal
isomorphism is constructed and proved independently in `InternalBarZeroEvaluation`.

The unchanged definitions are relocated to the publicly reexported
`InternalHomogeneousCochainCoordinateData` so the construction modules can import them
without a cycle. Original definition bodies and signatures are retained. This is recorded
in `coord/changes/T3-internal-cochain-coordinate-data.md`. No existing module besides the
item is changed, and there are no direct Lean importers to adapt. The original node's
statement is unchanged and its proof now records the actual presentation argument.

Validation: all five delivered Lean modules compile through `lcompile.py`. The shared
definitions took 11.3 seconds, inclusion and restriction specifications 1.1 seconds each,
the proved zero-evaluation construction 6.6 seconds, and the combination theorem 11.2
seconds. There are no compiler errors or warnings. A byte comparison verified that all
eight relocated data declarations and the original theorem signature are unchanged;
all delivered Lean lines have at most 100 characters.

## Proved and sorry left

The item originally had one hole, in
`CategoryTheory.CondensedBar.exists_internalHomogeneousCochainCoordinates`; its body now
contains no holes. This is a decomposition, not a complete proof without further holes:
one original hole is closed and two strictly smaller holes are added (net minus one).

The delivery also proves
`CategoryTheory.CondensedBar.exists_internalBarZeroEvaluation`
(node `lem-sfb-internal-bar-zero-evaluation`) by constructing the internal evaluation map,
proving its sectionwise bijectivity and reflecting isomorphisms through the forgetful
functors. No data definition contains a hole.

The two remaining holes, each exactly a named public theorem with source and complete
proof in words, are:

- `CategoryTheory.CondensedBar.exists_barHomogeneousInclusion`, node
  `lem-sfb-bar-homogeneous-inclusion`: construct the successive-quotient internal inclusion
  with image, naturality and deletion differential. This is steps 1--4 for one fixed
  group and bar diagram; it does not give group restriction, degree zero, coordinates
  or the derived comparison.
- `CategoryTheory.CondensedBar.exists_internalBarRestrictionEvaluation`, node
  `lem-sfb-internal-bar-restriction-evaluation`: construct the inhomogeneous restriction
  cochain map along a fixed continuous homomorphism with its evaluation formula. It
  asserts no homogeneous presentation, coordinate square or derived comparison.

All data chosen in the combination proof are uniquely fixed by their evaluation
formulas: every parameter map into a finite power is a tuple, and the evaluation
bijection detects sections. Thus the inclusion and restriction internal maps are fixed
on every section and hence as morphisms; all their other fields are proofs. The
homogeneous complex is explicitly the given bar complex. The degree-zero witness is
constructed by a proved theorem. No arbitrary data are chosen from mere existence.

## No longer needed

No original mathematical dependency is pruned. The original bar-data, action-module
and derived-category definitions remain needed. The two old direct public imports
`Sheaf.CategoryTheory.CondensedEquivariantBarData` and
`Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic` now occur in the definitions-only
module and remain publicly visible through its reexport.

The proof avoids constructing a separate homogeneous submodule complex, proving its
square-zero deletion differential separately, and constructing two separate inverse
cochain maps. These are proof steps avoided by using the bar complex as the subobject's
presentation, not existing modules or declarations withdrawn. No module is deleted.

## Where the brief, the DAG or earlier work was wrong

The original eight-step calculation is mathematically sound. Its blanket classification
of the internal-map constructions as elementary understates the Lean glue: natural
linear section maps must be lifted through the section-module equivalence and the
bar-term isomorphisms, and the differential identity still needs the signed face
calculation. These are now explicit smaller construction statements. The parent theorem
needs only their stated conclusions, not access to their proofs.

Edge cases checked in the formulas: n=0 gives an empty quotient tuple and the unit prefix;
the deletion boundary is x₁c-x₀c; no commutativity of J is used; characteristic two changes
no cancellation or signed-sum formula; the zero module and zero coefficient ring are
allowed. Empty profinite tests are retained in all quantifiers and in the degree-zero
natural-family construction. No hypothesis on injectivity or topological presentation
of coefficient modules is introduced. The unit route is retained; this is an auxiliary
calculation below its open-direct-image step.

## New nodes

`def-sfb-internal-cochain-coordinate-data` attaches the definitions relocated verbatim to
`InternalHomogeneousCochainCoordinateData`. It asserts no new existence result and removes
no original declaration. The change record is
`coord/changes/T3-internal-cochain-coordinate-data.md`.

`lem-sfb-bar-homogeneous-inclusion` states the successive-quotient inclusion construction
and deletion calculation from the original node's steps 1--4. Its module is
`BarHomogeneousInclusion`, and its existence theorem remains to be proved.

`lem-sfb-internal-bar-zero-evaluation` isolates the empty-tuple isomorphism from the
original step 2 in `InternalBarZeroEvaluation`; the delivery proves this construction.

`lem-sfb-internal-bar-restriction-evaluation` states only the inhomogeneous restriction
construction from the original step 7, in `InternalBarRestrictionEvaluation`. The
combination proof derives homogeneous restriction and both coordinate squares from it.

Each new node cites the same Stacks 0DVG displayed differential with the internal
adaptation made explicit, inherits the parent unit and current blueprint ancestor, and
records the actual Mathlib searches from this sandbox. Searches found discrete and
topological representation variants, not arbitrary internal condensed-module versions.
Blueprint searches for homogeneous cochain, bar restriction and bar zero returned no
matches. The existing section-module equivalence is used rather than restated.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
