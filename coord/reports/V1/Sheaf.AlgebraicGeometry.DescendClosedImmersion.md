## What changed

Proved `AlgebraicGeometry.exists_isClosedImmersion_stage_of_locallyOfFiniteType`
without changing its signature or any public import. A closed immersion is finite and
monic; the proof descends these two properties, takes a common upper bound, transports
both properties by pullback composition, and applies Mathlib's finite-monomorphism
criterion. Added proof-only imports of `Sheaf.AlgebraicGeometry.DescendFinite` and
`Sheaf.AlgebraicGeometry.DescendMonomorphism`.

Added the proved module `Sheaf.AlgebraicGeometry.DescendMonomorphism`, with one public
theorem and four fully proved private helpers. The new module publicly imports only the
Mathlib APIs used by its statement; its finite-stage comparison import is proof-only. Its diagonal argument follows Stacks
07RQ; isomorphism descent uses the existing sorry-free finite-stage model comparison
from 01ZM instead of the published 01ZL proof. Updated the assigned DAG node to the
route actually used and added the monomorphism-descent node.

Both modules compile without warnings through lcompile.py. `#print axioms` shows only
propext, Classical.choice and Quot.sound for the new monomorphism theorem. The assigned
theorem additionally reaches the existing sorry in finiteness descent; no new sorry is
introduced. Edge cases are preserved: empty schemes cause no cover or point selection,
there is a common upper bound even when schemes are empty, and i0 supplies the inhabited
index needed for cofilteredness. Neither local finite presentation of f0 nor a smallest
stage is assumed.

## Proved and sorry left

- Proved the assigned theorem
  `AlgebraicGeometry.exists_isClosedImmersion_stage_of_locallyOfFiniteType`
  (lem-weil-pbc-descend-closed-immersion), from the existing finiteness-descent declaration.
- Proved `AlgebraicGeometry.exists_mono_baseChange_stage`
  (lem-weil-pbc-descend-monomorphism); its four private helpers are also proved.
- No sorry remains in either delivered module. No sorry is added elsewhere.
- The existing, unchanged dependency
  `AlgebraicGeometry.exists_isFinite_baseChange_stage`
  (lem-weil-pbc-descend-finite) remains sorry in its own module; it is the next needed item.

## No longer needed

Removed the unused import `Sheaf.AlgebraicGeometry.LimitAffineTransition` from the new
monomorphism module; its proof gets the limit API from its proof-only upstream import.

Removed direct imports `Sheaf.AlgebraicGeometry.DescendAffine` and
`Sheaf.Paper.ColimitSurjectiveRingMap`. DescendAffine remains an indirect dependency of
DescendFinite, so this does not globally prune affineness descent.

The following original proof dependencies are no longer direct dependencies of the
assigned node (their definitions or some of their results can still occur below
DescendFinite or the proved monomorphism argument):

- lem-weil-pbc-closed-immersion-integral-separated-uc
- pqf-def-affine-morphism
- lem-weil-pbc-descend-affine — Sheaf.AlgebraicGeometry.DescendAffine
- def-pc-fibre-product — Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
- lem-weil-pbc-lft-base-change
- lem-weil-pbc-affine-open-spec-points
- def-weil-pbc-scheme-conventions
- lem-weil-pbc-open-fibre-product
- lem-weil-pbc-fibre-product-affine-spectra
- lem-weil-pbc-morphism-into-affine-scheme
- lem-weil-pbc-lft-affine-pairs
- def-weil-pbc-category-colimit — Mathlib.CategoryTheory.Limits.HasLimits
- lem-weil-pbc-limit-affine-transition — Sheaf.AlgebraicGeometry.LimitAffineTransition
- lem-weil-pbc-spec-colimit-limit
- lem-weil-pbc-closed-immersion-affine-cover-criterion
- lem-weil-pbc-colimit-surjective-ring-map — Sheaf.Paper.ColimitSurjectiveRingMap

In particular the original surjectivity argument through
`lem-weil-pbc-colimit-surjective-ring-map` / `Sheaf.Paper.ColimitSurjectiveRingMap`
and `lem-weil-pbc-closed-immersion-affine-cover-criterion` is not used. The original
finite affine-cover/tensor-product glue is not repeated in this item: finiteness descent
already packages the needed finite part. No unit statement or realized unit step is
bypassed; this item is below the unit level and its statement is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original DAG route is mathematically sound but longer than necessary with the
existing DescendFinite declaration and Mathlib's finite-monomorphism criterion.
The source finite-presentation closed-immersion theorem cannot directly replace this
item: f0 here is only locally finite type. Applying 01ZL as a black box for the new
monomorphism lemma would create a circular dependency because the published proof of
01ZL uses 01ZP. The delivered Lean avoids this using the independent, already proved
01ZM finite-stage model comparison. The proofs were checked against the Stacks sources
available read-only on this machine; no repository file was edited by hand.

## New nodes

`lem-weil-pbc-descend-monomorphism`, at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-descend-monomorphism.json`, states the
monomorphism component under the same locally finite type/qcqs assumptions. Its module
`lean/Sheaf/AlgebraicGeometry/DescendMonomorphism.lean` is fully proved, and it leaves no
new item with sorry. Three kinds of Mathlib search were attempted; LeanSearch returned
HTTP 500, while LeanFinder, Loogle and grep identified the useful existing tools.
No change record is needed: no existing statement or definition changed.


## Second reading by V1

1. PASS: compared the delivered item with the repository using diff and checked the
   existing theorem signature byte for byte. No existing statement, definition, or
   public import changed; no change record is required. The other module is new.
2. PASS: compiled both modules locally in import order without errors or warnings.
   There is no sorry or forbidden declaration in either module. Scratch-copy
   `#print axioms` checks of every delivered theorem, including all five private
   helpers, show only propext, Classical.choice, and Quot.sound, except that the
   assigned theorem also has sorryAx through the explicitly reported, unchanged
   `exists_isFinite_baseChange_stage`. The new monomorphism theorem is sorry-free.
3. PASS: no unfinished statement was split off. Read the new monomorphism statement
   and its four helpers from top to bottom; its diagonal is locally finitely presented
   by cancellation against a locally finite type projection, and the isomorphism
   descent uses the existing proved `exists_iso_of_isPullback`. Checked empty schemes,
   the identity system, and a preorder without a least index: no point is selected and
   i0 supplies nonemptiness. Repeated LeanFinder and Loogle searches with diagonal and
   later-index phrasing, and rg searches in Sheaf and the upstream scheme-limit module;
   no existing theorem gives this locally finite type monomorphism descent. Checked
   Stacks 07RQ in the locally available limits.tex. The new node's docstring gives the
   complete argument and its source; it is strictly one component of the item.
4. PASS: reviewed the finite-plus-mono reduction and the finite-stage model comparison
   source. The existing closed-immersion stage theorem assumes finite presentation
   and cannot replace this locally finite type statement. All old proof_deps removed
   from the assigned node occur in No longer needed. Read sk-thm-p1.json realized:
   neither delivered node realizes its statement or a step, and no unit route changes.
   Replaced the new module's unused public import of LimitAffineTransition
   with the precise Mathlib Morphisms.Affine import needed for IsAffineHom; the statement
   APIs are already provided by its public Mathlib imports, while the comparison
   theorem remains a plain proof-only import. The item's public imports stay unchanged.
5. PASS: both nodes' proof_deps equal the union of their steps' uses, and every cited
   node exists. Checked the existing node changes are confined to stage-3-owned fields;
   the new node has the required source, searches, created, blueprint, chapter, unit,
   and verbatim Lean statement. The proof and proof_origin describe the diagonal and
   independent model-comparison argument actually used, without claiming 01ZL.

Second reading replaced the new module's unused LimitAffineTransition import with
Mathlib.AlgebraicGeometry.Morphisms.Affine and updated
this report; the proof bodies and all theorem statements were left intact.
