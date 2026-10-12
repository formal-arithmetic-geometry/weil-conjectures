## What changed

The unchanged theorem `AlgebraicGeometry.isAffine_of_isFinite_surjective` now eliminates
`exists_noetherian_affine_factor`, applies the existing Noetherian theorem to its finite
surjective affine source, and applies Mathlib's `isAffine_of_isAffineHom` to the target
projection. The new module packages only approximation/descent, before the Noetherian
case. Its structure is ordinary data with property fields; no object is defined by choosing
an arbitrary witness from an unproved existence theorem.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.isAffine_of_isFinite_surjective` (1 of 1 original local
holes). Hole added: `AlgebraicGeometry.exists_noetherian_affine_factor` (node
`lem-weil-pbc-finite-surjective-affine-target-approximation`) in the new module.
No other holes were added or closed. This is a decomposition, not a completed axiom-free
proof or a positive net reduction in holes: one upper hole becomes one lower hole.
The new theorem's docstring gives the entire remaining approximation/descent argument.

## No longer needed

The following proof-only imports were removed from the item's module and moved to the
new approximation module, where they support its recorded proof plan:

- `Sheaf.AlgebraicGeometry.DescendFinite`
- `Sheaf.AlgebraicGeometry.DescendSurjective`
- `Sheaf.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`

The approximation module's unused proof-only import of
`Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian` was removed.
All original public imports remain unchanged and describe the public theorem's types.
No module is claimed pruned from the targets' import closure: the approximation dependencies
remain reachable through the new module. The target now directly uses just the new
approximation node, the Noetherian case, and affine-morphism permanence.
Every old direct `proof_deps` entry removed from the target node is listed here; all are
retained under the approximation node rather than discarded mathematically:

- `lem-weil-pbc-morphism-into-affine-scheme`
- `lem-weil-pbc-qcqs-over-affine`
- `def-weil-surjective-morphism`
- `lem-weil-pbc-finite-iff-integral-lft`
- `pqf-lem-integral-univclosed`
- `lem-weil-pbc-surjective-universally-closed-separated`
- `lem-weil-pbc-closed-immersion-integral-separated-uc`
- `def-weil-pbc-scheme-conventions`
- `lem-weil-pbc-integral-morphism-limit-of-finite`
- `def-weil-finite-integral-morphism`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-limit-affine-stage`
- `prop-nagata-noetherian-inverse-system`
- `def-nagata-noetherian-inverse-system`
- `lem-weil-pbc-cofiltered-limit-directed-reindex`
- `lem-weil-pbc-finite-type-over-noetherian`
- `pqf-def-locnoeth`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `thm-pd-spreading-out`
- `def-sbc-locally-finite-presentation`
- `def-pc-fibre-product`
- `lem-weil-pbc-colimit-initial-full-subcategory`
- `lem-weil-pbc-scheme-over-limit`
- `def-weil-finite-type-morphism`
- `lem-weil-pbc-descend-finite`
- `lem-weil-pbc-finite-morphism-permanence`
- `lem-weil-pbc-descend-surjective`
- `lem-weil-pbc-surjective-base-change`
- `def-pc-scheme`
- `lem-weil-pbc-limit-affine-transition`

## Where the brief, the DAG or earlier work was wrong

The first report called the reduction a proof without recording its zero net hole change,
and did not enumerate the removed direct dependencies. The first new node had the wrong
unit (`sk-thm-properbasechange` instead of its parent's `sk-thm-p1`), omitted dependencies
of its proof plan, and its theorem had only a summary rather than the required full proof
in words. The first proof suppressed the `haveI` linter instead of using ordinary `have`.
The proof-support change record was unnecessary: no existing interface is changed, and
the file-level linter option has now been removed.

## New nodes

`lem-weil-pbc-finite-surjective-affine-target-approximation`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-surjective-affine-target-approximation.json`,
with theorem in `lean/Sheaf/AlgebraicGeometry/FiniteSurjectiveAffineTargetApproximation.lean`.
It follows the parent's steps 1–7 and the affine-projection portion of step 9; the separate
Noetherian affineness argument remains in the parent proof. Its chapter and unit match the
parent. No change record is needed for the unchanged existing signatures and visibility.

## Second reading by R2

1. Compared the entire original module by diff and asserted byte-for-byte equality of
   the existing theorem signature. Its docstring, public imports and visibility are
   unchanged. No existing definition is changed; the only new data declaration is the
   explicitly specified structure. No target in Challenge.lean is changed.
2. Both delivered modules compile through lcompile.py in import order without warnings.
   Text inspection finds one sorry, exactly the named reported new theorem, and no
   forbidden declaration or hollow definition. Explicit scratch-copy `#print axioms`
   checks and the delivery-wide probe check the structure and theorem declarations.
   The target and approximation theorem use sorryAx as reported, plus only standard
   axioms; the structure and constructor use only standard axioms, with no sorryAx. Thus the target is decomposed,
   not finally proved.
3. Read the original nine-step plan and its declarations, and checked Stacks Lemma 01ZT
   at https://stacks.math.columbia.edu/tag/01ZT (the local literature file is absent on
   this machine). The factor statement stops before proving the Noetherian target
   affine, so it is a strict part of that argument, not a renamed target. Empty schemes
   cause no exception: surjectivity from empty X forces empty Y, and the empty stage
   supplies a factor. For a Noetherian affine Y, choose Z = Y, q = identity, W = X and
   g = f. No reducedness, nonemptiness, finite-type-over-a-field, or finite-presentation
   hypothesis is added. Repeated msearch leanfinder/loogle/grep searches with different
   wording and rg over Sheaf and WeilConjectures found no existing full factor theorem
   or general finite-surjective affineness theorem. LeanSearch returned Internal Server
   Error and is recorded as unavailable, without a fabricated verdict. Mathlib's cover theorem constructs
   an affine source of a surjection but does not provide this finite Noetherian stage.
4. Read from the top down: the parent contains a real combination of the approximation
   statement, existing Noetherian result and Mathlib permanence. No shorter direct
   theorem was found. Removed unused imports from the parent, moved its approximation
   proof-plan imports into the new module, and removed the new module's irrelevant
   Noetherian-case import. Enumerated every removed direct dependency above. Read
   dag/units/sk-thm-p1.json `realized`: neither the parent nor this auxiliary reduction
   replaces a realized unit statement or step. The same approximation/Noetherian
   route is retained, and the fixed unit record is untouched.
5. The parent proof/proof_deps/proof_origin match its three actual ingredients. The
   new node has the required creation, source, search, blueprint and Lean records,
   the parent's chapter/unit, complete proof steps and their exact dependency union,
   and its theorem signature verbatim. Its proof remains planned, as its named sorry
   declares. No unsupported progress or closure-pruning claim is made.

Second reading changed: removed unused parent imports and the unused approximation
Noetherian import; removed the linter suppression and replaced haveI with have; simplified
one redundant local instance; expanded the new theorem's proof docstring; corrected the
new node's unit, proof steps, dependency union and verbatim Lean statement; removed the
unnecessary change record; and corrected hole accounting and the exhaustive pruning report.
