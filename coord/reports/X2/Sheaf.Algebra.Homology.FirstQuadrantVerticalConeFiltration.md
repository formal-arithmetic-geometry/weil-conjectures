## What changed

Replaced the sorry in `HomologicalComplex₂.firstQuadrant_vertical_cone_filtration`
with a compiling reduction. Its signature and all existing public imports are unchanged.

The new module `Sheaf.Algebra.Homology.ConeHorizontalStepStable` constructs the
horizontal summand maps, their source/target image joins, and their finite tails.
Its theorem `HomologicalComplex₂.coneHorizontal_step_stable` is fully proved:
the extended total differential preserves or raises horizontal index, the total
map preserves it, and the cone differential combines these maps. A pullback
argument extends the generating-map factorizations to the finite supremum.

The item's proved private helper `filtration_of_degreewise` constructs subcomplexes
with these degreewise tails, using the uniquely restricted differential; monicity
proves square zero and compatibility. It assembles them into an antitone filtration.
The item also proves the full-step bound, empty-step bound, and negative graded
vanishing. Nonnegative graded homology follows by applying the homology functor to
one remaining chain-comparison theorem and composing with Mathlib's shift-homology
isomorphism. Both added imports in the item are proof imports.

The only remaining obligation is in the new module
`Sheaf.Algebra.Homology.ConeHorizontalGradedIso`: identifying the consecutive-tail
quotient complex with the column cone shifted by minus the horizontal index.
This contains neither the existence of a filtration nor any of its bounds or
negative graded vanishing, so it is strictly part of the original argument.

## Proved and sorry left

Original hole closed:
`HomologicalComplex₂.firstQuadrant_vertical_cone_filtration`
(node `lem-sp-first-quadrant-vertical-cone-filtration`).

Also fully proved:
`HomologicalComplex₂.coneHorizontal_step_stable`
(node `lem-sp-cone-horizontal-step-stable`), and all private helpers in both the
item and the stability module. The item has no sorry.

One hole added and left:
`HomologicalComplex₂.coneHorizontal_graded_iso`
(node `lem-sp-cone-horizontal-graded-iso`). This is a decomposition of the original
hole into its remaining graded-complex comparison, not an unconditional proof of
the original result. Holes closed: 1. Holes added: 1. Net: 0.
No definition contains a sorry or chooses arbitrary data from an unproved existence
statement. The finite tails and subcomplex construction are explicit; only an
isomorphism used inside a theorem proof remains postponed.

Validation: all three modules compile together with lcompile.py, without warnings.
The new chain-comparison statement was checked on p=0 (no sign correction), odd p
(source scalar -1 corrects the shifted off-diagonal block), n=p-1 (source vertical
cone degree -1 is retained), and n<p-1 (both cone terms are zero). The constructed
bounds include n=-1 and n<-1; these cases are covered by the compiled arithmetic
and extension-by-zero arguments. For negative p, both steps p and p+1 are the whole
complex, including p=-1 where the second step is zero-indexed.

## No longer needed

No existing import is removed, and no module is claimed to leave the targets'
actual import closure in this delivery.

The old proof dependency `def-sp-double-complex-total` is removed from the
item node's `proof_deps`; it remains in `stmt_deps`. No existing module import
is removed, so this is a pruned planned dependency, not a pruned module.

The planned declaration family in `Sheaf.CategoryTheory.DoubleComplexTotal` is
not needed for this proof: `firstFiltration`, `firstFiltration_antitone`,
`firstFiltration_subcomplex`, `firstFiltration_zero`, `firstFiltration_finite`,
`firstFiltration_graded`, and all corresponding second-filtration declarations.
The proof instead uses Mathlib's existing total-summand and differential API.
The definition node `def-sp-double-complex-total` remains a statement dependency
for the bicomplex/total notions; this does not claim that node can be deleted.
The existing filtration and filtered-subquotient definition nodes remain needed.

Removed from the new module while minimizing imports: Mathlib.Data.Int.Interval.
The stability module uses Mathlib's subobject and abelian APIs directly, without
importing the filtered-complex module. The graded module publicly imports its data
module, filtered-complex definitions and Mathlib's shift construction; ShiftSequence
is imported privately by the item for its proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or signature correction was required. The planned
`def-sp-double-complex-total` declaration supplies an integer-bicomplex degreewise
filtration, rather than the required subobject filtration of a natural-total map
cone. Its interface does not directly provide this cone construction. The new
stability theorem and proved degreewise assembly fill that interface gap.

A simpler sign correction is available when comparing directly with the Mathlib
shift by -p: write e=(-1)^p, multiply the source summand by e, and leave the target
summand fixed. The shift already multiplies the whole column-cone differential by
e, so its off-diagonal block is e*f. This avoids the degree-dependent rescaling
used in the original proof plan for a reindexed cone with unchanged differential.

The source read is Stacks Tag 012X, the displayed first-filtration formula and
Lemma 12.25.1's signed vertical graded differential. The cone refinement is the
agent-written calculation already specified by the parent node. No unit route
was bypassed; the unit record has empty realized lists. Searches of the library,
DAG, and imported blueprint found no existing generic horizontal cone graded
comparison. The related CartanEilenberg cone filtration has a different complex
indexing and augmentation hypothesis and does not supply this statement.

LeanSearch returned HTTP 500 and is recorded as unavailable. LeanFinder returned
mapping-cone component and additive-functor comparison APIs, used or inspected
as appropriate, but no exact graded-filtration theorem. Logged Mathlib grep found
no cone-filtration/graded-cone theorem. The blueprint ancestor helper returned
None because the parent is itself a module-created node; the new nodes inherit
the explicit blueprint ancestor and via chain already recorded in that parent.

## New nodes

`lem-sp-cone-horizontal-step-stable`, in
`dag/nodes/sec-abelian-varieties/lem-sp-cone-horizontal-step-stable.json`, records
the explicit finite horizontal tails and their fully proved preservation by the
cone differential. Lean module: Sheaf.Algebra.Homology.ConeHorizontalStepStable.

`lem-sp-cone-horizontal-graded-iso`, in
`dag/nodes/sec-abelian-varieties/lem-sp-cone-horizontal-graded-iso.json`, is the
remaining chain-isomorphism statement for a filtration with those prescribed
degreewise tails. Lean module: Sheaf.Algebra.Homology.ConeHorizontalGradedIso.
Its docstring gives the quotient construction, sign calculation, inverse, and
boundary cases. Each new node includes the source, proof steps, logged Mathlib
searches and inherited unit/chapter/blueprint route.

The existing item's node copy updates only proof, proof_deps and proof_origin.
No definition or statement was changed, so no change record is needed.

## Second reading by X2

1. Interface preservation: PASS. Compared the item against the repository with
   diff and checked the existing theorem signature byte for byte, including its
   section hypotheses. The original docstring and public imports are unchanged;
   the two added imports are private proof imports. The new files have no
   repository counterparts. No target, existing definition, existing statement,
   or other group's module is changed. No change record is necessary.

2. Proof and trust: PASS as a decomposition. Independently compiled all three
   modules together with lcompile.py, without warnings or errors. Searched the
   delivered Lean for forbidden declarations and options. There is exactly one
   sorry, the entire proof of the public named theorem
   HomologicalComplex₂.coneHorizontal_graded_iso. Scratch #print axioms checks
   show only propext, Classical.choice and Quot.sound for coneHorizontalSummand,
   coneHorizontalImage, coneHorizontalStep and coneHorizontal_step_stable.
   The graded comparison and the original theorem additionally use sorryAx,
   as reported. The degreewise assembly constructs actual restricted maps and
   complexes; it does not choose an arbitrary object from an unproved existence
   statement. The delivery probe checks all file-local helpers as well.

3. Split statements: PASS. The remaining chain-comparison theorem assumes a
   filtration whose exact degreewise images are prescribed; it neither supplies
   that filtration nor proves its bounds or negative graded vanishing. These
   parts of the original argument are independently proved, so this is a real
   reduction rather than a renamed copy. Its docstring and node give the
   quotient isomorphisms, inverse projections, differential calculation and
   sign correction. Checked p=0, p=1 with a nonzero column map, n=p-1 (the source
   degree-zero term), n<p-1 (zero objects), and zero source or target. With
   e=(-1)^p, the graded cone has blocks -e*d_A, e*d_B, f; the shifted column cone
   has -e*d_A, e*d_B, e*f. Multiplying the source by e and the target by 1
   commutes with the differential because e squared is 1. This agrees with
   Mathlib's shift differential and its natural-total sign instance.
   Independently searched with LeanFinder for quotients of consecutive diagonal
   sums and with Mathlib grep for associated graded/total terminology; only
   additive-functor cone comparisons and total-shift APIs appeared, not this
   theorem. Also searched both local source roots and inspected the upstream
   degreewise-subcomplex API and the integer-total first-filtration API. Neither
   closes this cone comparison in a few minutes. The split remains necessary.

4. Route and pruning: PASS. Read the proof from its conclusion down through the
   filtration assembly, joint-generation argument, finite bounds and stability.
   The proof uses Mathlib's existing cone, total, extension, subobject and
   shift-homology APIs. The degreewise helper is direct; importing the upstream
   subcomplex module would introduce a larger dependency without closing the
   graded hole. The new public imports supply data or types used in their
   exposed definitions/signatures, including imageSubobject from Subobject.Limits
   and the cochain shift instance. Proof-only imports of the original item are
   private. No module is actually pruned. The removed old proof dependency is
   now explicitly named above. Inspected dag/units/sk-prop-av-pqf-finite.json:
   its realized statement and step lists are empty, and no prescribed unit step
   is bypassed. Independently read Stacks Tag 012X's first-filtration formula and
   signed vertical differential; the cone refinement is correctly identified
   as the parent node's argument rather than a theorem quoted from Stacks.

5. Metadata: PASS. The existing node differs only in proof, proof_deps and
   proof_origin. Their steps track the actual Lean assembly, bounds, vanishing
   and homology-of-shift composition. Both new nodes have their source, full
   proof plan, dependency union, logged searches, split status, creation record,
   inherited blueprint route, chapter/unit and verbatim Lean signatures. The
   stability node also records its three concrete definitions. One original
   hole closes and one graded-comparison hole is added: net zero, with no claim
   that the original theorem is free of sorryAx.

Second-reading changes: clarified the removed old proof dependency in
No longer needed and added this independent review. No Lean repair or statement
change was required; the correct construction and reduction were preserved.
