## What changed

Completed and checked the earlier sandbox attempt. The existing public signature and
original docstring of `AlgebraicGeometry.schemeOpenModuleImage_pullback_exists` are
unchanged. Its proof now builds the sheaf morphism sectionwise. The private
`unit_sections_injective` proves separatedness using Mathlib's two-open sheaf
uniqueness theorem. The private `section_amalgamation` uses the Bool-indexed gluing
axiom and comparison isomorphisms. The final proof verifies addition, scalar
multiplication, naturality, and both requested composites.

Added the proof import `Sheaf.AlgebraicGeometry.OpenModuleImageSectionRestriction`,
a new module for the one unresolved calculation, with one public named theorem.
The second reader removed the redundant proof import
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`; its declarations are
already available through the existing public data import.
Updated the target node's proof, proof dependencies, and proof origin to describe
this actual reduction. Added the new helper's complete DAG node.

The section chosen by `hex.choose` is uniquely determined: two witnesses have
equal unit images and `unit_sections_injective` proves equality. This choice is
not arbitrary data obtained from an unproved mere-existence assertion.

## Proved and sorry left

Closed the existing hole in
`AlgebraicGeometry.schemeOpenModuleImage_pullback_exists`
(node `lem-pc-open-module-image-gluing-existence`). Neither private helper has a
hole. Added one hole, the entire proof of the public theorem
`AlgebraicGeometry.schemeOpenModuleImage_section_restriction`
(node `lem-pc-open-module-image-section-restriction`). No other holes are added.

This is a decomposition, not a net sorry reduction: one upper hole closed and
one strictly narrower map-calculation hole added. The new statement asserts
only the sectionwise formula for a nested-open restriction, without a cover,
compatible pair, amalgamation, or morphism-existence conclusion.

Both modules compile through `lcompile.py --all`. The target proof uses no local
partial `sorry`, no changed statement, and no hollow definition. The pending
helper has a source and a complete proof in words. The dry run checks axioms
and the remaining named holes.

## No longer needed

No original module import is removed and no library module is pruned. The added
`Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing` import was redundant and
is removed. The old direct proof dependency
`def-pc-derived-open-restriction-maps` is no longer directly used by the target
proof: the new helper carries this map-calculation dependency, so its module
remains in the import closure. The original public data import is required by
the unchanged statement and supplies the gluing and separatedness declarations
transitively. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous attempt had working Lean for the reduction, but no helper node,
updated target node, or report, so it was not reviewable or ready to deliver.
Those missing records are supplied here. No mathematical error in the original
statement or source was found. The empty scheme, empty test open, empty covering
member, repeated opens, and equal nested opens are allowed: the gluing proof
uses the same Bool-indexed cover and makes no nonemptiness assumption.

The local copy does not contain `literature/stacks-project/cohomology.tex`.
The cited source was read at the official Stacks pages
https://stacks.math.columbia.edu/tag/01EB and
https://stacks.math.columbia.edu/tag/08BV. Tag 01EB's first proof sentence
supplies the ordinary sheaf gluing argument; Tag 08BV displays the sectionwise
sequence whose concrete maps are being calculated.

LeanFinder, Loogle, and source grep found the ordinary restriction unit/counit,
`overFunctorEquiv`, and `overFunctorMap`, but no theorem about this transported
mate. LeanSearch returned Internal Server Error and is recorded as unavailable.
The blueprint and repository searches found no duplicate statement.

A direct calculation of the remaining mate was explored in
`scratchpad/Restriction.lean`: unfolding its adjunction and composition
comparison compiles, but the remaining transported equivalence components
were not closed. That scratch file is not part of the delivery. The original
`scratchpad/Probe.lean` experiment timed out; the delivered modules themselves
compile well inside the limit and no time-limit workaround was used.

## New nodes

`lem-pc-open-module-image-section-restriction`, in
`dag/nodes/sec-picard-framework/`, states the identification of the transported
nested-open map with ordinary restriction on sections. Its source is Tag 08BV,
with the concrete definition in KInjectiveMayerVietorisData. The statement is
strictly a map-identification step of the argument; it cannot by itself imply
an amalgamation. Its proof expands the mate, cancels the comparison and
open-site equivalence components, evaluates ordinary unit/counit maps, and
combines restrictions by functoriality. It inherits the target's chapter,
unit, and blueprint ancestor. Its module is
`Sheaf.AlgebraicGeometry.OpenModuleImageSectionRestriction`. No change record
is needed: no existing signature, definition, or public import is changed.

## Second reading by U4

1. Compared both delivered Lean modules against the repository. The sole existing
   public theorem's signature is byte for byte unchanged, as is its docstring.
   No existing definition, public import, or other module is changed. The new
   helper has its own module and node. Verdict: pass; no change record required.
2. Compiled both modules locally in import order (5.9 s and 24.7 s). Read the
   separatedness, Bool-cover gluing, linearity, naturality and composite proofs.
   The target has no sorry; only the reported public helper has one, as its entire
   proof. There are no forbidden declarations or hollow definitions. Explicit
   `#print axioms` in a temporary scratch module gave exactly propext,
   Classical.choice, Quot.sound and sorryAx for both public theorems. Choice of
   amalgamation is permitted because the proved two-unit injectivity determines
   each chosen section uniquely, including in the presence of the pending map
   formula. Verdict: pass as a decomposition, not a completed axiom-free proof.
3. Read the new formula against the concrete adjunction, composition comparison,
   overFunctorEquiv and the ordinary restriction unit/counit definitions. The
   source [Tag 08BV](https://stacks.math.columbia.edu/tag/08BV) gives the sectionwise
   maps; [Tag 01EB](https://stacks.math.columbia.edu/tag/01EB) supplies the sheaf
   kernel/gluing argument. The formula requires neither cover nor amalgamation
   and is strictly narrower than the item. For W=U it is identity after comparison;
   W empty, T empty, or X empty use the zero module of empty sections. No
   nonemptiness or injectivity of M is used. Its docstring gives the cancellation
   and functoriality argument, and its node matches the signature. Fresh
   LeanFinder, Loogle and grep searches using counit/mate terminology found the
   ordinary unit/counit components and comparison isomorphisms, but no replacement
   for this transported map calculation. Searched lean/Sheaf and lean/WeilConjectures
   for transported maps and generic open-cover mate results; none proves this
   formula directly. No few-minute completion was found. Verdict: pass.
4. The proof uses Mathlib gluing and separatedness directly, with only the
   transported restriction calculation deferred. All existing public imports
   are needed by the unchanged signature. A scratch compile without the added
   UniqueGluing import succeeded (22.2 s), so I removed that redundant import.
   Corrected No longer needed to list the old direct dependency moved to the
   helper. No module leaves the closure. Read sk-thm-picard-duality.json and its
   realized field: this item is not a realized unit statement or step and the
   existing derived Mayer-Vietoris route remains intact. Verdict: pass.
5. Compared the old and delivered target node: only proof, proof_deps and
   proof_origin change. Their steps describe the actual injectivity, gluing,
   and morphism assembly, and proof_deps is their uses union. Checked the new
   node's source, searches, creation record, blueprint ancestry, chapter/unit,
   Lean record and full statement against its file. Its dependencies supply
   exactly the two concrete constructions used by its calculation. Verdict: pass.

Changes by the second reader: removed one redundant proof import and corrected
its report and the dependency-pruning account. No proof, existing statement,
definition, or node statement was changed. One original hole is closed, one new
named hole remains, and the net hole reduction is zero.
