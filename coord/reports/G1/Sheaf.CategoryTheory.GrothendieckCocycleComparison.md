## What changed

The unchanged theorem `CategoryTheory.grothendieck_cocycle_comparison` now has a complete
Lean proof combining two separate edge calculations. It applies the complex cocycle equation
to `K = F(I)` and rewrites the complex edge using the injective-resolution comparison.

Added `Sheaf.CategoryTheory.HypercohomologyLeftEdge`, whose three definitions and
first-quadrant instance are fully implemented. The complex edge is an explicit composite of
extension homology comparisons, the derived unit, the truncation spectral object's left edge,
and canonical truncation/shift/degree-zero target comparisons. No data is obtained from an
unproved existence theorem.

Added the two statement modules `Sheaf.CategoryTheory.HypercohomologyEdgeCocycle` and
`Sheaf.CategoryTheory.GrothendieckHypercohomologyEdge`. The first concerns a general complex
and its cycle quotient, without `F`, acyclicity, or any injective resolution of an object.
The second identifies maps on the whole homology object for a prescribed resolution, without
any supplied cycle lift or quotient equation. They isolate different parts of the existing
argument; neither restates the assigned theorem. The new statements have source references
and complete proof descriptions. The original declaration's signature and docstring are kept.

All four modules compile together using lcompile.py in import order, with no warnings.
The second reader replaced the definition module's broad public Grothendieck import with
the specific derived-category and spectral-object construction imports. Proof-plan imports
for the two open statements are plain imports, so they expose no additional public API.

## Proved and sorry left

Closed the sole original hole in `CategoryTheory.grothendieck_cocycle_comparison`
(node `lem-pc-grothendieck-cocycle-comparison`) by decomposition, not an unconditional proof.

Added exactly two named theorem holes:

- `CategoryTheory.Functor.cochainHypercohomologyLeftEdge_cocycle`
  (`lem-pc-hypercohomology-edge-cocycle`).
- `CategoryTheory.grothendieckLeftEdgeMap_eq_hypercohomology`
  (`lem-pc-grothendieck-hypercohomology-edge`).

No holes remain in the assigned module. The definition module has no holes.
Net change in direct holes for this delivery is +1 (one closed, two added).
The parent proof combines the statements by an actual Lean rewrite.

Edge cases checked: the general complex edge uses the derived unit, not its inverse, so it
requires no termwise G-acyclicity; natural indexing ensures the first quadrant needed by the
left edge; at n=0 there is no incoming boundary and the shift is zero. Zero complexes give
zero morphisms on both sides. The resolution comparison is an equality on all homology,
independent of any particular cycle lift. The existing canonical Grothendieck definition
uses exactly the same truncation, shift, and rightDerivedZeroIsoSelf factors as the new
complex edge target iso.

## No longer needed

Removed the assigned module's direct proof imports:

- `Sheaf.CategoryTheory.CartanEilenbergExists`.
- `Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel`.
- `WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck`.

The upstream Grothendieck definitions remain visible through the existing public statement
import `Sheaf.CategoryTheory.GrothendieckComposablePair`. The CE existence and double-complex
model remain needed below the resolution-comparison statement; they are not globally pruned.
Likewise the old definition dependencies `lem-sp-derived-well-defined`,
`def-sp-composite-acyclicity`, `def-sp-injective-resolutions`, `def-sp-left-exact-additive`,
and `lem-sp-grothendieck-edge-maps` remain needed by the new calculations or by statements.
None of these nodes is claimed globally unnecessary. The parent node's proof dependencies
are now exactly the two new calculation nodes. No unit statement or unit step is bypassed.

For completeness, all seven old parent proof dependencies have left its direct proof:
`lem-sp-cartan-eilenberg-exists`, `lem-pc-grothendieck-ss-double-complex-model`,
`lem-sp-derived-well-defined`, `def-sp-composite-acyclicity`, `def-sp-injective-resolutions`,
`def-sp-left-exact-additive`, and `lem-sp-grothendieck-edge-maps`. Their declarations are
still needed by the new statement plans or the unchanged signatures; none of their modules
is asserted globally pruned. Also removed the new definition module's broad
`WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck` import in favor of the
specific modules that supply its constructions. Globally pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The double-complex model specifies the augmentation, filtration, abstract edge and derived
identifications, but its theorem statement does not supply the representative calculation
asserted in step 3 of this item's plan. That calculation cannot be closed merely by applying
the model theorem. It is isolated in the general complex cocycle equation; the resolution
identification is kept separately. The old docstring remains a description of the overall
mathematical proof, while the updated DAG records the actual reduction in Lean.

The referenced local Stacks source is absent from this clone. Read the primary Stacks pages
https://stacks.math.columbia.edu/tag/015J and https://stacks.math.columbia.edu/tag/015N instead.
The tags supply the CE constructions and page computations; the precise edge equations are
expanded representative/comparison calculations, not quotations of those lemma statements.
LeanSearch returned HTTP 500 and is recorded as unavailable. Loogle, LeanFinder, library
ripgrep searches and blueprint searches found no existing matching equations.

## New nodes

`def-pc-hypercohomology-left-edge`: fully implemented canonical complex edge, in
`lean/Sheaf/CategoryTheory/HypercohomologyLeftEdge.lean`. It introduces no arbitrary witness,
axiom or postponed data construction.

`lem-pc-hypercohomology-edge-cocycle`: the general complex representative computation,
in `lean/Sheaf/CategoryTheory/HypercohomologyEdgeCocycle.lean`; one named theorem hole.

`lem-pc-grothendieck-hypercohomology-edge`: compatibility with the prescribed injective
resolution and canonical Grothendieck edge, in
`lean/Sheaf/CategoryTheory/GrothendieckHypercohomologyEdge.lean`; one named theorem hole.

No definition or statement was changed and no change record is required.

## Second reading by G1

1. Unchanged interface: compared the original module with the repository using `diff -u`.
   Only its three plain proof imports and the theorem body differed. The full signature,
   including the supplied cycle lift, its inclusion equation, all category assumptions,
   acyclicity assumption and canonical resolution comparisons, is byte for byte unchanged.
   Its existing docstrings are also unchanged. The other three modules are new. No existing
   definition or target statement changes, and no change record is needed. Verdict: pass.

2. Proof and data: compiled all four modules in import order using only `lcompile.py`.
   They compile without errors or warnings. Read every definition and the first-quadrant
   instance: the zero extension, homology comparisons, derived unit, truncation left edge
   and target isomorphism are explicit constructions. There is no choice of a witness from
   an unproved existence statement. The only two `sorry` tokens are the two named theorem
   bodies listed above. Scratch `#print axioms` probes for all three new definitions return
   only `propext`, `Classical.choice`, `Quot.sound`; both open theorems and the original
   theorem additionally return `sorryAx`. No forbidden declaration or implementation
   mechanism occurs. Verdict: pass as a decomposition, not an unconditional proof.

3. Split statements: read both signatures, docstrings and nodes against Stacks
   [015J](https://stacks.math.columbia.edu/tag/015J) and
   [015N](https://stacks.math.columbia.edu/tag/015N). The general-complex equation isolates
   the representative calculation, with no original object, functor F, resolution or
   termwise acyclicity. The other equation isolates the resolution comparison on all
   homology, with no cycle lift or quotient equation. Neither statement alone reproduces
   the original theorem; its proof combines both by rewriting the actual edge composite.
   Left exactness identifies cycles after G; the derived unit supplies the source map even
   for nonacyclic terms. Checked zero complexes, degree zero (no incoming boundary and no
   shift sign), a single complex in degree n (the edge is the degree-zero derived comparison),
   and exact G (the ordinary cohomology comparison). The resolution equation specializes
   correctly to an injective object resolved in degree zero. The Stacks sources support
   the two filtrations and their computations; the displayed edge identities are expanded
   arguments, not quoted Stacks statements. Fresh LeanFinder, Loogle and Mathlib grep searches
   used different wording (cohomology class, image of a left exact functor, homology quotient
   maps); source and library `rg` searches found no matching higher-degree equation.
   Existing `rightDerivedPlusSingleUnitHomology_comp_comparison` handles only the single
   complex in degree zero, not either general statement. No split hole was closed by a
   short existing lemma. Verdict: both are valid separate parts of the argument.

4. Route and pruning: the parent proof instantiates the general equation at F(I), obtains
   the independently stated resolution equation, rewrites, and returns the desired equality.
   Read the old seven proof dependencies and the new dependency plans; every old dependency
   is accounted for under `No longer needed`, distinguishing direct removal from global
   pruning. Read `dag/units/sk-thm-picard-rr.json`: its preexisting `realized` lists are empty;
   this delivery alters no unit record or unit step. The general truncation theorem from
   the proper-base-change unit is used only as a tool for the same hypercohomology
   construction, not as a replacement for the Picard unit's route. Verdict: pass.

5. DAG agreement: compared the existing node with the repository; only `proof`, `proof_deps`
   and `proof_origin` changed. Its new proof names exactly the two equations used by Lean.
   Read all three new nodes: their statements match the explicit edge construction and
   the two open equations, with source, proof plans, searches, creation, blueprint ancestry,
   chapter/unit and Lean records. Their named declarations match their modules. Verdict:
   pass after restoring the modules of the open statements' planned proof dependencies.

Changes made in this reading: added plain imports of `CartanEilenbergExists`,
`CartanEilenbergLeftExactCohomology` and `TruncationHypercohomology` to the general cocycle
statement module, and `CartanEilenbergExists` to the resolution statement module, matching
their recorded proof plans. Replaced the broad public Grothendieck import in the new edge
definition module with its specific construction imports. Completed the pruning inventory
and wrote this independent review. No theorem statement, definition body or proof body was
changed. Final direct accounting remains one original hole closed by decomposition, two
holes added, net +1; zero original theorems proved without `sorryAx`.
