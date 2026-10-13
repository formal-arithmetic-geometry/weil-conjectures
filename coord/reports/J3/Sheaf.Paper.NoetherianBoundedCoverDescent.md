## What changed

Proved `Algebra.exists_finiteType_model_of_bounded_principal_cover` in
`Sheaf.Paper.NoetherianBoundedCoverDescent` with its original signature and docstring.
Two proved private helpers carry the localized fibre comparison and the dimension bound
from a principal-open cover. All new imports of the assigned module are proof-only.

Added `Sheaf.Paper.NoetherianPrincipalCoverModel` with the proved theorem
`Algebra.exists_finiteType_principal_cover_model`. This constructs the coefficient ring
as an algebra adjoin of a finite set of coefficients from a unit-ideal certificate.
It does not assume or conclude a dimension bound.

Updated the item's proof plan and dependencies to match the Lean argument. Added a node
for the coefficient-cover theorem and a node attaching the existing source-library theorem
`topologicalKrullDim_le_of_iSup_eq_top`. No existing definitions, public signatures,
public imports, or target statements changed; no forced adaptations or change records.

## Proved and sorry left

Closed the one original hole:
`Algebra.exists_finiteType_model_of_bounded_principal_cover`
(node `lem-weil-pbc-noetherian-bounded-principal-cover-descent`).

Also proved `Algebra.exists_finiteType_principal_cover_model`
(node `lem-weil-pbc-noetherian-principal-cover-model`). The two private helpers
`Algebra.dimension_le_of_fibre_principal_cover` and
`Algebra.localized_model_fibre_dimension` are fully proved.

Holes closed: 1. Holes added: 0. No `sorry` remains in either delivered module.
No decomposition into new unproved statements. The proof uses the existing field-extension
dimension theorem. The second reading's axiom checks show only the three permitted axioms
for the theorem, both private helpers, and the new cover theorem, including their dependencies.

Both modules compile with the launcher, without warnings. Empty cover, zero quotient,
zero localized fibres, empty equation family and zero variables are handled without
any nonemptiness assumption being added.

## No longer needed

No original imports were removed: they are public imports supporting the statement.
The second reading removed redundant proof imports `Mathlib.RingTheory.TensorProduct.Maps`
from the item and `Mathlib.RingTheory.Ideal.Operations` and
`Mathlib.RingTheory.Adjoin.Basic` from the new module. In the new module, the proof-only
`Mathlib.RingTheory.Spectrum.Prime.Topology` import is now plain, with the statement
importing `Mathlib.RingTheory.Spectrum.Prime.Defs` publicly.
The old plan's following direct dependencies are no longer needed here:

- `lem-weil-pbc-dimension-at-point-open-subspace`: the proof uses the already proved
  generic open-cover bound rather than a new pointwise argument. Its module
  `WeilConjectures.Mathlib.Topology.KrullDimension` remains, because it supplies that bound.
- `lem-weil-pbc-dimension-supremum-local-dimensions` / the direct proof import of
  `Sheaf.Topology.DimensionSupremumLocalDimensions`: unnecessary for the final cover step.
  The module still occurs transitively through the existing field-extension theorem;
  this delivery does not claim it leaves the targets' import closure.
- `lem-weil-pbc-prime-in-image-iff-fibre-ring-nonzero`: the elementary spectrum
  nonempty/nontrivial equivalence and contraction along includeRight suffice. No dedicated
  proof module for this node is imported.
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` moves out of the item's direct
  proof dependencies into the new coefficient-construction node; its Mathlib cover
  criterion remains used there.
- `def-weil-pbc-finite-type-algebra` and `def-weil-pbc-mv-polynomial-ring` move out of
  the item's direct proof dependencies into the new coefficient-construction node.
  They remain statement dependencies and are not pruned from the library.

No whole existing module is claimed to leave the import closure. Polynomial and quotient
scalar extension, tensor cancellation, localization base change, field-extension dimension
invariance, and the localization/basic-open identification are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The final two pointwise-topology steps of the DAG
have a shorter existing source-library route: `topologicalKrullDim_le_of_iSup_eq_top`.
The finite-cover construction can adjoin the multiplier coefficients directly over R₀;
there is no need to choose a new set of integer generators for R₀.
The unit's statement and realized steps remain unchanged.

LeanSearch was attempted and returned Internal Server Error; LeanFinder/Loogle and source
searches were used. The local literature copies are absent on this machine. WANTED:
`literature/stacks-project/algebra.tex`, Tag 00SU final paragraph, and
`literature/stacks-project/topology.tex`, Tag 0B7I proof. Both official Stacks pages were
read online, and the proof-origin records identify the worker's formal realization.

## New nodes

`lem-weil-pbc-noetherian-principal-cover-model` records the fully proved coefficient-ring
construction in `Sheaf.Paper.NoetherianPrincipalCoverModel`. Its statement is strictly the
cover-descending part of the original argument and adds no holes.

`lem-weil-pbc-dimension-bound-open-cover` attaches the already proved generic theorem
`topologicalKrullDim_le_of_iSup_eq_top` in
`WeilConjectures.Mathlib.Topology.KrullDimension`. It introduces no Lean file or hole.

## Second reading by J3

1. Interface: PASS. Compared the complete item with the repository by `diff` and checked
   the existing theorem signature and docstring byte for byte. Only its proof, private
   proved helpers, local elaboration options, and plain imports were added. No existing
   definition, public import, visibility, or target statement changed. The other module
   and two nodes are new and are explicitly declared in this report.
2. Proof: PASS. Both modules compile without warnings using `lcompile.py`. There is no
   `sorry`, axiom declaration, unsafe/opaque implementation, extern, or hollow definition.
   Scratch copies with `#print axioms` checked all four theorems, including both private
   helpers: each uses only `propext`, `Classical.choice`, and `Quot.sound`, with no
   `sorryAx`. The subring is explicitly `Algebra.adjoin R₀ C`; every chosen polynomial
   lift comes from a proved surjectivity/range theorem, and injectivity determines it.
3. New statements: PASS. There are no split-off holes. The new cover theorem is strictly
   the coefficient-construction part and does not restate the dimension conclusion.
   Reviewed the finite unit-ideal certificate, quotient lifts, finite adjoin, injective
   polynomial transport, and prime-properness contradiction. Empty indices give the
   empty sum and 1 in the equation ideal; zero quotients, empty equation families, and
   zero variables require no extra assumptions. The attached open-cover theorem's exact
   generic quasi-sober T₀ statement is already proved upstream. Independent LeanFinder
   search for retaining a unit-ideal certificate over an enlarged coefficient subring,
   Loogle search `PrimeSpectrum, topologicalKrullDim`, and searches of the project and
   Mathlib smooth descent found no shorter matching coefficient theorem. The smooth
   descent results require additional hypotheses; the spectrum/ring dimension equality
   does not replace the finite-coefficient construction.
4. Route and pruning: PASS after cleanup. Read Stacks Tags 00SU and 0B7I online and
   checked the subring enlargement and dimension-cover argument against them. The proof
   retains polynomial/quotient base change, localization, residue-field scalar extension,
   and field-extension dimension invariance, then uses the already proved generic
   open-cover bound. Read `dag/units/sk-thm-p1.json`: the item lies below its realized
   nodes, and no statement or step of that unit is bypassed or changed. Completed the
   old-dependency list with the unit-ideal certificate node moved into the construction
   node. Removed three redundant proof imports and made the new module's topology
   import proof-only. Removing localization-away finite-type or finite-stability imports
   failed instance synthesis, so those required imports remain.
5. Nodes: PASS after clarification. Checked every proof step, the union of `uses` against
   `proof_deps`, the unchanged original node statement, the verbatim Lean records, sources,
   provenance, searches, blueprint ancestry, chapter, unit, and creation fields. The two
   new nodes add no holes. Clarified the attached open-cover node's proof and provenance
   to describe the actual specialization-order/coheight proof in the existing module,
   rather than only its equivalent chain argument.

Changes by the second reader: three redundant proof imports removed; new module's
proof-only topology import demoted; missing moved dependency added to the pruning report;
axiom status corrected to the verified absence of `sorryAx`; attached open-cover node's
proof record clarified. The Lean proof bodies were left unchanged.
