## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.exists_eventually_isFlatOver_of_limit` by a complete Lean proof
from the existing affine module descent theorem and a new affine comparison theorem.
The original theorem signature, universes, visibility and docstring are unchanged.
Added the proof-only import
`Sheaf.AlgebraicGeometry.FlatModuleDescentAffineCharts`; retained the existing
`Sheaf.AlgebraicGeometry.AffineFlatModuleDescent` import because the proof applies
`AlgebraicGeometry.exists_eventually_flat_of_finitePresentation` directly.

The new module states one intermediate theorem:
`AlgebraicGeometry.exists_flat_module_descent_affine_charts`. It extracts finite
rings and section modules, identifies their limit tensor flatness, and states the
stage gluing implication. It contains no eventual-stage existence assertion and
uses no affine descent theorem. The main proof supplies that missing argument:
apply affine descent to each chart with A_i = R_i, then induct on finite sets to
construct a common upper bound. The empty family uses i as its bound. At every
later stage apply all chart conclusions and the gluing implication.

The tensor types explicitly install the module structure induced by the right
algebra on T tensor_{R_i} R_i. This makes the affine theorem specialize without
confusing its right-factor action with Lean's default tensor module instance.
All actions are those of the canonical scalar extension, and the new theorem's
proof in words explains the tensor-unit identification. Existential chart data is
used only inside a theorem proof, never chosen into a definition.

Updated the item's DAG proof and proof dependencies to match the compiled proof.
Added the new comparison node with its complete proof in words and searches.
No existing statement or definition is changed; no forced adaptations or change
records are needed. The unit record has no realized nodes for this item, and the
Tag 05LY route (finite affine reduction, affine descent, common bound, gluing) is
preserved.

Validation: both sandbox modules compile without errors or warnings through
lcompile.py. The final delivery dry run checks the declaration probes and
preflight. No library build, manual git operation, or push was performed.

## Proved and sorry left

Closed the hole in `AlgebraicGeometry.exists_eventually_isFlatOver_of_limit`
(node `lem-pc-flat-module-descent`). Its proof is complete, but depends on the
existing affine descent theorem and the new comparison theorem.

Added one hole:
`AlgebraicGeometry.exists_flat_module_descent_affine_charts`
(node `lem-pc-flat-module-descent-affine-charts`), in the new module
`Sheaf.AlgebraicGeometry.FlatModuleDescentAffineCharts`. Its entire proof is
`:= by sorry`; its docstring and node give the finite-cover, tensor-comparison,
and source-local gluing argument. There are no remaining holes in the item's
module, no partial proof holes, and no data definitions with holes.

This is a decomposition: one upper hole closed and one strictly smaller
comparison hole added, net zero new-hole reduction. The already stated
`AlgebraicGeometry.exists_eventually_flat_of_finitePresentation`
(node `lem-pc-affine-flat-module-descent`) remains an existing dependency with
its own hole, unchanged and not counted as a hole added by this delivery.

Edge cases checked mathematically: an empty source uses n = 0 and vacuous gluing;
an empty chart family uses i rather than assuming Fin(n) is inhabited; zero
rings and zero chart modules respect the tensor-unit isomorphism. The proof
requires no least upper bound, linear order, or additional nonemptiness of I.
The original Noetherian assumptions are retained, although this affine-local
comparison does not need them.

## No longer needed

None. No original import, node or module is pruned. The finite-affine-cover,
local finite-presentation and finitely-presented-section ingredients are still
needed by the new comparison node; they have moved from the main theorem's
immediate proof dependencies to the comparison's dependencies. The original
scheme and base-change definitions remain statement dependencies. The affine
module descent theorem is directly used by the main proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original plan's scheme-to-ring
comparison and source-local gluing were prose steps, with no declaration
combining the required module comparisons. Existing FlatDescentAffineCharts
concerns flat scheme morphisms and cannot replace the module comparison.
ModulePullbackAffineSections supplies the affine sections formula but not the
finite-family extraction and relative-flatness gluing. These portions are
isolated in the new comparison theorem rather than silently assumed.

LeanSearch was unavailable (HTTP Internal Server Error), including a retry.
LeanFinder, Loogle, source grep and the blueprint search were performed and
recorded. The local Stacks TeX files are absent on this machine; the cited
statements and proofs were checked on their official online pages:
[05LY](https://stacks.math.columbia.edu/tag/05LY),
[01PC](https://stacks.math.columbia.edu/tag/01PC), and
[01U4](https://stacks.math.columbia.edu/tag/01U4).

## New nodes

`lem-pc-flat-module-descent-affine-charts`, at
`dag/nodes/sec-picard-framework/lem-pc-flat-module-descent-affine-charts.json`,
records `AlgebraicGeometry.exists_flat_module_descent_affine_charts` in
`lean/Sheaf/AlgebraicGeometry/FlatModuleDescentAffineCharts.lean`. This is strictly
the affine-comparison portion of the original argument: it gives finite section
modules and a stage gluing implication, but no eventual flatness. Its proof
follows the affine reduction in Stacks 05LY with finite-presentation sections
from 01PC and local relative flatness from 01U4. It inherits the original
chapter, unit and blueprint ancestor. No change records were created.

## Second reading by C2

1. Compared the delivered FlatModuleDescent.lean with the repository file using
   diff. Its sole existing declaration,
   AlgebraicGeometry.exists_eventually_isFlatOver_of_limit, retains its signature,
   universes, visibility and docstring byte for byte. The only Lean changes are
   its proof and one ordinary proof-only import. There are no changed definitions
   or change records. Verdict: pass.

2. Compiled both modules together through lcompile.py in import order: clean,
   approximately six seconds each. Separate scratch-copy #print axioms probes
   for both declarations returned propext, Classical.choice, Quot.sound and
   sorryAx only. The latter is expected: the new comparison theorem and the
   pre-existing affine descent theorem remain open. Source scans found exactly
   one sorry, the named comparison theorem with its whole proof postponed, and
   no forbidden declarations or holed definitions. Removed the scratch probes
   after checking. Verdict: pass as a decomposition, not a completed proof.

3. Read the new comparison statement, its docstring, and every cited node's
   statement and Lean/Mathlib attachment. Read Stacks [05LY](https://stacks.math.columbia.edu/tag/05LY),
   [01PC](https://stacks.math.columbia.edu/tag/01PC), and
   [01U4](https://stacks.math.columbia.edu/tag/01U4). Quasi-compactness gives a
   finite cover; local finite presentation gives its finitely presented rings;
   finite presentation and quasi-coherence give the section modules. The affine
   limit comparison is applicable: the fixed i supplies nonemptiness of I, and
   the stages and all transitions are affine. The natural Gamma-Spec
   isomorphisms identify the colimit ring and its coprojections with those in
   the statement. The affine pullback sections theorem supplies the tensor
   comparison, including linearity for the chart ring. The tensor-unit maps
   t tensor r maps to t times the image of r, and t maps to t tensor 1, respect
   the explicitly installed right R_i action. Under these identifications
   limit IsFlatOver gives the required C-flatness. For gluing, localization
   gives relative stalk flatness; the cited prime-local module criterion
   recovers sections flatness on every arbitrary affine test pair, precisely
   the IsFlatOver definition. No descent assertion is hidden in this lemma.
   It is strictly the geometric comparison part of 05LY; the main theorem
   separately applies affine descent and proves the common-bound argument.
   Checked an empty source (n=0), a singleton directed set, zero rings and
   zero modules: no excluded case or extra nonemptiness assumption.
   Independent LeanFinder search for quasicoherent relative flatness on an
   affine cover returned scheme-morphism flatness lemmas, not this module
   comparison. Loogle Module.Flat, TensorProduct returned tensor-flatness
   lemmas, not this comparison. msearch grep returned no match. Also searched
   lean/Sheaf, lean/WeilConjectures, upstream Modules/FiniteDescent. The raw blueprint directory is absent
   locally; searched its imported records with blueprint_refs.py using
   flat module and affine flat. The former returned only
   lem-pc-rf-base-change-flat-module (derived direct-image base change,
   not this chart comparison); the latter returned none. ModulePullbackAffineSections
   provides one affine pullback comparison but not finite-family extraction
   or gluing; FlatDescentAffineCharts is about scheme morphisms. No existing
   replacement was found. Closing the comparison in a few minutes would
   require formalizing these geometric transports, so its named hole remains.
   Verdict: true, needed, strictly smaller; no relabelled eventual-flatness hole.

4. Read the main proof top down. It specializes the existing affine theorem
   with A_i=R_i and B_i=B_b, supplying both finite-presentation instances and
   exactly the right-algebra tensor flatness hypothesis. Its induction on a
   finite set takes i for the empty set and a directed upper bound at insertion;
   applying this to Finset.univ proves the conclusion at every later stage.
   Different proofs of i<=k are identified by proof irrelevance. The added
   import is ordinary, and both proof imports are used directly. The new
   module's public imports expose only ingredients of its statement; there
   is no proof-only public import. The old finite-cover and local-presentation
   proof dependencies are still needed by the comparison, so No longer needed
   correctly says none. Read dag/units/sk-thm-picard-semicon.json: realized has
   no node for this item; the 05LY finite-affine/affine-descent/gluing route
   remains intact. Verdict: pass, no shorter complete route found.

5. Compared the original and delivered item node as JSON: only proof,
   proof_deps and proof_origin differ. Its new proof_deps are exactly the two
   results applied by the Lean proof. Checked the new node's source, complete
   proof steps, union of proof dependencies, chapter/unit, blueprint ancestor,
   created record and verbatim Lean statement. Its geometric steps use the
   finite cover, affine finite-presentation sections, affine-limit comparison,
   fibre-product spectra and pullback sections declarations actually recorded
   in the cited nodes; the tensor-unit computation is elementary. The
   prime-local gluing step uses the module localization criterion, not the
   scheme-morphism flatness theorem. Verdict: pass after metadata repairs.

Changes by this second reader: converted the new node's mathematical statement
from plain-text notation to TeX without changing its meaning, and explicitly
marked the failed LeanSearch service verdict unavailable. No Lean proof or
statement was changed. This delivery closes one upper hole and adds one lower
comparison hole, net zero: a decomposition.
