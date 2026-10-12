## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero`,
`AlgebraicGeometry.Etale.integralFibreSection_localZero`, by a complete Lean assembly
of the strict-henselization argument. Its signature and existing docstring are unchanged.
The proof obtains the local structure on the strict henselization, uses a module-stalk
factorization and integral closed-fibre injectivity, cancels three injective maps, and
applies Mathlib's `GrothendieckTopology.Point.toPresheafFiber_eq_iff'` to the section
and zero. The returned pointed refinement has exactly the required map to the original V.

Added two modules, each with one public intermediate theorem and its DAG node:
`Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective` and
`Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization`. The first contains
only the strictly henselian integral global-section comparison, with no direct-image
stalk or neighbourhood refinement. The second contains only the qcqs stalk comparison
and compatibility of its restriction maps, with no integral hypothesis and no assertion
of injectivity along the fibre. Neither is the original local-zero statement renamed.
The main proof needs both, as well as the existing local-structure theorem.

Compilation: all three sandbox modules compile in import order through lcompile.py,
with no warnings. The main proof has no local or anonymous holes. No definition, existing
signature, public import, or target statement changed. No adaptations are required.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.integralFibreSection_localZero`
(node `lem-sbc-integral-fibre-section-local-zero`).

Added two named holes, both in new modules with full source/proof docstrings:

- `AlgebraicGeometry.Etale.strictHenselianIntegralSections_injective`
  (node `lem-sbc-strict-henselian-integral-sections-injective`).
- `AlgebraicGeometry.Etale.strictHenselizationModuleFibre_factorization`
  (node `lem-sbc-strict-henselization-module-fibre-factorization`).

This is a decomposition: one upper hole closed and two lower holes added, net minus one
before any subsequent proofs. It is not a sorry-free proof of the mathematical result.
There are no sorries left in the assigned module. The new modules preserve the existing
planned dependencies as proof imports; this delivery claims no closure reduction from
moving those dependencies.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization`
- `Sheaf.RingTheory.IntegralOverHenselianPair`
- `Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension`
- `Sheaf.AlgebraicGeometry.EtaleModuleSetPullbackComparison`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero`

These modules and their nodes remain needed by the two intermediate arguments, and
are imported there. No whole module or original planned node is pruned. Specifically, the old direct
`proof_deps` removed from the assigned node are
`lem-weil-pbc-sets-pushforward-stalk-strict-henselization`,
`lem-weil-pbc-integral-over-henselian-pair`, `lemma-weil-pbc-etale-degree-zero`,
`lem-weil-pbc-sections-base-field-extension`, and
`lem-sc-etale-module-set-pullback-comparison`. The first is retained through the
factorization node, the middle three through the injectivity node, and the last
through both. Thus these are removed direct dependencies, not pruned closure nodes. The original
public imports remain necessary for the unchanged signature. Affine refinement does
not require a separate lemma in the main module: the general comparison handles every
representative, and the point equality criterion refines the original V directly.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical steps fit, but their existing declarations do not expose the
assembled module-stalk comparison with its closed geometric lift and representative
formula, or the integral closed-fibre injectivity in the form needed here. The two new
nodes state precisely these missing intermediate interfaces. The original steps can
then be combined by a short actual Lean proof, including the filtered-colimit argument.

Searches were run with msearch.py: LeanSearch was unavailable (Internal Server Error),
LeanFinder returned structure-sheaf and tilde-module lemmas rather than etale sheaf
comparisons, and Mathlib grep found neither missing interface. The source library's
`WeilConjectures.SixFunctors.Integral.BaseChange` has a higher integral exchange theorem,
but import_direction.py confirms that importing it closes a cycle through this item.
It cannot supply a shorter proof here.

The local `literature/stacks-project/etale-cohomology.tex` named by the existing node
is absent on this machine. Checked the official Stacks pages instead:
[03Q9](https://stacks.math.columbia.edu/tag/03Q9) for the qcqs strict-henselization stalk
comparison, [09ZH](https://stacks.math.columbia.edu/tag/09ZH) for henselian affine
sections, and [0A3I](https://stacks.math.columbia.edu/tag/0A3I) for sections under
extension of a separably closed field. The original docstring's henselian route is a
valid alternative consequence of these results; the actual proof of
[0EYP](https://stacks.math.columbia.edu/tag/0EYP) uses finite approximation instead.
No unit step is bypassed: `sk-lem-universal-datum.realized` has no realization at this
local node, and the integral exchange statement above the item stays unchanged.

Edge cases: empty X or fibre uses the same section and colimit argument; the henselian
pair comparison allows the zero algebra; non-affine V is included in the representative
formula; no torsion or finite-type hypothesis is added; an arbitrary algebraically
closed extension Omega is allowed through 0A3I, not only an algebraic closure.
The existential comparisons are used only in the theorem proof. No data definition
is built by choosing a witness from an unproved existence theorem.

## New nodes

`lem-sbc-strict-henselian-integral-sections-injective` lives in
`dag/nodes/sec-smooth-base-change/` and records the strictly henselian integral
section injection. Its proof uses the existing integral henselian-pair theorem,
degree-zero henselian comparison, base-field-extension sections and module/set unit
comparison, with the existing global-section composition formula.

`lem-sbc-strict-henselization-module-fibre-factorization` lives in the same chapter
and records the qcqs module stalk factorization, separately from fibre injectivity.
Its proof uses the existing set stalk comparison, module/set comparison, strict
henselization limit and structural map, closed-fibre characterization, and composition
formula. The assigned node's proof and proof_deps now follow the Lean assembly.

No change records: no existing interface was changed.


## Second reading by R2

1. **Interfaces: PASS.** Compared every delivered module with the repository.
   Only the assigned module existed there: its theorem signature and existing
   docstring are byte for byte unchanged; its two public imports are unchanged.
   The other two modules introduce precisely the reported intermediate theorems.
   No definition, target, instance, attribute, or file-level option was changed.
   No change record or forced adaptation is needed.

2. **Proof and axioms: PASS as a decomposition.** All three modules compiled in
   import order through lcompile.py without warnings. Independently appended
   `#print axioms` in temporary copies and compiled each: all three declarations
   use only propext, Classical.choice, Quot.sound and the expected sorryAx.
   Removed the temporary copies. Inspected the actual cancellation proof and
   the pointed-refinement equality criterion, including preservation of zero.
   Exactly the two reported public intermediate theorems have sorry; there are
   no hidden holes, new data definitions, or forbidden declarations.

3. **Split statements: PASS.** Read their full types, docstrings and nodes, and
   the existing dependencies' declarations. The first is closed-fibre section
   injectivity over an integral algebra of a strictly henselian local ring;
   the second is qcqs stalk continuity and restriction compatibility without
   integral injectivity. Each is a strictly separate part of the argument,
   rather than the original local-zero statement under a new name. Checked
   empty schemes/zero algebras, non-finite integral algebras, non-affine V,
   arbitrary coefficient rings and transcendental Omega. The ring and scheme
   data already have constructions; existential witnesses occur only in proofs.
   Independently checked [09XK](https://stacks.math.columbia.edu/tag/09XK),
   [09ZH](https://stacks.math.columbia.edu/tag/09ZH),
   [0A3I](https://stacks.math.columbia.edu/tag/0A3I), and
   [03Q9](https://stacks.math.columbia.edu/tag/03Q9).
   Repeated searches with different terminology: LeanFinder for henselian-pair
   restriction of etale sections, Loogle for sheafFiber, Mathlib grep for fibre
   colimit/isomorphism and henselian sheaf comparisons, and rg over both library
   roots. No existing exact replacement was found. Inspected the nearby Zariski
   stalk-section comparisons and strict-henselization restriction construction:
   neither supplies the displayed module comparison and fibre formula. Proper
   exchange requires properness, which an integral morphism need not satisfy;
   integral exchange imports this item. Neither lower hole can be closed by a
   short application of those results.

4. **Route and pruning: PASS.** The main proof uses Mathlib directly for the
   final germ equality criterion. Public imports support the signatures;
   assembly-only imports are plain imports. The lower modules retain the
   dependencies of their stated unresolved arguments. Explicitly listed every
   removed old direct proof dependency under No longer needed; all remain in
   the closure, so no module is claimed pruned. Read
   dag/units/sk-lem-universal-datum.json: its realized lists are empty, and this
   local decomposition does not replace any unit step or alter the integral
   exchange route above it. One original hole is closed and two lower holes
   added, net minus one: this remains a decomposition, not a completed result.

5. **DAG: PASS.** The assigned node's three steps describe the actual Lean
   assembly and use exactly its three direct proof dependencies. The two new
   nodes include source, proof text, search records, creation and blueprint
   records, chapter/unit and the matching Lean declaration/signature. All
   cited nodes exist; each proof_deps list is exactly the union of step uses.
   The new-node proof plans and proof_origin agree with their docstrings.

Second-reading changes: report only. Added the explicit removed-dependency list
and this independent review. Kept the correct Lean proofs, statements, imports
and nodes unchanged; no additional hole was closed or added.
