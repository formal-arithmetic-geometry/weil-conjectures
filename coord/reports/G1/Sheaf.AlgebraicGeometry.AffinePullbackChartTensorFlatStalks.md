## What changed

Proved `AlgebraicGeometry.affine_pullback_chart_tensor_flat_iff_stalks` with its original
signature and public imports unchanged. Added two fully proved supporting modules:
`Sheaf.AlgebraicGeometry.AffinePullbackChartTensorSections` constructs the actual inverse-image
chart and its scalar-compatible tensor sections equivalence; `Sheaf.AlgebraicGeometry.AffineChartRelativeFlatCriterion`
proves the relative flatness criterion on an arbitrary single affine chart over an affine base.
The target combines these by linear-equivalence transport, localization along the base global
sections isomorphism, and rewriting chart membership. All three files compile without warnings.

The section comparison uses the existing proved affine pullback sections theorem, Mathlib's
pushout of affine section rings, and `Algebra.IsPushout.cancelBaseChange`. The criterion uses
the proved stalk tensor presentation and localization-preserves-flatness theorem, and Mathlib's
relative maximal-localization criterion. Quasi-coherence of tensor pullback is transported from
ordinary pullback by uniqueness of left adjoints. No definition or existing statement changed.
The two new nodes and the item's route record the actual proof. Sources checked: Stacks Tags
01U4, 00HT, 01IA, 01I4; the existing section comparison supplies Tag 01HV.

## Proved and sorry left

Closed the single original hole in `AlgebraicGeometry.affine_pullback_chart_tensor_flat_iff_stalks`
(node `lem-pc-affine-pullback-chart-tensor-flat-stalks`). Added no holes.
Both `AlgebraicGeometry.exists_affine_pullback_chart_tensor_sections`
(node `lem-pc-affine-pullback-chart-tensor-sections`) and
`AlgebraicGeometry.affine_chart_relative_flat_iff`
(node `lem-pc-affine-chart-relative-flat-criterion`) are completely proved.
There is no `sorry` in any of the three delivered Lean modules. Existing dependencies may
still rest on the project's earlier proof obligations; no claim of closing those is made.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` and
`Sheaf.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation` from the target module.
They are used in the two new helper modules and remain transitive dependencies. The old direct proof dependencies now reached through helpers are
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-pc-intrinsic-flat-module-stalk-tensor-presentation`,
`lem-pc-affine-sections-flat-over-base`, and
`lem-weil-pbc-fibre-product-affine-spectra`. The first two remain transitive module imports;
the latter two are Mathlib ingredients. The affine-spectrum formula is used in its equivalent
pushout-of-sections form (`isIso_pushoutSection_of_isAffineOpen` and
`isIso_pushoutSection_iff`), rather than by applying `pullbackSpecIso`. No whole module or node is pruned from the target closure.
No imports in the new modules are unused by their statements or proofs.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The plan's stalk and section comparisons did not directly expose
the exact combined interface, but its ingredients suffice without introducing any new hole.
The generic chart criterion needed an explicit scalar-tower verification using germ-stalkMap
compatibility; it is written in both directions. Mathlib's affine section-ring pushout interface
avoids constructing and transporting a separate scheme isomorphism to Spec(B tensor_A T).
The unit record has no realized statement or steps on this node, and the proof keeps the
original affine-local route. Empty charts, zero modules and zero base rings are included:
no proof step assumes a point or a nonzero ring; maximal-ideal quantification handles an empty
spectrum. The pullback quasi-coherence theorem is used as an existing general tool, without
changing the unit route. LeanSearch was unavailable; Loogle, LeanFinder and source searches
were run and recorded in the new nodes.

## New nodes

`lem-pc-affine-pullback-chart-tensor-sections`, in
`lean/Sheaf/AlgebraicGeometry/AffinePullbackChartTensorSections.lean`, is the fully proved,
flatness-independent section comparison for the actual inverse-image chart. Its statement
fixes the scalar action through the second projection and the given base isomorphism.

`lem-pc-affine-chart-relative-flat-criterion`, in
`lean/Sheaf/AlgebraicGeometry/AffineChartRelativeFlatCriterion.lean`, is the fully proved
single-chart relative localization criterion. It applies to any quasi-coherent module and
morphism to an affine base, independently of tensor products and base-change squares.

No change record is needed: no existing interface changed.

## Second reading by G1

1. Compared the delivered target module with the repository using diff and independently
   compared its theorem signature byte for byte: identical. Only proof imports and the proof
   changed. The other two modules are new, fully proved theorem modules. No existing definition,
   statement, public import, or visibility changed; no change record is required. Verdict: pass.
2. Compiled all three files in dependency order using lcompile.py: no errors or warnings.
   Searched each delivered module for sorry and forbidden declarations: none. A temporary
   scratch axiom probe printed axioms of all three named theorems; each has exactly propext,
   Classical.choice and Quot.sound, with no sorryAx. Reviewed the local choices of equivalences:
   they are inside proofs and come from proved comparisons; W is constructed explicitly.
   Verdict: pass, one original hole closed and no holes added.
3. No statement with sorry was split off. Read both new helper statements and proofs in full.
   The section comparison fixes the actual inverse-image open and exact T-action; the chart
   criterion concerns one chart only and does not assume flatness elsewhere. Checked empty
   charts, zero modules, and zero rings: the proofs use no nonemptiness assumption and the
   maximal-localization criterion includes the empty spectrum. Independent LeanFinder search
   for relative flatness detected by maximal localizations and Loogle search for
   Algebra.IsPushout.cancelBaseChange found the algebraic ingredients already used. Source
   searches of Mathlib, upstream module files and lean/Sheaf found no exact helper theorem.
   In particular relative_flat_of_stalks assumes flatness at every point of X, and
   relative_flat_module_stalk assumes all affine-section tests, so neither directly replaces
   this one-chart criterion. Verdict: pass; helpers are separate proper parts of the argument.
4. Read from the target through the section comparison and chart criterion to their existing
   dependencies. The proof uses Mathlib pushout cancellation and localization criteria directly.
   Every proof-only import is plain import; public imports supply signature notation or types.
   The old direct dependency list is now enumerated above, distinguishing transitive uses from
   actual pruning. No whole module is pruned. The unit sk-thm-picard-semicon has realized
   statement [] and steps [[]], so no realized unit step is bypassed. Verdict: pass.
5. Read all three delivered nodes and their referenced declarations. Their proof_deps equal
   the union of proof-step uses and agree with the Lean route. The affine-spectrum node is
   used mathematically through its equivalent affine section-ring pushout interface, as the
   new section node explains, rather than its particular pullbackSpecIso implementation.
   Both new nodes have sources, self-contained statements, docstring proofs, search records,
   creation/provenance, chapter/unit, and matching Lean records. Verdict: pass.

Changed only this report: expanded No longer needed to name every replaced old direct DAG
proof dependency and clarify the Mathlib pushout route, and added this independent second
reading. No Lean proof or node repair was needed.
