## What changed

The signature of `AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_degreewise_lift`
is unchanged. Its former `sorry` is replaced with the finite-support and finite-free-retraction
argument in Lean. The proof imports `Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift` and
`Mathlib.Data.Int.Interval` privately. The latter supplies `LocallyFiniteOrder ℤ` for the finite
support interval; removing it was tested and fails instance synthesis.

A new module `Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift` states the single-sheaf lifting
interface, with a shared family of natural restriction-stalk comparisons. The source is finite
free, the target arbitrary. It asserts neither bounded complexes nor simultaneous degreewise
maps nor an affine neighbourhood. The main proof extends this single-source result to arbitrary
finite-free retracts by naturality and the splitting identity, then handles the finite support,
common neighbourhood, affine shrinking and zero-source degrees.

The node `lem-sc-perfect-open-stalk-degreewise-lift` now records this route. No definition,
existing declaration signature, public import, or other module was changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_affine_perfect_open_stalk_degreewise_lift`
(node `lem-sc-perfect-open-stalk-degreewise-lift`). Its full proof compiles with no local holes.

Added: `AlgebraicGeometry.Scheme.exists_open_stalk_free_map_local_lifts`
(node `lem-sc-open-stalk-free-map-local-lift`), the sole `sorry` of the new module
`Sheaf.AlgebraicGeometry.OpenStalkFreeMapLocalLift`. Its proof is exactly `:= by sorry`.
The declaration and node give the complete single-sheaf argument and its sources.

This is a decomposition: one original hole closed and one strictly smaller hole added,
so the delivery claims no positive net hole reduction. The remaining theorem requires a
free source rather than a retract and contains no infinite degree family or affine conclusion.

Both delivery modules compile individually, and together in import order through `lcompile.py`.
The symbolic proof covers an empty support interval (`a > b`), zero source terms, zero free
ranks, and arbitrary targets. The local lemma was checked mathematically against those cases:
rank zero uses the zero map on U, empty U supplies no point, arbitrary N only contributes
finitely many prescribed image germs, and no Noetherian hypothesis is needed. Choices of
lifts occur only in theorem proofs; no data definition chooses an arbitrary unproved witness.

## No longer needed

Removed proof dependency: `lem-weil-pbc-stalk-internal-hom-finite-presentation`, module
`Sheaf.AlgebraicGeometry.StalkInternalHomFinitePresentation`. The original module did not
explicitly import it, so no existing import line was removed. This route directly sandwiches
maps through the supplied finite free retractions; it does not need finite-presentation
transport, the internal-Hom comparison, or the finite-presentation stalk-kernel route.
Those branches are not added to the import closure by this delivery. Global reachability
from other targets is left to the maintainer's queue computation.

The original public imports `PerfectComplex` and `OpenModuleStalkFunctor` remain necessary
for the statement. Both added private imports are used. No other planned nodes or modules
are claimed pruned. The new lemma's own plan uses the existing generic tools
`new-module-restriction-stalk-components` and
`lem-weil-pbc-finite-free-local-stalk-map-lift`; these serve restriction comparison and
single finite-free lifting, respectively, without replacing a unit step.

## Where the brief, the DAG or earlier work was wrong

The original plan groups several nontrivial interface steps into its internal-Hom citation:
transport from the slice site to U, a natural comparison after every restriction, and
compatibility of local representatives on a common smaller open. The internal-Hom theorem's
actual signature is a ringed-space germ formula, not the open-site functor isomorphism needed
here. This is an interface gap, not a false mathematical statement. The new theorem exposes
that single-sheaf gap and allows the finite-support argument to be checked by Lean.

Searches found Mathlib's additive `Scheme.Modules.restrictStalkNatIso` and its germ formulas,
plus the library's `FiniteFreeLocalStalkMapLift` and `FiniteLocallyFreeStalkHomLift`.
None is the combined open-site natural comparison and local-lift statement in one application.
A direct attempt to compose `overMapCompOverEquiv`, the linear restriction comparison from
`Modules.RestrictionStalkExtensionIso`, and restriction-of-scalars composition encountered
nondefinitional point transport: `X.homOfLE hWU ⟨x,hxW⟩` equals `⟨x,hxU⟩`, but their stalk
rings cannot be composed without explicit dependent transports. The scratch attempt remains
outside the delivered Lean tree; the named obligation records the complete intended argument.

The unit `sk-prop-av-cube` and its realized statement/steps are untouched. The refinement is
below the unit, within the existing local perfect-model comparison route. Source checks read
Stacks Tags 01CP and 00A0 (3) online. LeanSearch was unavailable; actual LeanFinder, Loogle and
Mathlib/library grep results are recorded in the new node.

## New nodes

`lem-sc-open-stalk-free-map-local-lift`, in `dag/nodes/sec-abelian-varieties/`, is stated by
`AlgebraicGeometry.Scheme.exists_open_stalk_free_map_local_lifts` in
`lean/Sheaf/AlgebraicGeometry/OpenStalkFreeMapLocalLift.lean`. It has the parent's chapter,
unit and blueprint ancestor, an exact Lean statement, actual search records, and a proof in
words. Blueprint search for `finite free stalk` found zero matches. No change record is
needed because existing interfaces are unchanged.

## Second reading by D4

1. **Interfaces: pass.** Compared the existing module with the repository by `diff -u`
   and checked its theorem signature byte for byte with a script. Only the proof body
   and two private imports differ. No existing definition, docstring, statement, public
   import, or other module changed; no change record is required.
2. **Proof and axioms: pass as a decomposition.** Compiled both delivery modules in
   import order with `lcompile.py --all`. Checked the sole remaining `sorry` is exactly
   the reported public theorem, with no forbidden declaration forms or hollow definitions.
   Compiled scratch copies with `#print axioms` for both declarations: each uses only
   `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`. The main proof
   uses naturality, the retraction identity, a finite interval of neighbourhoods, affine
   shrinking, and zero-source morphisms. Arbitrary lift choices occur within theorem
   proofs only; no definition extracts arbitrary data from an unproved existence result.
3. **Split obligation: pass.** Read its full quantifier order and natural-language proof,
   and independently checked rank zero, empty opens (the point hypothesis is impossible),
   arbitrary targets, and zero stalk rings. Canonical germ comparisons are chosen once
   before the maps, so the finite intersection proof really has common coordinates.
   This free-source, single-map result is strictly a part of the degreewise retract
   argument, not its restatement. Read the actual related declarations in
   `FiniteFreeLocalStalkMapLift`, `FiniteLocallyFreeStalkHomLift`, and
   `Modules.RestrictionStalkExtensionIso`. Independent LeanFinder, Loogle and grep
   searches with different queries found germ/localization APIs, not the complete
   slice-site statement. Independently read [Stacks 01CP](https://stacks.math.columbia.edu/tag/01CP)
   and [Stacks 00A0 (3)](https://stacks.math.columbia.edu/tag/00A0): finite free sources
   are finitely presented, and restriction comparisons are the canonical germ maps.
   Closing the remaining slice-site and dependent scalar transports is not a short
   proof repair; it remains the explicitly recorded obligation.
4. **Pruning and route: pass.** Both original public imports provide statement data;
   the new private theorem import supplies the lifting step and the integer interval
   import supplies local finiteness. The report names the only old proof dependency
   absent from the new route, `lem-weil-pbc-stalk-internal-hom-finite-presentation`.
   This is below the unit level. Read `dag/units/sk-prop-av-cube.json`: its statement,
   steps and `realized` fields are unchanged; no unit step is bypassed.
5. **Nodes: pass.** Existing node changes are confined to `proof`, `proof_deps`,
   `proof_origin`. Checked that both dependency lists are precisely the unions of
   their proof steps' uses, and the new node's Lean statement equals its signature.
   The new node has its source, complete argument, searches, split status, creation
   record, blueprint ancestry, chapter, unit and Lean record. Its plan distinguishes
   the comparison interface from finite-free local lifting.

Second reading changed no Lean proof or interface. Added the independent Loogle
search record to the new node and this review section. One original hole is closed
syntactically and one strictly smaller hole is added: net zero, a decomposition,
not an axiom-free completed theorem.
