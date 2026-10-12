## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_affineBaseChange_chart_coordinates`
without changing its signature or any public import. Only the item's module and its
existing DAG node are delivered.

Two private proved helpers construct the unit-normalized source and target coordinates.
The source helper applies `exists_tensorPullback_affine_sections` and swaps tensor factors.
The target helper uses Mathlib's `isIso_pushoutSection_of_isAffineOpen` and
`Algebra.IsPushout.equiv` to identify the target section ring, applies the same affine
pullback-sections theorem to g', and proves scalar compatibility by tensor induction.
The main proof uses the actual defining adjunction equation, naturality under restriction,
and R'-linearity. No invertibility of the base-change map is assumed.

Added proof imports: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Mathlib.AlgebraicGeometry.Morphisms.Separated`,
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`, and
`Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`.
Updated the node's proof, proof_deps and proof_origin to describe this route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_affineBaseChange_chart_coordinates`
(node `lem-weil-pbc-affine-base-change-chart-coordinates`).

No sorry remains in the delivered module. No holes were added or split off.
The two private helpers are proved. This is a proof from existing declarations,
not a decomposition. The affine-sections and quasi-coherent pushforward dependencies
are used as supplied by the library. The second reader compiled a scratch copy
against the green library without the sandbox overlay: `#print axioms` for the
main theorem and both private helpers lists exactly `propext`, `Classical.choice`
and `Quot.sound`, with no `sorryAx`.

The unchanged statement and proof require no nonempty-open or nonzero-ring hypothesis.
For empty charts, zero rings and the zero module the same section-ring pushout,
affine pullback-section theorem, tensor balancing and unit equations apply.
Single-file compilation is clean. The delivery dry run performs the final compiler,
signature, axiom and shape checks.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.AffineBaseChangeTensorComparisons`.
Node `lem-weil-pbc-affine-base-change-tensor-comparisons` and module
`Sheaf.AlgebraicGeometry.AffineBaseChangeTensorComparisons` are no longer dependencies
of this item. Its specialized Spec/tilde comparison route is replaced by the existing
arbitrary-affine-open pullback-sections formula. This is pruning of this item's route;
other importers may still need that node and module.

`ModuleBaseChangeMapOpenRestriction` stays as the original public import because it
supplies the definition of beta. The proof uses that definition, not the additional
open-restriction theorem: naturality of the section morphism suffices. No realized
statement or step of the unit `sk-thm-p1` is bypassed.

The experimental new target-comparison module was removed after its entire proof was
incorporated as a private helper. No new module or node is delivered.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned transport from the specialized Spec/tilde
comparison was unnecessary: `exists_tensorPullback_affine_sections` already gives
unit-compatible coordinates on arbitrary affine opens, and Mathlib supplies their
section-ring pushout. The old proof sketch had left this transport implicit; the
private helpers now carry it out explicitly. Every target statement and definition
is unchanged.

## Second reading by F2

1. **Unchanged interfaces — pass.** Read the complete repository/sandbox diff.
   The signature of `AlgebraicGeometry.Scheme.Modules.exists_affineBaseChange_chart_coordinates`
   is byte for byte identical, as are all public imports. The node still assumes precisely
   an affine f, a cartesian square, a quasi-coherent F, affine U and W, and W ≤ g⁻¹U.
   Its R, B, R', M, their scalar structures, both R'-linear equivalences, the canonical
   `moduleBaseChangeMap`, and the equation for every r and m match the Lean statement.
   No definition, target, other module, or change record is added or altered.

2. **Proof and axioms — pass.** Compiled the delivered module cleanly through `lcompile.py`.
   Also compiled a scratch copy without the sandbox overlay and printed axioms of the
   source helper, target helper and main theorem: each uses only `propext`,
   `Classical.choice`, `Quot.sound`; none uses `sorryAx`. Scanned the delivered Lean for
   sorry, axiom, unsafe, opaque, implemented_by, extern and kernel-check bypasses: none.
   The section comparison's pure-tensor equation uniquely determines its linear map;
   bijectivity uniquely determines its inverse. The chosen adjunction's theorem pins
   its unit to the explicit tensor/sheafification formula. The section-ring equivalence
   is the canonical pushout equivalence. No arbitrary existence witness is used as data
   in a new definition; indeed no new definition is delivered.

3. **Split statements and small cases — pass.** There are no split-off holes or new nodes.
   Read both proved private helpers: the first swaps the existing affine-section
   comparison and checks scalar compatibility; the second transports through the
   section-ring pushout, proves R'-linearity by tensor induction, then uses tensor
   balancing and composition of restrictions to obtain its unit equation.
   Neither helper restates the main coordinate formula. Empty W forces V' empty;
   empty U forces W empty. The zero-ring and zero-module cases introduce no missing
   nontriviality assumption, since all maps and pushouts remain defined. The identity
   square gives the usual scalar-extension unit equation.

4. **Shortest route, imports and pruning — pass.** Searched with the independent
   LeanFinder query "canonical exchange map for affine pushforward of a quasi coherent
   sheaf in tensor section coordinates" and searched both library roots with alternate
   pullback/section and module/base-change terms. Found sectionwise pushforward formulas
   and specialized base-change ring comparisons, but no direct replacement for the
   theorem on arbitrary compatible affine opens. The proof already uses the general
   affine pullback-section formula and Mathlib's affine section-ring pushout.
   All four added imports are proof-only: Flat supplies the section-ring pushout;
   ModulePullbackAffineSections supplies the canonical comparison;
   QuasicoherentPushforwardQcqs supplies quasi-coherence of f_*F; Separated supplies
   affine ⇒ separated ⇒ quasi-separated. A scratch compile removing Separated failed
   specifically at synthesis of `QuasiSeparated f`, confirming that import is needed.
   The only removed old proof dependency is the tensor-comparison node/module already
   listed under No longer needed. ModuleBaseChangeMapOpenRestriction remains for the
   definition of beta, not an invocation of its open-restriction theorem. Read the
   unit `sk-thm-p1` and its `realized` lists: no realized statement or step is removed
   or bypassed by this change below the unit level.

5. **DAG agreement — pass.** Read the item node and each of its four proof-dependency
   nodes, their recorded declarations/Mathlib matches, and the old-node diff. Source
   coordinates use pushforward quasi-coherence and affine pullback sections; target
   coordinates use the same sections theorem and the affine fibre-product fact in its
   Mathlib section-ring pushout form. The last step unfolds the defining adjoint of
   beta, applies the adjunction equation and restriction naturality, and extends the
   unit equation by R'-linearity. The node's proof and proof_origin describe exactly
   this route, and proof_deps is the union of its step uses. Only stage-3-owned node
   fields differ; the node's statement and Lean signature remain unchanged.

**Second-reader changes:** Corrected the report's provisional dependency/axiom wording
with the actual clean scratch-compile and axiom results, and added this independent
review. No Lean proof or node repair was needed. Closed one original hole, added zero
holes, split off zero statements; this is a proof, not a decomposition.
