## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_submodule_binary_gluing` without changing
its signature. Added four supporting modules: `ModuleSubmoduleBinaryGluingCore` constructs
an actual categorical pullback and proves its inclusion monic;
`ModuleSubmoduleBinaryGluingSecondRestriction` identifies its restriction to V with Q;
`ModuleSubmoduleBinaryGluingProperties` proves the inclusion is an isomorphism on W and
packages the two restrictions; `ModuleBinaryLocalProperties` proves locality of
quasi-coherence and finite type on the union site. All supporting results are proved.
The main module imports the restriction and locality results privately.

The pullback is constructed from Mathlib's finite limits, not selected from an
unproved existence theorem. Its direct-image map is the given inclusion transported
through the canonical iterated-restriction isomorphism. Monicity follows from
right-adjoint preservation and pullback. The restriction proofs evaluate the pullback,
use the actual slice-site adjunction maps, and assemble component inverses. The local
properties proof transports presentations and generating families through an
iterated-slice equivalence and uses a cover indexed by ULift Bool.

The main module contains proved private helpers transporting finite type across
isomorphisms. The locality module reuses the proved generator-transport and cover
arguments from `QuasicoherentFiniteTypeAffine` as local helpers, avoiding an import
of unrelated affine theory. All five delivered modules compile without warnings.
The main proof and restriction construction work for empty opens, disjoint opens,
repeated opens, and the empty scheme. Neither compactness nor affineness is used.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.Modules.exists_submodule_binary_gluing`
(node `lem-weil-pbc-module-submodule-binary-gluing`).

Added zero holes. No `sorry` remains in any delivered module. This is a complete proof,
not a decomposition. The added public results are
`binarySubmoduleInclusion_mono`, `binarySubmodule_on_V`,
`binarySubmodule_restrictions`, and `module_binary_local_properties`, all in
`AlgebraicGeometry.Scheme.Modules`. All private helpers are also proved.

## No longer needed

No imports were removed: the original public import of `Coherent` is still needed by
the unchanged statement. `def-weil-sheaf-of-modules-category` is no longer a standalone
proof dependency of the target node: its sectionwise construction step was replaced by
the explicit pullback node. It remains a statement dependency and its definitions remain
used; this does not prune its module. The two other original proof dependencies,
`pqf-def-coherent` and `def-weil-pbc-module-finite-type-presentation`, remain used.

The generic `Sheaf.Topology.ModuleObjectOpenDescent`,
`Sheaf.Topology.ModuleObjectOpenDescentAux`, and
`Sheaf.Topology.GlueSheavesOfModules` are not used or imported by this proof.
Their nodes `lem-weil-pbc-module-object-open-descent`,
`lem-weil-pbc-module-object-open-descent-aux-diagonal`, and
`lem-weil-pbc-glue-sheaves-of-modules` are unnecessary for this item; this does not
claim they are globally unreachable. No previously imported module is pruned.
The sectionwise image-subsheaf construction in the original plan is replaced by
Mathlib's pullback, which has the same local restrictions.

## Where the brief, the DAG or earlier work was wrong

The original DAG described a sectionwise construction but named only definition
nodes as proof dependencies; none of these supplied the required gluing interface.
The concrete pullback gives a shorter construction and supplies the exact restrictions
needed by the main theorem. The target statement and unit route are unchanged.

An arbitrary submodule whose inclusion is an isomorphism on W need not be of finite
type on W union V: take W empty and an infinitely generated module on V. The proof
therefore explicitly uses the identification with the given finite-type Q on V;
it does not infer local properties from monicity and the W restriction alone.

The local Stacks TeX files are absent on this machine. Read the cited sources directly
at https://stacks.math.columbia.edu/tag/01PF,
https://stacks.math.columbia.edu/tag/01BE and
https://stacks.math.columbia.edu/tag/01B5. The Lean implementation is recorded as
agent-written. LeanSearch returned Internal Server Error, recorded as unavailable;
LeanFinder, Loogle, and Mathlib source searches returned related definitions and
lemmas but no exact binary-submodule theorem. Searches of the imported blueprint
found no duplicate of the concrete pullback or binary locality statement.

## New nodes

`def-weil-pbc-module-binary-submodule-pullback` records the concrete pullback and
first projection in `ModuleSubmoduleBinaryGluingCore`. No arbitrary data witness
is selected.

`lem-weil-pbc-module-binary-submodule-mono` records the proved monicity of that
projection in the same module.

`lem-weil-pbc-module-submodule-binary-gluing-second-restriction` records the proved
identification on V in `ModuleSubmoduleBinaryGluingSecondRestriction`. It requires
no monicity or overlap hypothesis.

`lem-weil-pbc-module-submodule-binary-gluing-restrictions` records the proved
restriction isomorphism on W and the identification on V in
`ModuleSubmoduleBinaryGluingProperties`. It requires only invertibility on the overlap.

`lem-weil-pbc-module-binary-local-properties` records the proved locality of
quasi-coherence and finite type in `ModuleBinaryLocalProperties`.

Updated the original node's proof, proof dependencies, and proof origin to match
these proved results. No signatures or definitions of existing modules changed,
and no change record or forced adaptation is needed.

## Second reading by E1

1. Compared the delivered `ModuleSubmoduleBinaryGluing.lean` with the repository version. The
   existing theorem signature is byte-for-byte unchanged; only imports, private helpers, the
   proof, and its explanatory docstring changed. The four supporting modules are new files.
   Verdict: no accidental statement or definition change.
2. Compiled all five delivered modules with `lcompile.py --all`. No errors, warnings, `sorry`,
   axioms, unsafe declarations, or hollow definitions were found. The concrete pullback is
   constructed directly from finite limits. Verdict: proof is kernel-checked and uses no
   forbidden construction. A scratch axiom probe for the target, pullback definition,
   monicity instance, both restriction results, and locality theorem reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`.
3. Checked the supporting declarations and their DAG nodes. The pullback, monicity,
   restrictions, and locality statements are true, strictly simpler than the target, and each
   has a source, proof description, and matching Lean declaration. No duplicate declaration was
   found in the imported library. Independent LeanFinder, Loogle, and grep searches
   for local finite generation and pullbacks of subobjects found only the generator
   interfaces already used and ordinary module submodule pullbacks. Verdict: split-off statements are valid and necessary.
4. The target proof follows the shortest available route through the concrete pullback and
   locality results. The original generic descent/gluing dependencies are not imported or used;
   the report records them as no longer needed. Public imports remain limited to the target's
   statement dependency, while proof-only imports are private. Verdict: pruning and import
   visibility are correct.
5. The target node's proof, proof dependencies, and proof origin match the Lean proof, and the
   binary gluing unit's statement and route are preserved. Verdict: DAG and unit metadata agree
   with the delivered code.

I changed only this report: added the required second-reading record and explicitly listed
the removed standalone proof dependency `def-weil-sheaf-of-modules-category`. No Lean code
or DAG content was changed during review.
