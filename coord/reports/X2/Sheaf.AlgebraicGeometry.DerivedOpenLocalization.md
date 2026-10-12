## What changed

Proved AlgebraicGeometry.nonempty_derivedOpenLocalization with its signature unchanged.
Added the proved helper AlgebraicGeometry.nonempty_openExtensionRestrictionIso in
Sheaf.Algebra.Homology.OpenExtensionRestrictionIso. It shows the extension/restriction
unit is invertible using the existing module_extensionByZero_stalk_maps germ formula
and Mathlib's stalkwise isomorphism criterion.

The main proof uses the standard localization only on U and the chosen ambient
localization directly. Functoriality of exact derived functors carries E ⋙ R ≅ identity
to D(E) ⋙ D(R) ≅ identity, yielding faithfulness of D(E). Mathlib's
locallySmall_of_faithful and hasLocalizationOfLocallySmall construct the localization
in the requested Hom universe. Pointwise Nonempty and choice form the dependent family.
All added proof imports are non-public. No existing definitions or signatures change.

## Proved and sorry left

Closed the sole original hole: AlgebraicGeometry.nonempty_derivedOpenLocalization
(lem-pc-derived-open-localization-universe). Proved the new helper
AlgebraicGeometry.nonempty_openExtensionRestrictionIso
(lem-pc-open-extension-restriction-iso). No sorry remains in either delivered module;
no holes added or split off. Existing dependencies, including
AlgebraicGeometry.module_extensionByZero_stalk_maps, retain their existing holes.
This proves the assigned statement from the project's named dependency declarations;
it does not claim the complete transitive proof closure is sorry-free.

## No longer needed

Removed the direct import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact from
the assigned module because the new helper publicly imports its statement interface;
its declaration and node are still used by the main proof.

The planned derived adjunction, its full-faithfulness proof, comparison of two ambient
localizations, and manually transported Hom composition are unnecessary. In particular
Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction
(lem-sc-derived-open-shriek-derived-adjunction) and
Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
(lem-pc-derived-adjoint-functors) are not needed by this proof and are not imported.
Second reading also removed the redundant proof import Mathlib.Topology.Sheaves.Stalks
from OpenExtensionRestrictionIso; the required stalk declarations are already available
through its other imports. No former proof-dependency node is removed: the exact restriction/extension theorem
remains needed. No assertion is made that the two unused modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound but stronger than necessary. Faithfulness,
rather than full faithfulness, suffices to transfer local smallness. The natural
extension/restriction isomorphism was not itself a named statement in the original
proof dependencies. It is now a proved helper, rather than another unfinished item.
Empty and total opens are included: the stalk criterion is vacuous on the empty open.
The helper and its two project dependencies belong to the same unit; no unit step or
chapter route changes. The unit's realized entries do not name this auxiliary node.

## New nodes

lem-pc-open-extension-restriction-iso records the proved helper and its precise germ
argument, using lem-sc-derived-open-restriction-adjunction-exact and
lem-sc-module-extension-by-zero-stalk-maps. Its source is Stacks Tag 00A7 (4), with
(3) for the stalk description. Searches found no duplicate blueprint node or exact
Mathlib declaration. No change record is required because no existing signature or
definition changes.


## Second reading by X2

1. PASS: compared DerivedOpenLocalization against the repository with diff. Its sole
existing declaration, AlgebraicGeometry.nonempty_derivedOpenLocalization, has a
byte-for-byte unchanged signature; changes are its proof and non-public proof imports.
OpenExtensionRestrictionIso is a new module with one new theorem and no definitions.
There is no target, definition, or existing statement change and no change record.

2. PASS: compiled both modules in import order with lcompile.py, without warnings.
Searched the delivered Lean for sorry, axiom, unsafe, opaque, implemented_by, and extern:
none occurs. Scratch copies with #print axioms for both declarations report exactly
propext, Classical.choice, Quot.sound, and sorryAx. The latter comes from existing
imported holes, notably module_extensionByZero_stalk_maps, not any new hole. Choices
of adjunctions and stalk isomorphisms are local to proofs of Nonempty; no definition
stores arbitrary data selected from an unfinished existence theorem. Derived functor
composition, natural-isomorphism transport, and identity comparisons are the actual
proved localization constructions in the source ExactFunctor module.

3. PASS: there are no split-off unfinished statements. Read the new helper against
Stacks https://stacks.math.columbia.edu/tag/00A7 clauses (3) and (4), and the module
construction in https://stacks.math.columbia.edu/tag/03DI. It assumes an arbitrary
ringed space and open, with no compactness or separation assumption. Its germ equation
uses the SAME chosen adjunction as the dependency statement; stalk extensionality
identifies the composite with the given interior stalk isomorphism. Forgetting modules
and the slice/open equivalence both reflect isomorphisms. For the empty open there
are no stalks, so the sheaf stalk criterion is vacuous; for the total open it is the
usual identity comparison, and zero module sheaves give the zero-object isomorphism.
Independent msearch queries used LeanFinder (open-immersion extension by zero fully
faithful), Loogle (Faithful.of_comp_iso), and grep (extensionByZero with Iso); they
found only generic tools and open-immersion ring comparisons, no duplicate helper.
Also searched lean/Sheaf and the DAG for the extension/restriction identity.

4. PASS after import pruning: the main proof first uses the existing exactness theorem,
then the proved stalk-based helper, then proved derived functor functoriality and
Mathlib locallySmall_of_faithful/hasLocalizationOfLocallySmall. An injection of Hom
sets suffices, so the longer full-faithfulness/ambient-comparison argument is unnecessary.
All original proof_deps remain genuinely used; none needs listing as a pruned node.
Read dag/units/sk-thm-picard-duality.json: its realized statement and single step lists
are empty, and neither the item nor the helper realizes a unit step. The unit is unchanged.
Removed redundant Mathlib.Topology.Sheaves.Stalks from the helper and verified its
compile. Tested omitting Adjunction.Additive from the main module: the two additive
adjoint lemmas then become unavailable, so restored that necessary proof import.
Other explicit proof imports provide the helper, derived comparisons, and local-size
localization construction. Public imports supply statement objects and constructions.

5. PASS: read both node records alongside Lean. The main node's two proof steps and
proof_deps describe exactness, the new helper, functoriality, faithfulness, and shrinking
the Hom universe, in the order actually used. The helper's steps use exactly the
adjunction/exactness node and the stalk-maps node, followed by Mathlib's stalk criterion
and reflection of isomorphisms. Its full Lean signature, module/file, source, searches,
origin, created fields, blueprint ancestry, chapter, and unit are present and agree.
The existing node changes only proof, proof_deps, and proof_origin.

Second reading changed only the redundant Stalks proof import and this report.
Closed one original hole; added zero holes; the new helper is proved, not a decomposition.
