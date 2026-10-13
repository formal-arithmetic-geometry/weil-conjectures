## What changed

Repair of the import_prune_check return: removed the private declarations
`compact_sup_affines` and `isIso_over_of_le` entirely. The insertion case now uses
Mathlib's `Finset.isCompact_biUnion` and `IsCompact.union` directly after rewriting
open-set coercions. It uses Mathlib's `NatIso.isIso_map_iff` directly for the specific
restricted morphism, with preservation of isomorphisms by the restriction functor.
No replacement duplicate theorem, new import, interface change, or adaptation was added.


Replaced the sole sorry in
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_extension` by a complete Lean
finite-affine-cover induction. The original declaration and its visibility are unchanged.
The proof first extends the original pair quasi-coherently to X. Its induction carries
actual global quasi-coherent modules and maps, finite presentation on the growing open,
and an isomorphism on U. At each insertion it combines an affine replacement and binary
gluing, extends the glued map quasi-coherently, transports its restricted isomorphism using
`overFunctorMap` naturality, and composes with the preceding map. A finite affine subcover
finishes the induction. Locality on the singleton top cover gives global finite presentation;
functoriality proves the final morphism equation.

Added two modules, each containing one named remaining step:
`Sheaf.AlgebraicGeometry.ModuleFinitePresentationAffineReplacement` and
`Sheaf.AlgebraicGeometry.ModuleFinitePresentationBinaryGluing`.
The first isolates the finite-free/kernel/cokernel construction on V, and the second
isolates descent on W union V. Neither asserts the global extension theorem.
Their proof-dependency imports retain the existing nodes needed to prove these remaining steps.

Updated the item's DAG proof and proof dependencies to follow the Lean induction.
The source is Stacks 01PI, https://stacks.math.columbia.edu/tag/01PI.
No definition, existing signature, public import, or target statement changed.
All three modules compile individually/in import order through lcompile.py.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_extension`
(node `lem-weil-pbc-module-finite-presentation-extension`). There is no sorry left in the
item's module, including its two remaining private helpers.

Added remaining holes:

- `AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_affine_replacement`
  (node `lem-weil-pbc-module-finite-presentation-affine-replacement`). This only produces
  a module and map on the affine V, with an isomorphism on W intersect V.
- `AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_binary_gluing`
  (node `lem-weil-pbc-module-finite-presentation-binary-gluing`). This only glues an
  already supplied replacement on V to the old module on W, on their union.

This is a decomposition: one upper hole closed, two strictly smaller holes added,
net minus one. It is not claimed as a sorry-free proof. Each remaining proof is exactly
`by sorry`, with its source, complete proof in words, and matching DAG node.

Edge cases checked mathematically: U empty, X empty, a finite cover with no members,
W or V empty, empty overlap, W equal to V, W contained in V, and V contained in W.
The induction starts at the empty finset and uses no nonempty-cover assumption.
The final cover argument also applies to the empty scheme. The affine step on an empty
overlap can use the zero module and free rank zero. Binary gluing needs no compactness,
quasi-coherence, or affineness: its two finite-presentation restrictions cover the union.
Existence witnesses are eliminated in theorem proofs only; no definition chooses data
from a mere unproved existence theorem.

## No longer needed

The two duplicate private helper declarations `compact_sup_affines` and
`isIso_over_of_le` are removed. No import of ModuleFiniteTypeApproximation is needed:
its helpers are private and are not exposed to importers. The proof instead reuses
Mathlib's general compactness and natural-isomorphism results at the insertion case.


Removed from the item's direct imports:

- `Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`.
- `Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections`.
- `Sheaf.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType`.
- `Sheaf.AlgebraicGeometry.ModuleFinitePresentationCokernel`.
- `Sheaf.AlgebraicGeometry.ModuleFiniteTypeSubmoduleExtension`.
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`.
- `Sheaf.Topology.GlueSheavesOfModules`.
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.

The affine generators, kernel finiteness, cokernel finiteness, finite-type extension,
and quasi-coherent kernel modules remain dependencies of the affine-replacement step.
The gluing module remains a dependency of binary gluing. These moved dependencies are
not claimed as globally pruned modules. QuasicoherentFiniteTypeAffine remains reached
through the affine-generators module; its finite-presentation-implies-quasi-coherence
clause is already supplied by Mathlib's instance.

The new route has no direct need for nodes
`lem-weil-pbc-qcqs-scheme-spectral` or `def-weil-spectral-space`: quasi-separatedness
supplies compact overlap intersections directly. The local-lifting node
`lem-weil-pbc-ringed-space-module-exactness-local-lifting` is not needed for the argument's
finite-free surjection, since GeneratingSections already carries an Epi witness.
`def-weil-pbc-generating-sections` and
`lem-weil-pbc-quasi-coherent-finite-type-affine` are no longer direct dependencies of the
item; their uses below affine global generators remain. No unit statement or realized
unit step was bypassed: this item is not among sk-thm-p1's realized statement/steps.

Complete list of old direct proof dependencies absent from the new direct proof:

- `def-weil-pbc-generating-sections`.
- `def-weil-sheaf-of-modules-category`.
- `def-weil-spectral-space`.
- `lem-weil-pbc-affine-finite-type-generating-sections`.
- `lem-weil-pbc-finite-presentation-kernel-surjection-finite-type`.
- `lem-weil-pbc-glue-sheaves-of-modules`.
- `lem-weil-pbc-module-finite-presentation-cokernel`.
- `lem-weil-pbc-module-finite-type-submodule-extension`.
- `lem-weil-pbc-qcqs-scheme-spectral`.
- `lem-weil-pbc-quasi-coherent-finite-type-affine`.
- `lem-weil-pbc-quasi-coherent-module-kernel`.
- `lem-weil-pbc-ringed-space-module-exactness-local-lifting`.
- `pqf-def-coherent`.

These are direct dependency removals, not a claim that their modules leave the
target import closure. The two new steps retain the construction dependencies,
and the statement dependencies still record the module category and quasi-coherence.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two private helpers from
ModuleFiniteTypeApproximation. Importing that module cannot expose either private
name (both qualified #check attempts failed with Unknown constant). The repair
removes both declarations and their custom proofs, replacing their applications
with the existing general Mathlib results. This avoids changing another group's
module or its visibility. The earlier second reading below predates this repair;
its references to four private helpers describe the returned version.


No mathematical error in the existing statement or route was found. The original
nine-step proof does not contain declarations for the whole affine construction or for
the specific two-open gluing with a map into an ambient module. These are now the two
explicit remaining tasks rather than anonymous gaps in the induction.

The local literature/stacks-project/properties.tex source is absent on this machine;
the exact source proof was read at the authoritative Stacks 01PI page instead.
LeanSearch returned Internal Server Error. Its unavailability is recorded without
an absence verdict; LeanFinder, Loogle, and source searches were performed successfully.
No shorter extension theorem was found in Mathlib or either library root.

## New nodes

`lem-weil-pbc-module-finite-presentation-affine-replacement` records steps 3 and 5--8
of the original plan, restricted to construction on the affine V. It cites the existing
finite-type submodule extension, affine finite generators, kernel finite type, and
cokernel finite presentation nodes. Its new module is
`lean/Sheaf/AlgebraicGeometry/ModuleFinitePresentationAffineReplacement.lean`.

`lem-weil-pbc-module-finite-presentation-binary-gluing` records step 9 of the original
plan, constructing only a module and compatible map on W union V from supplied local
data. It cites generic module descent and local finite presentation. Its new module is
`lean/Sheaf/AlgebraicGeometry/ModuleFinitePresentationBinaryGluing.lean`.

Both nodes inherit the item's chapter, unit, and blueprint ancestor. Blueprint searches
found no duplicate. No change record is needed because existing interfaces are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared every delivered module against the repository. The only pre-existing
   declaration is exists_finitePresentation_extension; its signature is byte for byte
   identical, including visibility. Only its proof, proof imports and docstring change.
   There are no definition or target changes and no forced adaptations.
2. Compiled all three modules with lcompile.py, then scratch copies with #print axioms
   for all seven declarations, including the four private helpers. The compactness,
   restriction-isomorphism and singleton-cover helpers use only propext,
   Classical.choice and Quot.sound. The enlargement helper, the upper theorem and
   the two named open steps additionally use sorryAx, as expected. The sole remaining
   sorries are the two reported named theorems. No forbidden declarations or hollow
   definitions occur. Witnesses of open existence statements are used only in proofs.
3. Read Stacks 01PI and the existing finite-type extension, generators, cokernel,
   quasi-coherent extension and module descent declarations. The affine replacement
   and binary gluing are true, strictly partial steps with the required hypotheses.
   Tested empty schemes/opens/overlap and nested/identical opens mathematically; none
   require a nonempty cover or any extra hypothesis. The docstrings give full
   construction arguments, and both have matching nodes. Independent LeanFinder
   searches using affine-neighborhood/locally-finite-presentation phrasing, a Loogle
   search for SheafOfModules gluing and Mathlib/source rg searches found no shorter
   matching theorem. The general module descent theorem is an ingredient of gluing,
   not already the asserted binary finite-presentation statement. Neither remaining
   formalization can reasonably be closed in a few minutes without developing the
   localized-site comparison and descent constructions.
4. Read the induction from the target down: it retains compatibility with the
   original morphism through an initial quasi-coherent extension and compositions;
   naturality transports the isomorphism on each growing open. The finite affine
   subcover and singleton top cover close the global reduction. This is a
   decomposition (one hole closed, two added; net minus one), not a complete proof.
   The public imports supply statement types; remaining private imports supply
   actual proof ingredients or the plans for the two open steps. Checked the unit
   sk-thm-p1 realized list: no realized unit step is removed. Completed the report's
   list of all removed old direct proof dependencies; no globally pruned module is
   claimed.
5. All three nodes' proof_deps equal the union of their proof-step uses. The existing
   node changes only proof, proof_deps and proof_origin. New node statements agree
   with the Lean signatures after whitespace normalization, and have source, full
   proof, searches, creation, blueprint, chapter, unit and Lean records. The
   document-derived induction route matches Stacks 01PI and the code.

Changes made in this second reading: replaced the stale nine-step target docstring
with the actual global quasi-coherent induction and its new named steps; removed an
unused proof import of WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
from ModuleFinitePresentationBinaryGluing; completed the direct-dependency pruning
list and recorded the review. No proof term or statement needed repair.


## Second reading by J3

1. Compared the delivered extension module with the repository using diff and checked
   its existing theorem signature byte for byte up to `:=`: identical. The other two
   modules are new. There is no existing statement, definition, visibility or public
   import change, and no forced adaptation. Verdict: pass.
2. Independently compiled all three modules in import order through lcompile.py.
   Compiled scratch copies with #print axioms for all five declarations, including
   both private helpers. finitePresentation_of_top uses only propext, Classical.choice
   and Quot.sound; the enlargement helper, extension theorem and both split steps
   additionally use the expected sorryAx. Only the two reported named theorems contain
   sorry, each exactly `by sorry`. No axiom, unsafe, opaque, implemented_by, extern or
   hollow definition occurs. All existence witnesses are eliminated inside theorem
   proofs, never used to define data from an unproved mere existence. Verdict: pass.
3. Read the authoritative Stacks 01PI proof and the existing module descent,
   quasi-coherent extension, finite-type submodule extension and locality declarations.
   The affine replacement and binary gluing statements are true and strictly smaller
   parts of the argument, not renamings of the item. Checked empty X, U, W, V and
   overlap; equal and nested W,V; and the empty finite cover. No nonemptiness assumption
   is missing. Their construction docstrings and nodes supply the required proofs in
   words. Independently searched LeanFinder with affine-neighborhood/intersection
   wording, Loogle for overMap, launcher grep for replacement/gluing/enlargement, and
   rg across the library and Mathlib sheaf modules. Found no matching construction
   theorem or shorter global extension theorem. A first Loogle query with an
   unqualified IsFinitePresentation was invalid and was replaced by the successful
   overMap query; it is not evidence of absence. Closing either split statement
   requires the actual affine kernel/cokernel or localized-site descent construction,
   rather than a short application already available. Verdict: pass.
4. Read the proof from the final target down through the finite-affine-cover induction,
   affine enlargement and two new steps. The restriction naturality equation preserves
   the isomorphism on the previous open, and composition preserves the identification
   and final map equation on U. The repaired insertion uses Finset.isCompact_biUnion,
   IsCompact.union and NatIso.isIso_map_iff directly; the previously rejected duplicate
   compactness and restriction-isomorphism helper declarations are absent. Imports
   provide the statement types, proof ingredients or the documented plans for the
   open steps. Compared all old proof_deps with the new list: every removed dependency
   is reported. Checked sk-thm-p1.realized: no realized statement or step is bypassed.
   This is one upper hole closed and two lower holes added (net minus one), a
   decomposition, with no claim of globally pruned modules. Verdict: pass.
5. Parsed all three node files: proof_deps is precisely the union of the proof-step
   uses. The existing node changes only proof, proof_deps and proof_origin. Both new
   node Lean signatures match their modules after whitespace normalization; all
   required source, search, creation, blueprint, chapter, unit and Lean fields are
   present. The documented route follows the Lean proof. Verdict: pass.

Changes in this reading: appended this current review of the repaired version and
recorded fresh compilation, axiom and independent search evidence. No Lean proof,
statement, import or node needed another repair.
