## What changed

Replaced the original sorry in `AlgebraicGeometry.truncated_directImage_affine_finiteSupport`
with a complete Lean reduction. Its signature is unchanged.

First construct the coproduct projections of the ambient derived coproduct. Additivity
makes the induced sheaf comparison monic: the projections detect the components of
an algebraic direct sum after presheaf evaluation, and exact sheafification transports
the monomorphism to module sheaves. The comparison monomorphism is proved directly with the fixed ambient coproduct
projections in scope. There are no generic module, presheaf or sheaf mono helper
declarations. The parent `DerivedDirectImageTruncatedCoproduct` cannot be imported
because it imports this item, and its three helpers are private.

The new `truncated_directImage_sheaf_coproduct_epi` gives local epimorphy. Mono and epi
make the sheaf comparison an isomorphism. The separate new
`truncated_higherImages_affine_coproduct` says that evaluation of the coproduct of the
individual truncated higher-image sheaves is a module coproduct. That statement
contains neither S nor the ambient coproduct maps. Its module colimit universal
property and `ModuleCat.coprodIsoDirectSum` give an explicit two-sided inverse for
the canonical algebraic direct-sum map to the evaluated sheaf coproduct. Finally,
check on every `DirectSum.lof` that the displayed linear map factors through this
surjection and evaluation of the sheaf isomorphism. Their composition is surjective.

The two new modules isolate independent parts of the original spectral argument:
local lifting to the higher image of S, and global affine evaluation of the source
sheaf coproduct. Neither is a renamed statement of the original affine-support theorem.
All local steps in the item are proved; no partial proof contains sorry.

Stacks Tags 08DZ, 08D5 and 015J were read online because the cited local perfect.tex
is absent on this machine. LeanFinder, Loogle and Mathlib grep found no shorter
independent comparison. LeanSearch was attempted and returned Internal Server Error.
The three final modules are checked together in import order. No definitions or existing
statements were changed, and no target statement review is reopened.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.truncated_directImage_affine_finiteSupport`
(node `lem-pc-truncated-direct-image-affine-finite-support`). It now contains no sorry.

Added two named holes, each in its own new module:
`AlgebraicGeometry.truncated_directImage_sheaf_coproduct_epi`
(node `lem-pc-truncated-direct-image-sheaf-coproduct-epi`), and
`AlgebraicGeometry.truncated_higherImages_affine_coproduct`
(node `lem-pc-truncated-higher-images-affine-coproduct`). These are every sorry left
in this delivery. The latter concerns only affine evaluation of the coproduct of
the individual higher-image sheaves, not its comparison to a higher image of S.

This is a decomposition: one upper hole closed, two lower holes added, net -1.
No claim of a sorry-free spectral-sequence proof or positive net hole reduction is made.

Edge cases: the projection argument makes no choice of an index, so it includes
I empty. The affine-coproduct statement includes the empty family and empty affine
open. For q<a, the source and target abutments vanish; the remaining spectral lemma
explicitly includes this case. Its quasi-coherence argument starts from the zero
last filtration step and also covers the zero abutment.

## No longer needed

Removed these original proof-only imports from the item:
`Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`,
`Sheaf.CategoryTheory.ExactCoupleMorphism`,
`Sheaf.CategoryTheory.FiniteFiltrationInduction`,
`Sheaf.CategoryTheory.TruncationHypercohomology`,
`Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum`,
`Sheaf.Paper.HigherDirectImagePresheaf`,
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`, and
`Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension`.

Their corresponding eleven former direct proof dependencies are no longer used
in the combining Lean proof. They remain needed in the spectral and quasi-coherence
arguments of the two new nodes, so no entire node or module is claimed globally pruned.
The item's new direct dependencies are local sheaf epimorphy, affine source-coproduct
evaluation, and the proved exact-sheafification tool used in its monomorphism proof.

The eleven old direct proof dependencies removed from the item are:
`lem-pc-derived-ambient-direct-sums`, `lem-pc-quasicoherent-module-coproducts`,
`lem-weil-pbc-quasi-coherent-module-kernel`, `lem-sp-couple-morphism`,
`lem-sp-finite-filtration-induction`, `thm-sp-truncation-e2`,
`lem-weil-pbc-qcqs-cohomology-direct-sum`, `lem-weil-pbc-higher-direct-image-presheaf`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, and
`lem-pc-quasi-coherent-extension`. This lists direct dependency pruning only;
no entire module is claimed pruned from the targets' closure.

No import of the parent truncated comparison, the monolithic Sections module, or
the existing bounded-below QCoh theorem is added: each has a path back to this item.
No blueprint unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent truncated-coproduct comparison is proved but imports this item, so it
is not an independent shortcut. Its monomorphism proof supplies the concrete component calculation, but the three
private helper declarations cannot be reused by importing it. The returned delivery
duplicated those generic declarations; the repair removes them and states only the
monicity of the fixed comparison map inside the target proof. All objects and maps
are explicit local constructions from the target binders.

A shared-helper extraction was tried during repair. The delivery gate refused the
parent adaptation because the original parent still compiles unchanged. Removed
the extraction and its parent adaptation entirely. The final repair changes no other
existing module and adds no new module beyond the two original spectral bridges.

The existing bounded-below quasi-coherence proof cannot be imported here: it imports
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`, which imports
DerivedDirectImagePreservesDirectSums and hence reaches this item. The recorded
`lem-pc-finite-support-hi` declaration names only a vanishing theorem and does not
itself provide the quasi-coherence clause. The ordinary higher-image quasi-coherence
declaration exists in Sections, with that same import obstruction.

An attempted repair extracted the existing ordinary theorem into its own module,
re-exported it from Sections, and reused the existing bounded-below proof. That
candidate compiled and its overlaid import graph had no cycles. deliver3.py refused
it with: “Sections compiles unchanged against your changed dependencies; its adaptation
is not forced. Remove it from this delivery.” The extraction and all its files were
removed; this final delivery adapts no other module and has no change records.
The process/tool mismatch is reported here, not worked around.

The original plan's spectral/naturality interfaces do not directly supply the affine
module comparison as a Lean declaration. The remaining two nodes explicitly state
those bridges, with complete proof instructions, while the item now contains the
real algebraic proof that combines them. The mathematical bounded-below spectral
route is retained below the unit level; no unit-route mathematical error was found.

## New nodes

`lem-pc-truncated-direct-image-sheaf-coproduct-epi`: the local sheaf comparison is
an epimorphism. It does not assert global section surjectivity. Its proof uses
termwise exact sums, qcqs cohomology, natural spectral pages and finite convergence.

`lem-pc-truncated-higher-images-affine-coproduct`: affine evaluation preserves the
canonical coproduct cocone of the individual lower-truncated higher-image sheaves.
Its proof derives quasi-coherence from ordinary localization, page kernel/cokernel
closure and finite extension induction, then uses proved affine colimit evaluation.
There is no S, ambient coproduct hypothesis, or comparison to its higher image in
this statement. It is a distinct needed part of the original argument.

## Earlier second reading (a previous round; superseded)

1. **Repository comparison.** Compared the delivered item module with the repository version. The target theorem signature is byte-for-byte unchanged; the two additional modules and three node records are declared in the report. No existing declaration or definition was altered.

2. **Compilation and trust.** Compiled all three modules with `lcompile.py` in import order. The target contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the only remaining `sorry`s are the two named split-off theorems listed above. The proofs use ordinary Lean declarations and the permitted imported theorem holes.

3. **Split-off statements.** Checked both new statements against their implementations and DAG records. Each is strictly a supporting bridge: local sheaf epimorphy and affine evaluation of the individual higher-image coproduct. They do not restate the affine finite-support target, and repository searches found no existing equivalent declaration. Their docstrings, source references, edge cases, and nodes are present.

4. **Shortest route and pruning.** Reviewed the proof from the target downward. The combining proof uses the projection mono argument, the local epi bridge, affine coproduct evaluation, and the module direct-sum universal property. The removed proof-only imports are no longer referenced by this module; the report records all eleven and explains why their nodes remain needed by the split-off arguments. No import cycle or parent-module shortcut was introduced.

5. **DAG and unit consistency.** Checked `proof`, `proof_deps`, `proof_origin`, module paths, and declarations in all three node files against the Lean proofs. The target node remains on its recorded unit route, with the two new nodes as its explicit supporting dependencies. No unit statement or realized step was bypassed.

**Changes made during second reading.** No Lean proof or statement required repair. Added this second-reading record to satisfy the delivery contract; the dry run is the next verification step.


## Second reading by V1

1. **Visible interfaces: pass.** Independently diffed the item against the repository.
   Its sole existing theorem signature is byte-for-byte identical. Only its proof,
   proof-only imports and local heartbeat option changed. The two new theorem modules
   are declared above; there are no changed definitions or forced adaptations.

2. **Proof and trust: pass as a decomposition.** Compiled all three delivered modules
   together with `lcompile.py`: 5.0 s, 5.5 s and 26.8 s, with no errors or warnings.
   Scanned all delivered Lean sources: exactly the two named theorem holes above;
   no prohibited declarations and no data definitions with holes. An independent
   scratch module importing the sandbox overlay ran `#print axioms` on all three
   declarations: only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is expected because both bridges remain open. The IsColimit witness
   used to construct the inverse determines each desc map uniquely by its legs;
   this is not arbitrary data selected from a mere existence assertion.

3. **Split statements: pass.** Read both statements, complete docstring arguments,
   and nodes against Stacks Tags 08DZ, 08D5, 015J and 01I7. Local sheaf epimorphy
   is strictly the lifting part; the affine source-coproduct lemma contains neither
   S nor its structure maps. Neither merely renames the target. Checked the empty
   family, empty affine open, zero family, singleton family and q<a: the proposed
   maps/colimits have the required zero or canonical identifications. The common
   truncation bound is essential and is present. New searches used “affine sections
   preserve direct sums of quasi coherent module sheaves” (LeanFinder), fully qualified
   `CategoryTheory.Limits.sigmaComparison` (Loogle), and evaluation/colimit and
   truncation/coproduct patterns (Mathlib grep and repository rg). These found the
   already-used coproduct comparison machinery and the general proved affine
   quasi-coherent colimit theorem, which requires quasi-coherence of the higher
   images. They do not close either spectral bridge independently. The existing
   bounded-below QCoh theorem and parent comparison import this item and cannot
   be shortcuts. No split hole could be closed in a few minutes with these tools.

4. **Top-down route and pruning: pass.** Read the entire combining proof: ambient
   projections detect direct-sum components after presheaf evaluation; exact
   sheafification gives the concrete comparison mono; the epi bridge makes it an
   iso; the independent affine colimit bridge gives a two-sided module inverse;
   extensionality on DirectSum.lof checks the final factorization. Every added
   proof import supports these steps and has plain `import` visibility. Public
   imports provide types/operations in the statement, including truncGE. The ten
   removed imports and all eleven removed old direct dependency IDs are recorded
   explicitly above. No module is globally pruned. The unit's realized field is
   unchanged (empty statement list and one empty step list in the repository),
   and no realized unit node is bypassed by this reduction.

5. **DAG consistency: pass.** Checked exact equality of every node's recorded Lean
   signature with its source, and equality of proof_deps with the union of proof
   step uses. The item's steps describe the actual mono/epi/affine evaluation proof.
   Both new nodes have source, proof_origin, search records, split status, creation
   record, blueprint ancestry, chapter/unit, and complete lean records. The exact
   sheafification dependency is an existing Mathlib leaf, not an undeclared hole.

**Changes made during this second reading.** No Lean statements or proofs changed.
Expanded `## No longer needed` with all eleven removed direct dependency IDs and
appended this independent review. One original hole is closed by two strictly
supporting holes, net -1: a decomposition, not a sorry-free proof of the item.
