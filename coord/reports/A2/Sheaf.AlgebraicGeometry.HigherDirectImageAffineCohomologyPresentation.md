## What changed

Replaced the sorry in AlgebraicGeometry.higherDirectImage_affine_cohomology_presentation
with a complete Lean proof using the existing higherDirectImagePresheaf universal
property and Mathlib TopCat.Sheaf.hom_ext on the affine basis. Its statement and
visibility are unchanged. Added HigherDirectImageCoefficientComparison, which isolates
the coefficient-natural resolution comparison (original proof steps 1 and 2).
The new statement identifies each comparison component with an isomorphism followed
by canonical theta; it contains no morphism-detection assertion. The assigned module
cancels these isomorphisms, extends affine component equality to presheaf equality,
and invokes unique factorization. Updated the assigned node's proof and dependencies.
No definitions, existing signatures, or other modules were changed. On resuming
the earlier attempt, scoped the two backward.isDefEq options to the assigned theorem
with `set_option ... in`; global options had caused the first dry run to flag an
interface change. The existing docstring and theorem signature are preserved.

## Proved and sorry left

Closed: AlgebraicGeometry.higherDirectImage_affine_cohomology_presentation
(lem-pc-higher-direct-image-affine-cohomology-presentation), the item's only hole.
Added: AlgebraicGeometry.higherDirectImage_coefficient_comparison
(lem-pc-higher-direct-image-coefficient-comparison), the only sorry in the delivery.
This is a decomposition, not a net reduction of holes: one closed, one added.
The affine-basis detection and universal-property uniqueness argument is proved.
The remaining obligation is the naturality and resolution identification of the
comparison maps. Its source and complete proof in words are in its docstring and node.
Checked degree zero, the zero module, empty inverse-image opens, and empty Y:
the resolution comparisons apply without positive-degree or nonempty hypotheses,
and basis extensionality includes the empty space. No arbitrary witness from an
unproved existence theorem is used in a definition; no new definitions are introduced.
Both modules compile locally without warnings through lcompile.py.

## No longer needed

Removed direct proof imports from the assigned module:
Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact and
Sheaf.Topology.RestrictInjectiveResolution. Their nodes
lem-sc-derived-open-restriction-adjunction-exact and
lem-sc-ringed-space-restrict-injective-resolution are now dependencies of the new
comparison lemma, so their modules remain needed in the overall closure.
No module is claimed pruned from the target closure. The explicit stalk-representative
argument and the restriction-compatibility clause of higherDirectImagePresheaf are
unnecessary for detection: affine-basis extensionality plus its universal property
suffices. The presheaf module remains needed, so its other clauses are not pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's stalk argument was longer than necessary:
Mathlib already supplies the required basis extensionality. The existing
OpenModuleCohomologyComparison has an objectwise comparison with abelian cohomology,
which does not directly supply the coefficient-natural map required here.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, and local
source searches were performed. The local literature checkout does not contain
cohomology.tex, so Stacks Tags 01E1 and 01E4 were read on the official website.
A further attempt at closing coefficient naturality encountered excessive elaboration
of homology comparisons; that unfinished experiment is outside the delivered Lean
files. The compiling reduction was retained. The unit record has empty realized
lists, and this proof changes no unit statement or step.

## New nodes

lem-pc-higher-direct-image-coefficient-comparison, in
lean/Sheaf/AlgebraicGeometry/HigherDirectImageCoefficientComparison.lean, isolates the
resolution construction and coefficient naturality, strictly omitting the assigned
statement's affine morphism detection conclusion. It records the source, edge cases,
three search kinds and the existing exact-restriction and presheaf dependencies.
The blueprint ancestor is inherited from the enclosing coproduct-epi node:
lem-sc-finite-duality. No change record is needed because no existing interface changed.

## Second reading by A2

1. PASS. Diffed the assigned module against the read-only repository. Its existing
   theorem signature is byte for byte identical (also checked mechanically), as are
   its visibility and docstring. Only proof imports, theorem-local elaboration
   options, and its proof changed. The other module is new. No definitions or
   existing interfaces changed, so no change record or downstream adaptation is needed.
2. PASS, conditional on the reported lower obligation. Compiled both delivered
   modules together through lcompile.py, in import order, with no errors or warnings.
   Scratch-copy #print axioms for both declarations returned only propext,
   Classical.choice, Quot.sound and sorryAx. The assigned module has no sorry;
   the comparison theorem has the delivery's only sorry. Scanned both files for
   forbidden declarations/options and arbitrary witness selection: none. No new
   definitions are present. The affine-basis cancellation and unique-factorization
   argument was read line by line against the proved HigherDirectImagePresheaf.
3. PASS as a decomposition. The new lemma isolates the coefficient-natural
   comparison and its resolution formula, without any affine detection conclusion.
   Detection is proved separately using hom_ext and the universal property, so this
   is not the original item renamed. Verified the natural-language proof against
   Stacks 01E1 and 01E4: restrict an injective resolution, identify section complexes,
   forget scalars exactly, and compare augmentation-preserving lifts. The formula
   works for every resolution by homotopy invariance. Degree zero is ordinary
   sections; the zero module and empty inverse-image open give zero cohomology;
   empty Y introduces no nonemptiness requirement. Independent LeanFinder, Loogle,
   Mathlib source and local-library searches found no duplicate. In particular,
   OpenModuleCohomologyComparison is objectwise, and ModuleCohomologyTopComparison
   supplies only the whole-space comparison, not the required coefficient formula.
   Closing the remaining full naturality/resolution obligation is not a short
   application of those declarations. Its source, proof docstring and node are present.
4. PASS. The proof takes the existing presheaf universal property and Mathlib's
   basis extensionality rather than constructing stalk representatives. Its plain
   imports are proof-only; public imports provide the types and instances in its
   statement. Both removed old proof dependencies are listed under No longer needed
   and retained by the new comparison lemma, so no closure module is claimed pruned.
   Read dag/units/sk-thm-picard-duality.json: its realized statement and step lists
   are empty. No unit record or unit-level route is changed by this lower reduction.
5. PASS. Diffed the existing node: only proof, proof_deps and proof_origin changed.
   Mechanically checked both nodes' verbatim Lean signatures and that proof_deps
   equals the union of step uses. Read the new node's source, statement dependencies,
   blueprint ancestry, chapter/unit, created record, searches and Lean record;
   they match the comparison and the delivered proof.

Second reading changed only review documentation and search evidence: appended this
section and added independent, relevant comparison searches to the new node. No Lean
proof or statement needed repair. One upper hole closed and one lower hole added:
zero net holes closed, one decomposition, no target-closure modules pruned.
