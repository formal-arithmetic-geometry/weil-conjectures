## What changed

Repair of the returned delivery at head 2a3e6f0cd: removed all nine copied
private declarations from FormalFunctionsDegreeZeroAugmentationCompatibility:
zeroIso, degreeZero_naturality, levelIso, levelIso_hom, unitPushforwardComp,
unitTransition, unitSectionsSquare, degreeZero_unit_square, levelIso_naturality.
Added proof-only `import all Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroSystemIso`.
The proof now uses that module's existing canonical zeroIso, levelIso and
levelIso_naturality directly. SystemIso is untouched, and no existing public
signature or visibility changes. No forced adaptation is needed.

The proof assembles the imported canonical components with NatTrans.ofOpSequence
and obtains a natural isomorphism componentwise. It applies the generic new
formalFunctions_degreeZero_augmented_sections theorem to the unit module,
cancels the augmentation, moves the tensor-unit morphism past restriction by
naturality, and evaluates its unit characterization on t. The remaining
restriction is appLE. All this combination code is proved Lean.

Updated the original node's proof, proof_deps and proof_origin to record actual
reuse of the SystemIso module rather than copied proofs. The generic helper
module and new node are unchanged from the reviewed delivery. The proof-scope
change record is updated to describe reuse rather than added private helpers.
The sk-thm-p1 statement and realized steps remain intact.

Both delivered modules compile using lcompile.py --all. The main module also
compiles alone after removing its redundant direct TensorPullbackStructureSheaf
import. All Lean lines are at most 100 characters. No axiom, hollow definition
or arbitrary data witness is added.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.formalFunctions_degreeZero_augmentation_compatibility
(node lem-weil-pbc-formal-functions-degree-zero-augmentation-compatibility).
No sorry remains in that module.

Added exactly one hole:
AlgebraicGeometry.formalFunctions_degreeZero_augmented_sections
(node lem-weil-pbc-formal-functions-degree-zero-augmented-sections), in
Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentedSections.
Its whole proof is exactly := by sorry. No other hole is added.

This is a decomposition: one original hole closed and one strictly smaller
generic theta/augmentation step split off, net zero in delivered declarations.
The canonical system construction uses existing helpers whose bodies are proved;
its transition proof still inherits upstream sorryAx (see the second reading). The assembly
and final augmentation/unit transport are fully proved in the repaired module.

## No longer needed

Removed original direct proof imports
Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties,
Sheaf.Paper.HigherDirectImagePresheaf and
Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf.
The first and third remain available through SystemIso's dependencies; their
nodes are still used there. HigherDirectImagePresheaf remains needed in the
new generic helper's proof plan. No whole-closure pruning is claimed.

Removed the returned version's direct ModuleCohomologyFMapZeroAugmentation
import: it is used by SystemIso, rather than reproved here. All nine duplicated
private helpers listed above are removed. Their existing declarations in
SystemIso supply the canonical components and transition calculation.
The direct node dependencies on left-exact degree-zero comparison,
module-cohomology-fmap-zero-augmentation and enough-injectives are replaced by
lem-weil-pbc-formal-functions-degree-zero-system-iso; those results remain
needed transitively. The module-pullback-structure-sheaf node remains needed
in the final transport step. No complete module is pruned from target closure.

## Where the brief, the DAG or earlier work was wrong

The previous delivery incorrectly treated private components in SystemIso as
unavailable and copied them. Lean's `import all` makes the existing private
components accessible in the proof. The repair deletes every duplicate flagged
by the landing check, as well as the two copied definitions, and reuses the
original construction without altering its module.

The open-choice existence theorem flatBaseChangeMap_sections_choices currently
assumes Flat g and Flat (pullback.snd g f). These hypotheses do not apply to
formal infinitesimal fibres. Its displayed construction only restricts resolutions
and transposes the unit under an open restriction adjunction, and does not need
those flatness assumptions. The new helper's proof plan spells out that
construction directly from exact open restriction; it never invokes flatness of
the infinitesimal closed immersion. No statement is disputed or weakened.

The local literature tree contains lists but no cohomology.tex. Read the official
Stacks pages https://stacks.math.columbia.edu/tag/01E4,
https://stacks.math.columbia.edu/tag/01FB and
https://stacks.math.columbia.edu/tag/01E1, and fetched cohomology.tex into the
sandbox scratchpad to check the labels lemma-describe-higher-direct-images,
remark-explain-arrow/equation-choice and lemma-cohomology-of-open. The sources
are available and do not require a new literature request.

## New nodes

lem-weil-pbc-formal-functions-degree-zero-augmented-sections is the canonical
theta formula for augmented sections of any module, before applying the
structure-sheaf isomorphism. It is sourced from Stacks 01E4, 01FB and 01E1.
The node gives the restricted-resolution construction without flatness, the
augmentation-preserving section-class normalization, germ naturality, the
zero-augmentation square for the restricted h-map, and cancellation of the
restriction to the whole fibre. Edge cases checked in the proof plan: zero
module, zero section, empty fibre, V=top, n=0, and an arbitrary nonflat fibre
projection. The statement is an equality of fixed maps and chooses no data
from an unproved existence theorem.

LeanFinder found only group-cohomology augmentation comparisons. Loogle found
no result for the resolution augmentation query; local source supplies the
canonical generic augmentation lemmas but no formal-fibre theta formula.
LeanSearch returned Internal Server Error and is recorded as unavailable,
without a verdict. Grep of both library roots, Mathlib and the DAG found no
existing statement of the generic normalization formula.

Change record:
coord/changes/formalFunctions_degreeZero_augmentation_compatibility-proof-scope.md.


## Second reading by V1

1. Compared the delivered main module with the repository using diff and checked
   its existing theorem signature byte for byte: identical. Its only public import
   remains FormalFibreCohomology. The additional imports are proof-only, including
   import all SystemIso. No existing definition or visibility changed. The change
   record accounts for the local elaboration settings and instance registration.
2. Compiled both delivered modules in import order with lcompile.py: clean.
   A scratch copy with #print axioms showed only propext, Classical.choice,
   Quot.sound and sorryAx for both public theorems. The canonical zeroIso and
   levelIso have only the three allowed axioms. levelIso_naturality inherits
   sorryAx from existing upstream dependencies: this delivery does not establish
   an axiom-free final result. The only delivered sorry is the named public
   formalFunctions_degreeZero_augmented_sections theorem, with its whole proof
   exactly by sorry. No forbidden declaration or hollow definition is present;
   the tensor adjunction is fixed by its adjunction property, and the constructed
   system isomorphism is not selected from an unconstrained existence theorem.
3. Read IsFormalFunctionsTheta, RestrictedResolutionSections,
   FlatBaseChangeOpenChoices, resolutionSectionClass, the existing open-choice
   construction, and the zero-augmentation square. Read the sandbox copy of
   cohomology.tex at lemma-cohomology-of-open (01E1),
   lemma-describe-higher-direct-images (01E4), and remark-explain-arrow (01FB).
   The new theorem has no inverse-system existence or transition assertion:
   it isolates the section-class normalization and augmented h-map equation.
   Its source and complete docstring argument apply to arbitrary modules.
   Restricting resolutions preserves injectives only along open inclusions;
   nothing here assumes the infinitesimal closed immersion is flat. The pinned
   augmentation and section components prevent arbitrary resolution choices
   from changing the class. For zero modules/sections and empty fibres both
   sides vanish; V=top and n=0 require no extra assumptions. The argument also
   applies to nonflat fibre projections. Independent LeanFinder search for
   derived direct image degree zero section class augmentation naturality found
   InjectiveResolution.toRightDerivedZero'_naturality and related generic
   resolution lemmas. Loogle on toRightDerivedZero and NatTrans.app found the
   generic augmentation isomorphism and toRightDerivedZero_eq lemmas. Neither
   closes the sheafification/section-class calculation directly. Searched both
   library roots and the upstream checkout for theta, augmented germs and
   resolutionSectionClass; no duplicate or short replacement was found. The
   remaining calculation is not a few-minute closure. Verdict: a genuine
   decomposition with one strictly smaller hole, not a renamed target proof.
4. Read the main proof from the constructed b downward: canonical components
   and transition naturality assemble b, the new formula handles theta, then
   inverse-hom cancellation, morphism naturality and the tensor-unit equation
   give appLE. These are real proved reductions. The proof imports are minimal
   for this route and the report correctly claims no whole-module pruning.
   The exact original proof_deps no longer directly needed are
   lem-weil-pbc-left-exact-injective-resolution-degree-zero,
   lem-weil-pbc-module-cohomology-fmap-basic-properties, and
   lem-weil-pbc-higher-direct-image-presheaf. They remain needed transitively
   by SystemIso or the split theorem's proof plan. The retained direct node
   lem-weil-pbc-module-pullback-structure-sheaf supplies the final unit equation.
   Read sk-thm-p1.json: its realized statement and steps are unchanged; this
   calculation lies below those steps and bypasses none of them.
5. Checked both node Lean statements against their files: verbatim matches.
   The original node's proof and proof_deps describe the imported canonical
   components, generic formula, and final unit transport as implemented.
   Its only changed fields are proof, proof_deps and proof_origin. The new
   node has source, statement dependencies, all proof steps and their union,
   proof_origin, recorded searches, split status, creation and blueprint data,
   chapter/unit and the matching Lean record. Verdict: nodes agree with Lean.

Second-reading changes: clarified inherited upstream sorryAx in this report,
listed the exact removed direct dependency node IDs, and added this review.
No Lean proof or signature needed repair. The accounting remains one original
hole closed, one hole added, net zero; no module pruned from target closure.
