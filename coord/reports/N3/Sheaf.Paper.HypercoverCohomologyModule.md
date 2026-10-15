## What changed

Proved AlgebraicGeometry.hypercover_cohomology_module_part with its original signature,
including arbitrary Ring R and all universes. The proof constructs a natural cocone
through the section bicomplex of an actual injective resolution. Injective rows identify
its total cohomology with derived terminal sections; the canonical derived-functor
comparison identifies that functor with the stated etale cohomology. Finite refinements
supply representatives and kill kernels. A direct module argument proves the colimit
universal property, including linearity and uniqueness. Dualized Mathlib simplicial
chain homotopies prove invariance under refinement homotopy.

Five new modules contain proved parts of this argument: HypercoverResolutionModel,
HypercoverInjectiveModuleRow, HypercoverRefinementSectionLifts, HypercoverBottomRefinement
(all in Sheaf.Paper), and
Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing. The bottom-row proof
contains the complete finite descending cochain induction, not a deferred descent
assertion. It treats representatives and bounding cochains, proves the unique final
kernel lift, and transports both calculations through the signed transposition of the
bicomplex. Degree zero, empty coproducts, the empty base and zero coefficients are included.

The two adapted modules were unclaimed. EtaleConstantRingModuleEquivalence has the
same twelve constructions and proofs with its unnecessary CommRing binder generalized
to Ring. The already proved RingedHypercoverInjectiveAugmentation free-module proof
moves to the new arbitrary-ring module; its original theorem retains its exact public
signature and public imports as a specialization. This relocation supplies a reusable
proved theorem and follows the one-new-statement-per-new-module requirement. It is not
a performance split. Existing callers require no edits. No target or definition used
by a target changes meaning.

The explicit resolutionDoubleComplex is irreducible after its proved API is established,
preventing instance search in downstream proofs from expanding its full construction.
All new objects are actual functor, chain-map, kernel or total-complex constructions;
no arbitrary data is chosen from an unproved mere existence statement.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.hypercover_cohomology_module_part
(node thm-weil-pbc-hypercover-cohomology-module-part).

Added zero holes. Every delivered Lean module has zero sorry. In particular the new
public lemmas bottom_refinement_descent, exists_refinement_lifting_sections,
exists_refinement_primitive, injective_module_row_quasiIso and
CategoryTheory.ringedHypercover_injective_augmentation_exact_ring are proved, as are
all comparison and refinement identities in HypercoverResolutionModel. No unfinished
intermediate theorem remains. This is a proof from existing project declarations,
not a claim that every dependency in its import closure is already axiom-free.

The existing Sheaf.Paper.FiniteSplitHypercoverRefinement declarations
exists_and_cofiltered and exists_refinement_solving_local_requirements are used as
stated dependencies. The current repository has a proof of exists_and_cofiltered;
exists_refinement_solving_local_requirements remains open. This delivery changes neither.
The first-quadrant augmentation and explicit total-complex support API are reused
from already proved library modules. No new descent assumption is introduced.

Validation: all eight delivered modules compile together through lcompile.py --all.
The unchanged direct callers of the generalized interfaces are checked separately.
The final deliver3.py --no-push result is recorded by the delivery tool.

## No longer needed

Removed direct proof imports from the item:

- Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives;
- Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist;
- Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful;
- Sheaf.Paper.HypercoverFreeResolution;
- WeilConjectures.AlgebraicGeometry.HypercoverFreeResolution;
- WeilConjectures.Mathlib.Algebra.Homology.TotalComplex (the new model imports this
  infrastructure where its actual total-complex constructions need it).

The original commutative wrapper also no longer needs the following plain imports
itself. They move with its private proof to RingedHypercoverInjectiveAugmentationRing,
where they remain required; this relocation does not prune them from the import closure:

- Mathlib.LinearAlgebra.Finsupp.LinearCombination;
- Mathlib.AlgebraicTopology.AlternatingFaceMapComplex;
- Mathlib.Algebra.Category.Grp.FilteredColimits;
- Mathlib.CategoryTheory.Adjunction.Additive;
- Mathlib.CategoryTheory.Sites.Equivalence;
- Mathlib.Algebra.Homology.ShortComplex.Exact;
- Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono;
- Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels;
- Sheaf.CategoryTheory.RingedHypercoverFiniteCones.

The following original planned proof obligations are no longer required by this proof:

- lem-weil-pbc-hypercover-free-resolution, including the planned
  Sheaf.Paper.HypercoverFreeResolution route;
- lem-weil-pbc-module-sheaves-enough-injectives and
  Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives (use the existing actual Mathlib
  injectiveResolution instead);
- prop-weil-pbc-kinjective-resolutions-exist and
  Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist (the existing derived compatibility
  theorem supplies the canonical identification);
- lem-weil-pbc-module-sheaves-colimits-forgetful and
  Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful (the module universal property
  is proved directly);
- thm-sp-double-complex-spectral-sequences (no spectral-sequence theorem is invoked;
  the actual total-complex infrastructure remains needed);
- lem-weil-pbc-abelian-sheaf-epi-locally-surjective and
  lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective (use Mathlib's module-sheaf
  local-surjectivity criterion directly).

These are pruned dependencies of this item; other parents may still use them.
The finite-split-refinement node remains necessary both for common refinements and
for solving the actual local primitive requirements. No unit-level proof step is
bypassed: sk-prop-h2 has no realized statement or proof-step node for these discarded
subordinate choices. Unused imports were removed from the new arbitrary-ring
augmentation module; the original wrapper's public imports remain identical. The second
reading also made FiniteSplitHypercoverRefinement a plain proof import in the new
HypercoverRefinementSectionLifts module, publicly importing only the defining
FiniteSplitEtaleHypercover module for the hypercover types.

## Where the brief, the DAG or earlier work was wrong

The target assumes only Ring R, whereas the planned constant-ring realization and
available ringed augmentation theorem imposed CommRing. Neither explicit construction
uses commutativity. The first interface was generalized with the same bodies; the
second was proved in arbitrary-ring generality while keeping its old specialization.
The affected node's statement_change records the stronger interface and every existing
DAG citer. Their commutative specializations remain identical.

Solving a lifting sieve only on constituent pieces is insufficient for subtracting
a total-complex boundary: a primitive on the whole refined term is required.
HypercoverRefinementSectionLifts proves the missing passage by constructing the
scheme disjoint union, identifying its colimit cofan, and gluing via the sheaf axiom.
No compatibility among distinct disjoint constituents is assumed.

No statement is disputed. No existing target signature changes. No adaptations to
modules held by another group are included. The node proof plans are updated to
match the chain maps, finite induction and universal property actually proved.

## New nodes

lem-sc-hypercover-resolution-comparison records the explicit section bicomplex,
augmentations and natural/refinement-compatible derived comparison in
Sheaf.Paper.HypercoverResolutionModel. All constructions and identities are proved.

lem-sc-ringed-hypercover-injective-augmentation-ring records the proved arbitrary-ring
generalization in Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing.
The original commutative theorem applies it without changing its public signature.
Change record: coord/changes/N3-hypercover-ringed-augmentation-ring.md.

lem-sc-hypercover-injective-module-row records injective-row acyclicity over any ring
in Sheaf.Paper.HypercoverInjectiveModuleRow. It realizes the constant module sheaf on
an equivalent small site and uses the proved ringed augmentation. The constant-ring
interface generalization is recorded in
coord/changes/N3-hypercover-arbitrary-ring-realization.md.

lem-sc-hypercover-refinement-section-lifts records simultaneous whole-term section
lifting and primitives for exact short complexes in
Sheaf.Paper.HypercoverRefinementSectionLifts. These follow from the existing finite
refinement theorem, explicit disjoint-union gluing and preservation of kernels.

lem-sc-hypercover-bottom-refinement-descent records both representation and local
kernel killing for the actual bottom inclusion in
Sheaf.Paper.HypercoverBottomRefinement. Its complete Lean proof uses finite cochain
corrections, the unique degree-zero kernel lift and homology representatives; no
further split-off is left. Mathlib searches (including unavailable-service results)
are recorded from the actual search log in each new node.

## Second reading by N3

1. **Existing interfaces — pass.** Compared all eight delivered files with the shared
   repository by diff. The two existing theorem signatures
   `AlgebraicGeometry.hypercover_cohomology_module_part` and
   `CategoryTheory.ringedHypercover_injective_augmentation_exact` are byte-identical.
   The only existing declaration-type change is the recorded CommRing-to-Ring section
   binder in EtaleConstantRingModuleEquivalence: all twelve declaration texts and bodies
   otherwise match. The moved free-module proof differs only in its theorem name, ring
   sheaf binder and the corresponding local `S := R`. The original commutative theorem
   remains its exact specialization. Both adapted modules are unclaimed. Read both new
   change records and the landed ringed proof-scope record. Checked all named callers:
   InjectiveEtaleConstantRingModule, EtaleModuleSheavesGrothendieckAbelian and
   ProEtaleHypercoverInjectiveRow; no statement acquires a new hypothesis or loses a
   conclusion. No target statement or target-defining construction changes.

2. **Proofs and objects — pass.** Independently compiled the eight-file set with
   lcompile.py. No delivered file contains a proof hole or a forbidden declaration;
   all lines satisfy the width bound. The scratch axiom probe checks the item, both
   ringed theorems, the coefficient equivalence, both section-lifting theorems, row
   acyclicity, bottom descent, and every named public resolution-model construction
   and identity. Resolution-model declarations, row acyclicity and both ringed
   theorems use only propext, Classical.choice and Quot.sound. The item, bottom descent
   and section lifting additionally use sorryAx through the existing finite local
   refinement dependency; no new sorry is introduced. Reviewed the actual bicomplex,
   augmentations, preserved-kernel lifts, signed total flip and module universal
   property. Every chosen representative is used inside a proof. Every new defined
   object is constructed explicitly, or inverts a proved isomorphism; no definition
   chooses arbitrary data from an unproved existence assertion.

3. **New statements and small cases — pass.** No statement is split off with sorry.
   Read all five new nodes against their Lean declarations and proofs. Whole-term
   lifting uses a genuine disjoint-union cofan, with separatedness handling the empty
   family and distinct-component overlaps. Bottom descent performs the finite
   decreasing-resolution-degree induction twice, for cocycles and bounding cochains;
   the q=0 kernel case is separate, and the final kernel lift uses monicity. The
   scalar arguments use left modules over Ring, including the zero ring. Empty bases,
   empty constituents, no requirements, and degree zero require no nonempty-family
   hypothesis. The resolution comparison is conditional on row acyclicity, discharged
   by the independently proved injective-row theorem. It is strictly a comparison
   construction, not a restatement of the colimit theorem.

4. **Route and pruning — pass after import/report repair.** Read the defining
   IsCohomologyColimit and its cohomology/refinement maps. The final proof establishes
   its homotopy invariance, natural cocone, refinement identities and pointwise
   universal property, including R-linearity and uniqueness. Fresh leanfinder, loogle
   and grep searches use different queries from the first worker; they found sheaf
   cohomology presheaves and one-hypercover sheaf conditions, not this all-degree
   comparison. Homotopy.homologyMap_eq is already used. Searched lean/Sheaf and
   lean/WeilConjectures for alternative comparison, descent and caller declarations.
   Inspected SiteCechEdgeNormalization: it concerns the ordinary Cech complex with
   supplied augmentation data, so it does not replace the constructed arbitrary
   hypercover argument. Read Stacks Tag 01H0 at
   https://stacks.math.columbia.edu/tag/01H0; the finite refinement corrections implement
   its comparison argument directly on the resolution bicomplex. All seven removed
   original proof-dependency nodes are listed in No longer needed. Added the omitted
   upstream HypercoverFreeResolution import to that list. The sk-prop-h2 realized
   statement and step lists are empty; none of these discarded auxiliary choices
   realizes a prescribed unit step. The unit record is untouched.

5. **DAG and provenance — pass after metadata repair.** Checked every new node has
   its source, origin, three search kinds, creation/blueprint data, chapter/unit and
   verbatim Lean attachment. Checked the proof_deps of all eight node records are
   exactly the union of their proof-step uses. The main node uses resolution
   comparison, injective rows, bottom descent and finite common refinements; the
   bottom node uses local section primitives, and the original ringed node now uses
   its arbitrary-ring specialization. The changed constant-ring statement records
   its old statement and all four existing DAG citers, whose commutative uses still
   hold. Changed the five substantial free-module/cone/sheafification/duality steps
   of the new arbitrary-ring augmentation node from elementary to non-elementary;
   their proofs are present and their dependencies are unchanged.

Changes made by this reading: made FiniteSplitHypercoverRefinement a proof-only
import in HypercoverRefinementSectionLifts and publicly imported its defining
FiniteSplitEtaleHypercover module; completed the removed-import list; corrected the
report's stale claim that exists_and_cofiltered itself is still a hole; corrected
the new ringed node's elementary flags. A trial removal of the Proetale proof import
failed because it supplies subcanonical_smallEtaleTopology, so that needed import
is retained. No mathematical proof or statement needed repair. Closed one original
hole, added zero holes, and left zero split-off statements.

Validation after the review: all three unchanged direct callers compiled independently
against the delivered interfaces (9.3 s, 3.8 s and 58.1 s respectively for
EtaleModuleSheavesGrothendieckAbelian, InjectiveEtaleConstantRingModule and
ProEtaleHypercoverInjectiveRow). The second-reader deliver3.py --no-push passed all
compilation, axiom probes and preflight, with review class CODEX. The final report
also enumerates all nine relocated wrapper proof imports; no proof source changed
after that successful dry run.
