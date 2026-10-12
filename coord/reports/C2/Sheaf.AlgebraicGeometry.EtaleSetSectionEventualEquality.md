## What changed

Completed a finite affine-cover reduction of
AlgebraicGeometry.etaleSetSectionEventualEquality, preserving its signature.
The main proof restricts the two sections to each member of a finite affine cover,
uses affine eventual equality, chooses a common cofiltered lower bound including
both original stages, and combines comparison composition with restriction
naturality and sheaf separatedness. The empty cover is handled by the same proof. Edge cases checked: the empty
object/cover, identity restrictions, and arbitrary (not necessarily affine)
morphisms in the restriction-naturality theorem.

Added three modules, with matching nodes:
EtaleSetSectionAffineEventualEquality, EtaleSetSectionComparisonNaturality,
and EtaleFiniteAffineRestrictionDetection. The finite-cover detection theorem
has a complete proof and compiled without warnings through lcompile.py.
The main module and all three new modules compile through lcompile.py.
Restriction naturality is proved by forming the composite of four whiskered
natural transformations and applying its naturality equation. The earlier missing
comparison artifact is now available in the shared build; no dependency copy is
included in the delivery. Typed explicit choices replace the expensive choose
tactic; the final main proof compiles in about 41 seconds under the 60-second limit.

## Proved and sorry left

Compiled and proved AlgebraicGeometry.etale_finite_affine_restriction_detection
(node lem-weil-pbc-etale-finite-affine-restriction-detection).

Compiled and reduced AlgebraicGeometry.etaleSetSectionEventualEquality
(node lem-weil-pbc-sets-section-eventual-equality) to affine eventual equality
and the existing comparison laws, using the two proved helpers.

Compiled and proved AlgebraicGeometry.etaleSetSectionComparison_naturality
(node lem-weil-pbc-sets-section-comparison-naturality).

Named sorry theorems added:

- AlgebraicGeometry.etaleSetSectionAffineEventualEquality
  (lem-weil-pbc-sets-section-affine-eventual-equality): only the affine case,
  with the site/section comparison and filtered-colimit argument still to prove.

Hole accounting: the existing hole AlgebraicGeometry.etaleSetSectionEventualEquality
is closed syntactically, and one new hole
AlgebraicGeometry.etaleSetSectionAffineEventualEquality is added. This is a
decomposition (net zero holes), not an axiom-free proof of the original item.
The finite-cover descent and restriction-naturality parts are fully proved.

No sorry occurs inside a definition or an anonymous/private helper.
The existing etaleSetSectionComparisonLaws dependency remains sorry upstream.

## No longer needed

Removed direct proof imports from the main module:
Sheaf.AlgebraicGeometry.AffineEtaleInverseImageComparison,
Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit,
Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings,
Sheaf.AlgebraicGeometry.LimitAffineTransition,
Sheaf.CategoryTheory.ColimitSiteSections,
Mathlib.CategoryTheory.Limits.Connected,
Mathlib.CategoryTheory.Sites.Equivalence,
Mathlib.CategoryTheory.Sites.EqualizerSheafCondition,
and Sheaf.AlgebraicGeometry.FullAffineEtaleTopos.

The affine inverse-image comparison, affine-site colimit, limit affineness,
colimit sections, affine-site equivalence, connected constant-diagram colimit,
and site-equivalence transport are still needed by the new affine-case node;
this is dependency relocation, not global pruning of those nodes.
The cofinal-finite-coverings node
lem-weil-pbc-etale-qcqs-cofinal-finite-coverings and its module
Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings are not needed by this
route: the finite restriction-detection helper proves exactly the finite affine
open-cover and separatedness facts using existing Mathlib/upstream declarations.
No claim is made that other users no longer need that node.

Complete accounting of the old main-node dependencies no longer used directly:

- lem-weil-pbc-affine-etale-site-colimit,
  lem-weil-pbc-affine-etale-site-topos,
  lem-weil-pbc-colimit-constant-connected-diagram,
  lem-weil-pbc-colimit-of-sites-sections,
  lem-weil-pbc-limit-affine-transition,
  lem-weil-pbc-sets-affine-etale-inverse-image-comparison, and
  lem-weil-pbc-site-equivalence-sheaf-transport move to the affine-case plan.
- lem-weil-pbc-pretopology-sheaf-condition moves to the proved finite-cover
  helper, whose proof uses the sheaf hom-ext consequence directly.
- lem-weil-pbc-etale-qcqs-cofinal-finite-coverings is no longer used on this
  route. The proof takes Mathlib's finite affine open subcover directly.
- lem-weil-pbc-sets-section-comparison-laws remains a direct dependency.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped because the comparison module source had landed
but its artifact was absent from the last green build. That artifact became
available during this repair. The previous proof draft also used the nonexistent
Finset.insert name and assumed a Subsingleton instance for Over hom sets. The
repair uses insert and Over.OverMorphism.ext with subsingleton underlying arrows.

The existing comparison-laws theorem states identity, composition, and cone
compatibility, but its docstring also describes restriction naturality, which
is not a clause of its signature. The new naturality node states that square.
The unit's realized statement/step remains untouched.

Read the Stacks etale-cohomology source from the available read-only copy at
/home/ubuntu/c1-stacks-review/etale-cohomology.tex, labels theorem-colimit and
lemma-colimit-affine-sites. The repository literature source is absent locally.
Mathlib searches are logged in searches.jsonl: LeanSearch was unavailable;
LeanFinder returned structure-sheaf statements, not the required etale assertion;
grep found the filtered-colimit equality and covering hom-ext tools used in this
route. Blueprint searches found no identical concrete section comparison lemma.

## New nodes

lem-weil-pbc-sets-section-affine-eventual-equality restricts the parent result to
an affine etale object and retains its affine-site/filtered-colimit argument;
it does not include finite-cover descent.

lem-weil-pbc-sets-section-comparison-naturality states and proves only the
restriction commutation square for a single section comparison.

lem-weil-pbc-etale-finite-affine-restriction-detection is proved: a finite affine
open cover detects equality of arbitrary sheaf sections after any base change.
It contains no inverse-limit or eventual-equality assertion.


## Second reading by C2

1. Unchanged interface: PASS. Compared the main module with the repository using
   diff and independently compared the original theorem signature byte for byte.
   Only its proof and private proof imports changed. No existing definition,
   declaration signature, public import, target, or unit record is changed;
   no change record is required. The three other modules are new statements.
2. Proof and trust: PASS as a decomposition. All four files compiled through
   lcompile.py without warnings. Scratch-copy #print axioms checks show only
   propext, Classical.choice and Quot.sound for
   AlgebraicGeometry.etale_finite_affine_restriction_detection and
   AlgebraicGeometry.etaleSetSectionComparison_naturality. The affine theorem
   and original theorem additionally use sorryAx, as expected from the named
   affine hole and the upstream comparison-laws hole. There is exactly one
   sorry in this delivery, in the public named affine theorem; no hollow
   definition or prohibited trust escape occurs. The original item is not
   claimed axiom-free.
3. Split statements: PASS. The affine case is true by the affine-site section
   colimit argument in Stacks 0EYL/09YN and compatible inverse-image units. It
   is strictly part of the original proof: it excludes finite-cover descent,
   which the main file implements. Its source, full proof docstring and node
   are present. Tested the argument on an empty object/empty cover, constant
   diagrams and coincident original stages: including j and k in the finite
   set guarantees the required arrows even with no local witnesses. The
   naturality helper applies to arbitrary restrictions and base morphisms;
   its four-factor natural transformation is exactly the defined comparison.
   The detection helper uses only separatedness, valid also for an empty
   covering and arbitrary base change. Independent searches used LeanFinder
   for injectivity of the affine limit-section comparison, Loogle for
   NatTrans.naturality, and grep for finiteSubcover, hom_ext_ofArrows and
   coverPreserving_overPullback. The structure-sheaf limit results returned
   by LeanFinder and the module/abelian section-colimit results in the library
   do not state the required set-valued comparison assertion. The general
   naturality lemma is already used directly. No duplicate concrete helper
   was found. The remaining affine proof is not a few-minute application:
   the concrete stage-to-limit identifications still need to be constructed.
4. Route and pruning: PASS after report clarification. Read the full main
   proof, its imported declarations and sk-thm-iff's realized field. The
   realized unit statement and step are lemma-weil-pbc-property-iff-acyclicity;
   neither is bypassed. The main proof restricts first, obtains affine
   witnesses, transports their equalities to one cofiltered lower bound,
   uses thinness of preorder arrows and comparison composition, and applies
   separatedness. The public imports are needed by the new signatures;
   main proof imports are private. FullAffineEtaleTopos and
   LimitAffineTransition are already public dependencies of the affine-site
   modules, so no redundant direct imports were added for them. Restored
   private Connected and Sites.Equivalence imports to the affine helper's
   retained proof plan. No simpler available set-valued theorem closes its
   affine hole.
5. DAG agreement: PASS after repair. The main node's four dependencies match
   the actual reduction. The new nodes carry the source, chapter, unit,
   blueprint provenance, creation record, searches and Lean declaration.
   Corrected the finite-cover node to name the actual finiteSubcover
   construction, the qcqs permanence lemmas, the proved upstream
   coverPreserving_overPullback and sheaf hom_ext_ofArrows. Removed its
   unused lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings dependency;
   replaced the generic covering-base-change dependency with
   lem-weil-pbc-etale-base-change-continuous, whose upstream declaration is
   the one used by Lean. Proof dependencies are the union of step uses.

Changes by the second reader: corrected finite-cover proof metadata, restored
 two private imports for the affine proof plan, explicitly counted the
 decomposition, completed the dependency relocation list below, and added
 this review. No mathematical proof or existing statement was rewritten.

