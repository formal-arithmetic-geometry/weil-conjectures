## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.AffineBasisLowerTailSectionsReconstruction
by a complete Lean reduction. Restrict the lower tail to V, obtain local bound zero,
apply truncation_isDerivedLimitTriangle_of_local_bound on V.toScheme, and apply
Scheme.rightDerivedFunctor_isDerivedLimitTriangle to abelian global sections.
The proved private helper map_product_lift identifies the first map by projections.
The proved private helper transport_roos_triangle constructs the product isomorphism,
checks its compatibility with 1 minus shift by projections, and transports the
boundary and distinguished triangle. The original theorem signature and all public
imports remain unchanged. Two new modules isolate the missing restriction comparisons;
their statements assert neither reconstruction nor the original conclusion.

The arbitrary derived universes wC and wA are retained. The auxiliary category on V
uses HasDerivedCategory.standard at universe u+1. Both presentations of its module
category receive the same localization instance. Sections preserve countable products
by the ordinary sheaf and presheaf evaluation instances. No data definition contains
sorry, and no data definition chooses an arbitrary witness from an unproved existence theorem.
The comparison lemma supplies isomorphisms used only within the proof of the original
existential boundary statement; compatibility alone need not uniquely determine them.

## Proved and sorry left

Closed: AlgebraicGeometry.affineBasisLowerTail_sections_reconstruction
(lem-sc-affine-basis-lower-tail-sections-reconstruction), the only original hole.
The two private categorical helpers are proved without sorry.

Added and left as named theorem holes:
- AlgebraicGeometry.affineBasisRestrictedLowerTail_local_bound
  (lem-sc-affine-basis-restricted-lower-tail-local-bound), in
  Sheaf.AlgebraicGeometry.AffineBasisRestrictedLowerTailLocalBound.
- AlgebraicGeometry.openDerivedSections_truncationTower_comparison
  (lem-sc-open-derived-sections-truncation-tower-comparison), in
  Sheaf.AlgebraicGeometry.OpenDerivedSectionsTruncationTowerComparison.

This is a decomposition: one original hole closed and two smaller holes added, net -1,
not a claim of a sorry-free proof. Each remaining hole has its source, complete argument
in its docstring, a new module and a node. The first is only the hypothesis needed by
the existing local-bound criterion, and the second is a comparison of functors and
canonical truncation maps independent of any acyclicity hypothesis.

## No longer needed

Removed direct proof imports:
- Sheaf.Algebra.Homology.KInjectiveRestrictOpen: needed by the comparison node, rather
  than by the combination proof itself; not globally pruned.
- Sheaf.AlgebraicGeometry.ModuleCohomologySourceComparison: replaced in the local-bound
  node's plan by Sheaf.AlgebraicGeometry.OpenModuleCohomologyComparison and its theorem
  nonempty_openModuleCohomology_addEquiv_restrict_H, which already includes the required
  restriction-to-open comparison. The parent no longer directly needs
  lem-sc-module-cohomology-source-comparison.

Retained the reconstruction and derived-functor comparison dependencies. No unit
statement or step is bypassed: sk-thm-picard-duality.realized has no realization here,
and this reduction follows the parent's three restriction/reconstruction/sections steps.
No further existing module is claimed to be globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The existing restriction lemma preserves K-injective complexes but does not itself
state the natural derived evaluation comparison or compatibility with truncation
projections and transitions. The old proof plan hid these comparisons. The source
comparison alone also does not provide the complete local-bound hypothesis for the
restricted lower tail. Those two pieces are now explicit statements. The remaining
combination is formalized, not hidden in a new reconstruction lemma.

Read the Stacks statements and proofs of Tags 0D64, 08BS and 08U1 on their official
pages, since literature/stacks-project is absent in this machine's read-only clone.
The module also follows the existing open-module-cohomology comparison (Tags 01E1,
03FD). LeanFinder and Loogle had no exact match; LeanSearch returned Internal Server
Error, recorded as unavailable. The blueprint searches for restriction truncation,
cohomological bound, lower truncation, K-injective restriction, derived sections, and
cohomology restriction found no duplicate of either new statement.

Edge cases checked mathematically: the empty V has the empty affine basis and zero
sections; zero F gives zero homology; arbitrary cutoff a gives the original homology
below a and zero otherwise. Both comparisons are valid for arbitrary unbounded
objects and do not introduce quasi-coherence, separatedness, or finite-dimensional
hypotheses. Affine opens inside V are sent to affine opens in X by the open immersion;
no intersection of affine opens is assumed affine. The second statement applies to
arbitrary opens, so its proof needs no affine hypothesis at all.

## New nodes

lem-sc-affine-basis-restricted-lower-tail-local-bound states the zero positive
cohomological bound on an affine basis of V for restriction of truncLT a QF. Its proof
uses exact restriction/homology, standard truncation cohomology, and the existing
open-module-cohomology/source-H comparison. This is the parent's local-bound input,
strictly prior to any reconstruction.

lem-sc-open-derived-sections-truncation-tower-comparison states objectwise derived
sections isomorphisms with the two canonical projection/transition compatibility
squares. Restriction preserves K-injectives and is exact; the underived sections
identity derives, and t-exactness gives the truncation comparison. It is independent
of the parent's vanishing hypothesis and conclusion. Its products and Roos-triangle
transport are proved in the parent module, not left in this node.

The parent node's proof and proof_deps now match this compiled combination. No
statement or definition was changed and no change record or forced adaptation is needed.

## Second reading by A4

1. Interface: diffed the existing module against the repository. The only existing
   public declaration, affineBasisLowerTail_sections_reconstruction, retains its
   signature byte for byte, including both derived universes and hhomology. All
   existing public imports remain unchanged; the two replacements are proof imports.
   There are no adapted existing modules, changed definitions, or change records.
2. Proof: independently compiled the parent and read both private helpers. The first
   uses product extensionality; the second transports the Roos triangle along e and
   Pi.mapIso en, checking 1-minus-shift by projections and the shifted boundary by
   inverse cancellation. No forbidden declaration or hollow definition occurs. The
   only textual holes are the two named public theorems listed above; the parent's
   result is a decomposition (one hole closed, two added), not an axiom-free proof.
   A scratch-copy #print axioms checks the parent, both helpers and both new theorems.
3. Split statements: the local-bound hypothesis is precisely p > 0 and q < 0 required
   by truncation_isDerivedLimitTriangle_of_local_bound at d = 0. Exact restriction,
   truncation homology, affine-open images and transitive restriction give its claim.
   The second statement compares derived sections, projections and transitions and
   is independent of the acyclicity hypothesis; it does not assert reconstruction.
   Checked empty V, zero F/E, all integer cutoffs (including a <= 0), and unbounded
   complexes. No quasi-coherence, separatedness, or affine-intersection assumption
   is used. Read Stacks 0D64, 08BS and 08U1 on their official pages. Independent
   LeanFinder/Loogle/grep queries and rg of the library found ingredients rather than
   duplicates. In particular the existing upstream mapDerivedCategoryTruncGEIso
   supplies the truncation comparison directly. Neither hole can be closed by a
   single existing theorem: restriction/sections transport still needs formalization.
4. Route and pruning: read the old proof_deps and both existing reconstruction and
   derived-functor theorems. The parent uses exactly the two retained dependencies
   and the two new lemmas. Both removed old dependencies are recorded under No longer
   needed; KInjectiveRestrictOpen is still needed by the comparison plan. The unit
   sk-thm-picard-duality has realized.statement = [] and realized.steps = [[]]; this
   item realizes no unit step and retains the restriction/reconstruction/sections
   route. No globally unreachable module is claimed without closure evidence.
5. DAG: compared all three statements with their Lean signatures, checked new-node
   source, searches, chapter/unit, created, blueprint and lean fields, and checked
   the parent's proof/proof_deps against each application in the proof. Verdict:
   valid decomposition, with two remaining strictly smaller obligations.

Second-reading changes: added plain proof imports of OpenModuleCohomologyComparison,
ExactFunctor and Embedding.CochainComplex to the local-bound module and of
KInjectiveRestrictOpen and ExactFunctor to the tower-comparison module, so their
stated proof dependencies are available to the next worker. Shortened the comparison
node's proof plan to use the already proved mapDerivedCategoryTruncGEIso and its
projection factorization. Corrected the report's claim that the comparison witnesses
are uniquely determined: they are only eliminated inside an existential theorem
proof. No existing signature, Lean proof, public import or hole count was changed
by the second reader.
