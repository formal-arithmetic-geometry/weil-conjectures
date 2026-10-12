## What changed

Proved AlgebraicGeometry.derivedGlobalSections_affinization_comparison with its original,
byte-for-byte signature. The private underived_comparison constructs the natural isomorphism
by cancelling scalar restrictions using Scheme.toSpecΓ_appTop. The derived proof verifies the
composite unit on K-injective complexes and applies uniqueness of right derived functors.

Added Sheaf.AlgebraicGeometry.GlobalSectionsDirectImageKInjectiveAcyclic, containing the proved
theorem AlgebraicGeometry.isIso_globalSections_restrictScalars_unit_on_directImage_kInjective.
After second reading, it reuses the existing
AlgebraicGeometry.isIso_directImage_globalSections_unit_on_kInjective, then applies exact
restriction of scalars. Its private unit_isIso_comp_of_exact proves the needed unit
invertibility using the existing exact-postcomposition derived-functor theorem and its
universal property. No existing interface, visibility or definition changes.
Both delivered modules compile without warnings using lcompile.py in import order.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.derivedGlobalSections_affinization_comparison
(lem-pc-derived-global-sections-affinization-comparison).
The new theorem AlgebraicGeometry.isIso_globalSections_restrictScalars_unit_on_directImage_kInjective
(lem-pc-global-sections-direct-image-kinjective-acyclic) is proved, not split off with sorry.
Holes closed: 1. Holes added: 0. No sorry remains in either delivered module.
The existing AlgebraicGeometry.isIso_directImage_globalSections_unit_on_kInjective remains open
in its upstream module, which this delivery neither changes nor duplicates. Axiom checks of
both public theorems show propext, Classical.choice, Quot.sound and sorryAx from existing
open dependencies. The two private helpers use only the three permitted standard axioms.
This is not a claim that the target is transitively sorry-free.

## No longer needed

Removed the direct proof import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
and the dependency lem-pc-ringed-spaces-derived-direct-image-composition from this item's route.
Removed the direct import Sheaf.AlgebraicGeometry.GlobalDerivedHom and the direct proof
 dependency def-pc-global-derived-rhom from the item's node; it remains transitively needed
through the existing direct-image global-sections acyclicity module and is not globally pruned.
These are all original proof_deps omitted by the new proof.
Added proof-only imports WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
and Sheaf.AlgebraicGeometry.GlobalSectionsDirectImageKInjectiveAcyclic to the item.
The new module imports DirectImageGlobalSectionsKInjectiveAcyclic and exact-derived-functor
compatibility only for its proof; its public imports supply the actual signature.
No unit statement or realized proof step is bypassed; sk-thm-picard-duality has empty realized
lists, and its route is unchanged. No claim of a globally pruned module is made.

## Where the brief, the DAG or earlier work was wrong

The first proof unnecessarily repeated the point-evaluation argument already encapsulated by
AlgebraicGeometry.isIso_directImage_globalSections_unit_on_kInjective. Second reading found
that theorem by a broader search and replaced the repeated argument with its application.
The original affinization plan is valid; the proof takes the composite-unit route below the
unit level. No false statement or interface repair was found, and module pushforward is never
assumed to preserve K-injectivity.

## New nodes

lem-pc-global-sections-direct-image-kinjective-acyclic records the scalar-restricted extension
of existing direct-image global-sections acyclicity. Exact restriction of scalars is its only
additional step. It is true for arbitrary coefficient-ring maps, including noninjective maps,
zero rings and empty schemes, and is strictly a part of the affinization proof.
Its module is lean/Sheaf/AlgebraicGeometry/GlobalSectionsDirectImageKInjectiveAcyclic.lean.
No change record is required: no existing public statement or definition was altered.

## Second reading by M2

1. Compared the existing module and its node with the repository using diff. The existing
   theorem signature, universe binders, hypotheses, conclusion, visibility and docstring are
   byte-for-byte unchanged. Only proof imports, a private constructed isomorphism, and the
   theorem body change. The other delivered module is new; no existing module is adapted.
2. Compiled both delivered files locally in import order without errors or warnings. Scanned
   both for sorry and forbidden declarations: none present. Scratch-copy #print axioms checks
   show only propext, Classical.choice, Quot.sound, and existing-dependency sorryAx in the two
   public results. The private isomorphism is constructed by restriction-of-scalars identities,
   with no arbitrary witness chosen from an unproved existence theorem.
3. No new statement is left with sorry. Read the new acyclicity statement, docstring and node;
   it adds exact scalar restriction to existing global-sections acyclicity and is sufficient
   for the composite-unit argument. Checked identity maps, zero complexes, empty schemes and
   zero/noninjective coefficient maps: no step assumes flatness or preservation of K-injectivity.
   Broader Lean-library/upstream searches found the existing acyclicity theorem, now reused.
   LeanFinder's eight hits concerned ordinary derived functors or K-injective localization;
   no exact scalar-restricted statement was found. Loogle and grep confirmed scalar restriction
   tools and no duplicate of this extension.
4. Read the proof from the item downward. Scalar cancellation followed by the K-injective
   unit criterion is a genuine reduction. Pruned the repeated point-space argument in the
   new module. Imports distinguish signature requirements from proof requirements, and the
   report lists every old proof dependency absent from the item's new route. Checked the unit
   realized fields and statement/steps: unchanged, with no unit-level bypass.
5. Compared both nodes with the final Lean. The item's steps match scalar cancellation,
   acyclicity and right-derived uniqueness. The new node now names precisely
   lem-pc-direct-image-global-sections-kinjective-acyclic as its proof dependency, followed by
   exact postcomposition; its Lean statement matches verbatim, and required new-node fields
   and search records are present.

Changes made in second reading: reused existing direct-image global-sections acyclicity;
removed unit_isIso_of_natIso and the duplicated point-space proof; replaced the new module's
public SchemeDerivedDirectImage import with signature-level Scheme and RingedSpaceDerivedDirectImage
imports; updated the new node's proof, proof_deps, proof_origin and search evidence; corrected
this report's dependency and axiom descriptions. The original theorem proof was retained.
