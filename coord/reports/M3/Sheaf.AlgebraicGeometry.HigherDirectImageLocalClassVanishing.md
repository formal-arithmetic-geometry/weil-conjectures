## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.exists_higher_image_local_class_eq_zero`
with a complete proof from two strictly smaller raw-cohomology statements. The original
signature and docstring are unchanged. The proof constructs the sieve of eventual zero
restrictions, lifts sections locally through the proved module cohomology-presheaf
comparison, refines by local injectivity at the limit and affine open covers, applies raw
cohomology continuity, and uses restriction naturality and topology transitivity.

Added `HigherDirectImageRawOverNaturality.lean`: its raw pullback is explicitly constructed
from inverse-image composition, the single-functor comparison, derived pullback, shift
comparison and coefficient identification. Its theorem compares this construction with
canonical higher-image transitions and restrictions. Added
`HigherDirectImageRawAffineClassVanishing.lean` for eventual vanishing of raw classes whose
raw limit image is zero. Neither new statement claims local eventual zero of arbitrary
higher-image sheaf sections. No definition chooses data from an unproved existence theorem.

Updated the original node's proof, proof dependencies and proof origin to match the Lean
argument. Added two corresponding nodes with exact Lean signatures and complete proof plans.
All files remain module files. New public imports are confined to the new modules and are
needed by their signatures; the original module's new imports are proof-only.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.exists_higher_image_local_class_eq_zero`
(node `sbc-lem-higher-image-local-class-vanishing`). Its combining proof has no sorry.

Added two holes, each exactly a named public theorem with `by sorry`:

- `AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_toSheaf`
  (node `sbc-lem-higher-image-raw-over-naturality`): compatibility with canonical transitions
  and restriction, for one morphism over W without any inverse-limit hypotheses.
- `AlgebraicGeometry.Etale.exists_higher_image_raw_affine_class_eq_zero`
  (node `sbc-lem-higher-image-raw-affine-class-vanishing`): eventual zero in raw cohomology on
  an affine object, assuming raw cohomology already vanishes at the limit.

This is a decomposition: one original hole closed and two smaller holes added, not a
sorry-free proof of geometric continuity. The data construction has no sorry. Edge cases
checked mathematically: arbitrary commutative rings including the zero ring; q=0; negative
q, where degree-zero sheaf cohomology vanishes; empty etale objects; and cofiltered
categories with parallel arrows rather than only directed posets. The naturality statement
also applies to identity morphisms and zero classes. The covering-sieve proof uses no finite
subcover or common later stage.

## No longer needed

Removed direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
- `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit`
- `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`
- `Sheaf.AlgebraicGeometry.HigherDirectImageOverCoherence`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The original node no longer directly uses
`sbc-lem-higher-direct-image-presheaf`,
`sbc-lem-higher-image-over-transition-coherence`,
`lem-weil-pbc-sheaves-colimit-sheafification`,
`lem-weil-pbc-filtered-category-exists-directed-final`,
`lem-weil-pbc-colimit-constant-connected-diagram`,
`lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-injective-module-abelian-acyclic`, or
`lem-weil-pbc-etale-cohomology-limit-complex-systems`.
The last five are still needed below the new raw-continuity/naturality nodes; their
removal here does not claim they are globally unreachable. Ordinary sheaf colimit
sheafification and abstract abelian higher-image comparisons are unnecessary for this
local argument: it uses the already proved fixed module-valued raw comparison.
Canonical transition composition is unnecessary because the raw witness is obtained
at the original stage, and the final assembly uses only restriction naturality.

Deleted the prior attempt's unaccepted duplicate
`HigherDirectImageAffineLocalClassVanishing.lean` and node
`sbc-lem-higher-image-affine-local-class-vanishing` from the sandbox. They are not
repository deletions or retained dependencies of this delivery.

## Where the brief, the DAG or earlier work was wrong

The previous attempt isolated an affine sheaf-section theorem with the same signature as
`exists_higher_image_affine_class_eq_zero`, which already depends on this item. It also
lacked a full docstring proof, exact node signature, recorded searches, route update and
actual pruning. Reusing that reduction would duplicate an existing obligation. The repair
instead separates raw cohomology continuity from naturality, and proves all local
sheafification and sieve assembly in the original module.

The original DAG cited an abstract abelian presheaf identification. The source library
already proves local bijectivity of the fixed module-valued comparison, which is exactly
what this proof needs (node `sbc-lem-module-higher-image-raw-comparison-locally-bijective`).
The unit `sk-lem-failure-field` has no realization attached to this auxiliary node, and its
higher-image-continuity step is preserved. No target statement or unit route changes.

Read Stacks Tags 09Z1 (`lemma-relative-colimit`), 03Q8 (`lemma-higher-direct-images`),
0EZM (`lemma-colimit-variant-complexes`) and 03FD (`lemma-cohomology-modules-abelian`).
Mathlib searches and repository searches found structure-sheaf limit lemmas and the
abelian directed-system variants, but no exact raw module-cohomology vanishing bridge.
Blueprint searches for raw cohomology and natural higher direct images found no matches.

## New nodes

`sbc-lem-higher-image-raw-over-naturality`: the two naturality squares for the explicitly
constructed raw pullback. It has no limit hypotheses, eventual-stage assertion or
covering-sieve conclusion. Source: Tags 03Q8 and 09Z1, with the unit/counit computation
spelled out in its proof and declaration docstring.

`sbc-lem-higher-image-raw-affine-class-vanishing`: injectivity of cohomology continuity
expressed as eventual zero of a raw affine class. The limit-zero hypothesis is in raw
cohomology, so it cannot be applied directly to the original sheaf section. The main proof
supplies that hypothesis through two nontrivial local refinements. Source: Tags 09Z1,
0EZM and 03FD. No change records or forced adaptations are needed.

Validation: the three-file sandbox compiles without warnings (20.0 s, 5.6 s,
57.0 s respectively). The canonical raw presheaf/comparison abbreviations prevent
repeated expansion of their derived-category constructions. Their data is unchanged.

## Second reading by M3

1. Interface preservation: compared every delivered module with the repository. Only the
   original module already exists; its sole declaration's signature and existing docstrings
   are byte for byte unchanged. Its edits are proof imports and the proof body. The two raw
   modules are new. No existing definition, target, instance, or statement is changed; no
   change record or forced adaptation is needed. Verdict: pass.
2. Proof and data: independently compiled all three files in dependency order, without
   warnings (19.1 s, 5.1 s, 48.9 s). Read the local-surjectivity, local-injectivity, affine-cover
   and downward-closure arguments. The only direct holes are the two public named theorems
   listed above. Explicit `#print axioms` checks of all six delivered declarations show only
   propext, Classical.choice and Quot.sound for the three raw data constructions, and those
   plus sorryAx for the three theorems. No forbidden declarations or arbitrary witnesses
   chosen from unproved existence occur. Verdict: pass as a decomposition, not a closed
   geometric-continuity proof.
3. Split statements: checked the raw pullback's factor directions against the transition
   definition and the fixed upstream comparison. Its naturality square follows by derived
   adjunction naturality and triangle identities; restriction is precomposition and commutes
   with these factors. Raw eventual zero is the injective half of cohomology continuity on
   the affine base change. Read Stacks Tags [09Z1](https://stacks.math.columbia.edu/tag/09Z1),
   [03Q8](https://stacks.math.columbia.edu/tag/03Q8),
   [0EZM](https://stacks.math.columbia.edu/tag/0EZM), and
   [03FD](https://stacks.math.columbia.edu/tag/03FD). Checked zero rings, zero classes, identity
   arrows, degree zero, negative degrees, empty objects and non-posetal cofiltered indices: no
   counterexample or missing hypothesis found. Both statements have sourced proof docstrings
   and matching nodes, and are strictly parts of the original argument. New searches with
   different wording found no exact Mathlib replacement. Repository raw-affine representation
   lemmas supply surjectivity, and the upstream comparison naturality theorem changes
   coefficients at a fixed morphism; none duplicates either new statement. Verdict: pass.
4. Route and pruning: the main proof uses the already proved fixed module comparison and
   elementary topology operations before invoking the two remaining raw obligations. All
   five removed imports and all eight old proof dependencies are recorded in No longer
   needed. Public imports of the new modules are needed by their signatures/data; main
   proof-only imports are plain imports. The raw affine module retains proof-plan imports
   for its open continuity argument. The unit sk-lem-failure-field realization is empty for
   this auxiliary node and is unchanged; its higher-image-continuity route is retained. No
   globally unreachable module is claimed without an import-closure check. Verdict: pass.
5. Nodes: checked the original node diff is confined to proof, proof_deps and proof_origin;
   its three dependencies match the implemented assembly. Each new node has the required
   source, searches, creation, blueprint, chapter, unit and Lean record, with the exact
   displayed theorem signature; proof_deps equal the union of proof-step uses. Verdict: pass.

Second-reading changes: removed extra blank lines and trailing whitespace from the main
proof, and appended independent, differently worded searches and their concrete verdicts
to both new nodes. No mathematical proof or statement needed repair. The two substantial
raw obligations cannot be closed by a short existing lemma found in this review.
