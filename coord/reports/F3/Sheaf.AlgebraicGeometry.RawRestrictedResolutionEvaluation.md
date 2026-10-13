## What changed

Proved `AlgebraicGeometry.Etale.RawRestrictedComparison.rawRestricted_resolution_evaluation`
from one strictly smaller source-normalization statement, in the new module
`Sheaf.AlgebraicGeometry.RawRestrictedSectionsUnitZero`. The original signature and
`resolutionSectionsIso` definition are unchanged. Added a proof-only import of the new module. The new module also imports the proved
bounded-below normalization privately for its remaining proof plan.
The new `sectionsUnit` is an explicit construction from the right-derived unit and localization
comparisons, with no chosen witness. Three private lemmas prove its naturality and its inverse
relationship with the resolution comparison. The final proof applies zeroth homology, uses
homology localization naturality, and evaluates an equality of additive morphisms at the generator.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Etale.RawRestrictedComparison.rawRestricted_resolution_evaluation`
(node `lem-sbc-raw-restricted-resolution-evaluation`): no sorry remains in the item.
Added one hole `AlgebraicGeometry.Etale.RawRestrictedComparison.sectionsUnit_zero`
(node `lem-sbc-raw-restricted-sections-unit-zero`). This is a decomposition, with net holes 0,
not a complete axiom-free proof of the item. The remaining statement only normalizes the
comparison for an arbitrary single sheaf; it has no chain map, target complex, resolution,
K-injectivity hypothesis, represented free sheaf, or generator.

## No longer needed

No existing import or module can be removed: the homotopy-sections module supplies
`underivedSingleIso`, `chainEvaluation`, and `underivedSections`; the K-injective module
supplies `rightDerivedFunctorObjQIso` used in the existing public definition.
The theorem `exists_rawRestrictedHomotopySectionsIso` itself is not used, and no proof of
that theorem is needed for this evaluation compatibility. Its module remains necessary
for its concrete definitions. No other DAG node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's claim that the degree-zero normalization follows directly from naturality hides
compatibility between the classical derived functors and the total right derived functor.
The two interfaces are connected by `homologyRightDerivedFunctorObjSingleFunctorIso`, whose
construction runs through the bounded-below functor and chosen injective resolution. This
is the precisely isolated remaining task. No mathematical statement was changed or disputed.
The unit record `sk-lem-failure-field` has empty realized lists, and its route is unchanged.

The first searches found classical degree-zero comparison and injective-resolution formulas.
Second-reading local searches additionally found a proved bounded-below normalization
`rightDerivedPlusSingleUnitHomology_comp_comparison` and the module-direct-image theorem
`canonicalDirectImageH0Unit` with private generic transport calculations. Neither states
the total-derived comparison with etale restriction. The remaining proof plan now reuses
the bounded-below normalization instead of repeating its injective-resolution calculation. LeanSearch returned HTTP 500 (recorded unavailable),
LeanFinder returned eight classical-comparison hits, and grep returned five defining-formula
hits. Read Stacks Tags 072W, 0BKV, and 0D6F online because their local TeX is absent. They
justify the injective-section computation; the explicit comparison-normalization glue is
identified as agent-supplied. Checked zero sheaves, zero chain maps, zero target complexes,
and empty etale objects: the proof is natural-transformation algebra with no exclusions.

## New nodes

`lem-sbc-raw-restricted-sections-unit-zero`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-raw-restricted-sections-unit-zero.json`, records the
single-sheaf normalization and its explicit `sectionsUnit` construction. Its proof explains
the augmentation-into-cycles computation and compatibility of bounded and unbounded units.
No definition or statement of an existing module changed; no change record or forced
adaptation is needed.

## Second reading by F3

1. Compared the delivered item with the repository source. The signatures of
   `resolutionSectionsIso` and `rawRestricted_resolution_evaluation` are byte-identical,
   and the entire definition body of `resolutionSectionsIso` is byte-identical.
   The existing theorem docstring is unchanged. The only additions in the item are
   a proof-only import, three private proved helpers, local elaboration options,
   and the proof replacing the original sorry. No target, definition, hypothesis,
   conclusion, or existing public visibility changed. Verdict: pass.
2. Compiled both modules locally, in import order: no errors or warnings (10.7 s
   and 49.0 s before the documentation/import correction). Scanned both modules:
   the only direct sorry is the named theorem `sectionsUnit_zero`; no axiom,
   unsafe, opaque, implemented_by, extern, or hollow definition. Compiled a scratch
   copy with explicit `#print axioms` for both definitions, the original theorem,
   the new theorem, and all three private helpers. The definitions and private
   helpers use only propext, Classical.choice, and Quot.sound. The two public
   theorems also use sorryAx, accounted for by the one remaining normalization
   hole. This is a decomposition, not an axiom-free completion. Verdict: pass.
3. Read the new statement, its explicit unit construction, docstring and node.
   Its sole remaining task is source normalization for an arbitrary sheaf, with
   no resolution, chain map, K-injectivity, free represented sheaf, or generator.
   It is a strict part of the argument, not a restatement of the original item.
   Naturality of the localization and single-complex comparisons, compatibility
   of the two derived units, and the proved classical augmentation comparison
   establish it; none require a nonzero sheaf or nonempty etale object. Checked
   zero sheaf, empty object, zero map and zero resolution cases: both sides reduce
   to zero maps where appropriate, with no missing assumptions. Independently
   searched with LeanFinder, Loogle, and local rg using unit/homology/augmentation
   terminology. Found existing bounded-below normalization and module-direct-image
   normalization; neither duplicates the sheaf statement. Replaced the proposed
   repetition of the augmentation proof by the existing bounded-below theorem in
   the docstring and node, retaining the single source-transport hole. Verdict: pass.
4. Read the proof from the original target downwards. The generic unit naturality
   is proved from naturality equations, the resolution helper cancels the invertible
   unit, and the final proof applies homology, the source normalization, homology
   localization naturality, and element evaluation. No further homotopy-section
   bijectivity or arbitrary existence witness is used. No existing import or old
   proof dependency can be pruned: the concrete definitions in the homotopy-sections
   module and comparison-map module remain used. The K-injective module supplies
   data in the unchanged public definition. The new module's additional plain
   import supplies the proved normalization needed by its remaining proof plan.
   Read `dag/units/sk-lem-failure-field.json`: its realized lists are empty; no
   realized statement or proof step was bypassed or changed. Verdict: pass.
5. Compared both nodes with the declarations and proof. The original node records
   exactly the naturality/inverse-unit calculation and use of the new normalization.
   Its statement and statement dependencies are unchanged. The new node has its
   verbatim Lean statement, explicit construction, source, creation, blueprint,
   searches and complete proof plan. Corrected its proof dependencies to include
   the existing bounded-below augmentation node and marked that step non-elementary.
   All original proof dependencies remain needed; none are missing from the pruning
   report. Verdict: pass.

Second-reading changes: added the proof-only import of
`Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison` to the new module;
updated the new theorem's proof docstring to name the proved bounded-below
normalization and the derived-unit factorization equation; updated its node's proof,
proof dependencies, proof origin and independent searches; corrected the report's
search account and added this review. No change record is needed because no existing
statement or definition changed. No additional hole was closed or added by this review.
