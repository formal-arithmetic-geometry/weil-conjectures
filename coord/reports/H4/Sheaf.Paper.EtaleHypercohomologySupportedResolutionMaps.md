## What changed

Preserved the signature, visibility, universe, original docstring and scoped options of
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_supported_resolution_maps`.
Replaced its sorry by a complete Lean reduction of the arbitrary-resolution-lift
comparison to support-controlled maps of augmented CE totals. Added proof-only imports
of EtaleHypercohomologySupportedCETotals, KInjectiveComparisonPrinciple and
CartanEilenbergAugmentationQuasiIso. Both original public imports remain necessary.

The new module Sheaf.Paper.EtaleHypercohomologySupportedCETotals states one obligation:
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_supported_ce_filtered_totals`.
It chooses D, M and eInf jointly, together with an actual sheaf CE-total map u, its strict
augmentation square, and the stationary-page equation for the homology map of that same u.
It does not quantify arbitrary D/M/eInf, and does not assert anything about arbitrary
supplied K-injective lifts j or section maps w. Its docstring gives the supported
construction and representative argument in five numbered steps. This isolates steps
1-3 of the original plan, leaving its substantial step 4 proved in the item's module.

The proof adapts the existing, proved resolution comparison in
EtaleHypercohomologyFilteredResolutionMaps, with the CE-total identification from
EtaleHypercohomologyCETotalMaps. It uses the existing public ceSectionsUnit naturality
and totalSectionsIso_comparison, rather than duplicating their proofs. In particular it
proves the homotopy-category cancellation, applies global sections to the homotopy,
identifies its endpoints, and cancels the canonical c_formula comparison. It retains
the same filtration maps t throughout, so the stationary-page equation survives.
No existing dependency interface or target statement changes; no forced adaptations.

Both delivered modules compile cleanly using lcompile.py --all. Local single-file
compiles are approximately 3.4 seconds for the new obligation and 17 seconds for the item.
The existing node copy now records the Lean route, including the finite-diagonal
sections comparison, and points to the new support-construction node.

## Proved and sorry left

Original holes closed: one of one,
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_supported_resolution_maps`
(node `lem-weil-pbc-supported-resolution-maps`). Its body has no sorry.

Holes added: one,
`AlgebraicGeometry.Etale.exists_etaleHypercohomology_supported_ce_filtered_totals`
(node `lem-weil-pbc-supported-ce-filtered-totals`), in the new module
Sheaf.Paper.EtaleHypercohomologySupportedCETotals. Its whole proof is `:= by sorry`.
No other declaration delivered has a hole; the private sectionsUnit construction and
its naturality theorem are complete. No data are chosen from an unproved mere-existence
statement in a definition: the new existential is eliminated only within the theorem.

This is a decomposition (one upper hole closed, one strictly lower obligation added),
not an axiom-free proof of the final theorem and not a claimed net hole reduction.
The lower statement concerns the selected CE-total map only; the genuine proof of
independence from every supplied resolution lift is now complete. Existing imported
obligations remain the library's existing obligations, not new holes of this delivery.

## No longer needed

Imports removed: none. Both original public imports directly supply declarations used
by the signature and are retained. Every added proof-only import is used.

The old direct proof dependency `lem-weil-pbc-ce-total-filtered-maps`
(Sheaf.Paper.EtaleHypercohomologyCETotalMaps) is no longer used by this proof: its arbitrary
existential presentation does not retain the explicit support bound. Its role is replaced
by the new supported CE-total construction. The proved generic
Sheaf.Paper.EtaleHypercohomologyFilteredResolutionMaps is used as a source for the proof,
not imported, since its unrestricted eventual threshold cannot imply the required bound.
Neither module is claimed globally unreachable: other library users may still need them.

`lem-sp-cartan-eilenberg-exists` and
`lem-sp-filtered-stable-subquotient-at-bounds` move from direct dependencies of the item
to dependencies of the new construction node; they are still needed, not pruned.
The augmentation quasi-isomorphism and K-injective comparison dependencies remain
and are actually applied in Lean. The finite-diagonal sections comparison is added
explicitly to the route. No unit-level statement or proof step is bypassed;
dag/units/sk-prop-h2.json has no realized entry naming this item.

## Where the brief, the DAG or earlier work was wrong

The earlier helper was false: arbitrary M could be zero while the identity lift forces
an identity abutment map. Also arbitrary eInf cannot be assumed natural. That helper
and its core theorem are not revived. The new construction jointly chooses M and eInf
from the same filtered-total map and asserts its stationary compatibility before any
arbitrary resolution lift is introduced. Thus zero M is never substituted for the
page map belonging to the identity total map on a nonzero stationary piece.

The existing eventual-bound CE construction cannot be used as an arbitrary witness
for the support-controlled assertion. The new obligation explicitly performs the
supported choice first, taking zero CE data for the all-zero complex, otherwise using
the least nonzero complex degree. This yields zero rows below every lower support bound
simultaneously. The arithmetic bound then forces exactly the two stationary outer steps.

Small-case checks of the new statement and its proof plan: on the zero complex or empty
scheme every relevant total, subquotient and image is zero. For a point and a nonzero
sheaf concentrated in degree zero, a=0, q=n=0, r=2 is admissible; the identity augmented
total lift gives the identity on the single nonzero graded piece. Arbitrary smaller
support bounds only delay stabilization; changing a support witness does not change
the canonical quotient map. Negative degrees and empty diagonals give zero objects.
These are mathematical checks, not claims of a formalized etale-sheaf countermodel.
The Lean proof of the arbitrary-lift comparison is uniform in all these cases.

Read Stacks Tags 015J and 0EZM online; Tag 015K's endpoint was unavailable during this
session. The existing construction modules and their docstrings were also read.
The explicit least-support choice and bound are an agent expansion of the source
arguments, recorded as such in proof_origin, not a claim of a verbatim Stacks lemma.
Mathlib searches used LeanFinder, Loogle and grep. LeanSearch returned an internal
server error and is recorded as unavailable. Blueprint searches for support, stationary
and 015J found no existing blueprint statement of the new obligation; ancestor returns
None for this generated support node. The original node's blueprint fields are untouched.

An additional overlay DAG audit found two pre-existing cycles, both also reachable
from the original item before this delivery: sheaf-algebraic-structures-abelian-component
with sheaf-algebraic-structures-objects, and sheaf-algebraic-structures-objects with
sheaf-algebraic-structures-ring-component (all ids prefixed lem-weil-pbc-).
The overlay has exactly the same two cycles; none involves the new obligation, whose
dependencies do not reach the item. This existing coordination defect is reported here
for the maintainer; no unrelated node is changed. The import-cycle and delivery
preflight checks pass.

The deliver3.py --no-push dry run printed OK: compilation, axiom probe and preflight
passed, with only the independent second reading outstanding. Nothing was pushed.

## New nodes

`lem-weil-pbc-supported-ce-filtered-totals`, in
`dag/nodes/sec-curve-estimates/lem-weil-pbc-supported-ce-filtered-totals.json`, is the
support-controlled augmented CE-total construction, before comparison with arbitrary
K-injective resolution lifts. Its module is
Sheaf.Paper.EtaleHypercohomologySupportedCETotals. The record includes the verbatim Lean
signature, the five-step natural-language construction, source, actual search records,
and inherited chapter and unit. It has no dependency back on the item being proved.
There are no change records because no existing interface changes.

## Second reading by H4

1. **Interfaces: PASS.** Independently diffed the delivered item against the repository.
   The existing theorem signature is byte-for-byte identical, as are its docstring,
   universe, visibility and scoped options. The only Lean changes are three proof-only
   imports, two fully constructed private helpers, and the proof body. The new module
   adds one theorem; no existing definition or target changes. Existing node changes
   are exactly proof, proof_deps and proof_origin; no change record is required.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled both modules
   in import order with lcompile.py --all, cleanly (2.8 s and 15.1 s). Scratch copies
   with #print axioms show exactly propext, Classical.choice, Quot.sound and sorryAx
   for each public theorem. The sole textual sorry is the whole proof of the named
   supported_ce_filtered_totals obligation. No forbidden declaration, hollow
   definition or data choice from an unproved existence theorem occurs. D, M, eInf
   and u are eliminated within a theorem proof only. Read the homotopy cancellation,
   mapped homotopy endpoints, c_formula cancellation and unchanged t/hc equation.
3. **Split obligation: PASS.** Checked the simultaneous existential quantifiers:
   no arbitrary M, eInf or presentation is asserted natural. The new assertion
   concerns an augmented CE-total lift and its own homology map; it omits the
   original assertion about every supplied K-injective lift. The latter is proved
   by the actual 100-line reduction, so this is a genuine partial argument, not
   renaming the original hole. Reviewed CE existence (including its prescribed
   zero negative rows), augmented CE comparison and stationary quotient formulas.
   For a nonzero bounded-below complex the least nonzero degree b exists, every
   lower support bound a satisfies a <= b, and the chosen rows below b are zero.
   For r >= max(1,q-a+2,n-q+2), q+r >= n+2 and q-r+1 <= a-1,
   exactly sufficient for the two outer-step bounds. Checked zero complexes,
   negative and empty diagonals, and the degree-zero identity case with a=q=n=0,
   r=2; no counterexample or extra hypothesis is introduced. Read Stacks Tags
   015J, 015K and 0EZM independently; the bound is an explicitly recorded expansion.
   Fresh LeanFinder search for stable-page naturality found no applicable replacement;
   Loogle found Homotopy.homologyMap_eq, already used, and Mathlib grep found generic
   spectral-sequence infrastructure rather than this supported construction. Local
   searches located EtaleCECoherentFirstPageLifts and EtaleCEStationaryPageNaturality;
   their existential presentations and unrestricted thresholds do not supply the
   required support-controlled bound. The remaining construction cannot be closed
   in a few minutes from their current interfaces.
4. **Route and pruning: PASS.** Read the proved CETotalMaps and FilteredResolutionMaps
   reductions and the existing generic coherent-lift/stationary interfaces. The
   new proof uses existing sections naturality and comparison results, then the
   K-injective comparison principle, with no redundant obligation for this step.
   Added imports are proof-only and each supplies an applied declaration. Both
   original public imports supply signature declarations, including cohomologyMap.
   The old direct CE-total dependency is replaced; CE existence and the stationary
   subquotient obligation remain under the new node, as the pruning section says.
   No globally unreachable module is claimed. The sk-prop-h2 realized statement
   and step lists are empty, so no realized unit step is bypassed or changed.
5. **DAG: PASS.** Verified the new node signature occurs verbatim in its Lean file,
   required source/search/creation/blueprint/chapter/unit records are present, and
   each node's proof_deps equals the union of uses in its proof steps. The original
   node's four steps describe the actual reduction; the new node describes the
   unresolved filtered construction. The new node has no dependency back on the
   item. One hole closed and one hole added remains a decomposition with net zero,
   not a proof free of sorryAx.

Second reading changed only this report by adding the independent review and fresh
search/axiom evidence. No Lean or DAG repair was needed.
