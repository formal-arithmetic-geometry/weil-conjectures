## What changed

Repaired reviewer X-ae896 E3 in the sandbox. Added the actual restricted CE bicomplex
and sheaf total, explicit degree-zero augmentation components, the augmentation
chain map, and the finite-diagonal global-sections comparison. The latter is
constructed from extension-by-zero naturality and coproduct comparison maps.
It never selects an isomorphism from an unproved existence proposition.

Defined etaleRestrictedSectionsLift by Subobject.factorThru with its prescribed
composite through the monic filtered-step inclusion. Proved its arrow equation
and uniqueness, so this universal-property choice determines the map exactly.
Defined etaleFilteredStepCohomologyIso in the item's module by composing homology
of the inverse sections lift with resolutionEtaleCohomologyIso for the explicit
restricted augmentation. Named resolution and invertibility lemmas supply proofs,
not arbitrary data.

Changed the compatibility conclusion to this definition and changed the final
proof to let e := etaleFilteredStepCohomologyIso X K T p q. The final theorem's
signature and all Challenge signatures are preserved. Removed the dispute comment:
its identified unrestricted-choice fault is now repaired. Added matching nodes,
updated the three original proof routes, and recorded the compatibility signature
change and its users in coord/changes/etale-filtered-step-canonical-comparison.md.

Validation: all six delivery modules compile through lcompile.py. The original,
unchanged EtalePresentationImageFiltration consumer also compiles against the
repaired module. The initial dry run passed compilation, the axiom probe and
preflight, except for the second reader's section; it is rerun after the additional
restricted-resolution proof.

The construction/properties live in five new modules:
EtaleRestrictedTotalConstruction, EtaleRestrictedAugmentationComm,
EtaleRestrictedTotalResolution, EtaleRestrictedSectionsFactors, and
EtaleRestrictedSectionsComparison, all under Sheaf.AlgebraicGeometry.

## Proved and sorry left

Closed the original etale_filtered_step_cohomology_iso hole by supplying the
explicitly constructed comparison. This is a decomposition, not an axiom-clean
proof: one original hole closed, two strictly smaller property holes added.
Proved etaleRestrictedTotal_resolution from cartanEilenberg_total_resolution,
etaleRestrictedAugmentation_comm, etaleRestrictedBicomplex_below, and the original row-resolution and injective-term
fields T.rows and T.terms. The lift arrow and uniqueness lemmas instead justify
the separate sections-factorization construction.
The final etale_filtered_step_cohomology was already proved; its witness is
repaired rather than counted as a newly closed hole.

Every remaining sorry, with its node:

- AlgebraicGeometry.Etale.etale_filtered_step_cohomology_compatibility
  (lem-weil-pbc-etale-filtered-step-cohomology-compatibility): the original
  naturality hole, with the requested corrected comparison in its conclusion.
- AlgebraicGeometry.Etale.etaleRestrictedSections_factors
  (lem-weil-pbc-etale-restricted-sections-factors): the actual sections inclusion
  factors through the monic filtered-step subobject.
- AlgebraicGeometry.Etale.etaleRestrictedSectionsLift_isIso
  (lem-weil-pbc-etale-restricted-sections-lift-isIso): the resulting unique lift
  is an isomorphism of complexes.

The two remaining added properties have complete proof docstrings and matching nodes.
They concern chain maps and resolutions, independent of p and of the final
cohomology compatibility equation. No sorry occurs in a definition or private helper.

## No longer needed

Removed the item's direct proof imports of
Sheaf.CategoryTheory.CartanEilenbergMappedTotal and
Sheaf.CategoryTheory.KInjectiveComputes. Their nodes
lem-sp-cartan-eilenberg-mapped-total and lem-sp-kinjective-computes are not needed
by this proof route: the finite-diagonal map is directly constructed, and derived
cohomology is computed by the existing resolutionEtaleCohomologyIso definition.
No claim is made that these modules leave the whole target closure; other users
may still import them.

The CartanEilenbergTotalResolution import moved to the new restricted-resolution
property module, where its theorem is needed; it is not pruned. The
KInjectiveComparisonPrinciple import stays for the compatibility proof plan.
The final theorem no longer needs the Nonempty iso theorem or its node
lem-weil-pbc-etale-filtered-step-cohomology-iso; that API is retained and now proved.
The unlanded pointwise split from the earlier attempt stays removed. No unit route
is bypassed: sk-prop-h2 has no realized nodes in its statement or step lists.

## Where the brief, the DAG or earlier work was wrong

The old compatibility statement chose an arbitrary isomorphism from bare
Nonempty Iso. Its docstring argued only for a canonical resolution comparison,
so flagging the problem without constructing that map did not repair E3.
The delivered definition now fixes the forward map and inverse by actual
coproduct comparisons, the unique monic lift, and the derived-resolution recipe.
Choosing a lower bound in the finite-diagonal proof affects only preservation
proofs, not the coproduct comparison map. Existential data extraction
from an unproved new property is the unique factorization or inverse:
Subobject.factorThru has a fixed arrow equation and monicity determines its result
uniquely, as proved in Lean; asIso supplies the unique inverse of this fixed lift.
Neither property permits selecting an unrelated isomorphism.

The compatibility node's corrected statement names this construction, and its
statement_change lists every existing DAG citer. The declaration-specific search
lists only the item's own final proof; external consumers use its unchanged
existential statement and require no adaptation. No target definition or meaning
changes. Edge cases checked in the proof plans: arbitrary negative q, zero
complexes, empty diagonals, and all integer p; below q the augmentation source
is zero, as implemented in the Lean commutation proof.

## New nodes

- def-weil-pbc-etale-restricted-total-construction: explicit bicomplex, total,
  finite-diagonal comparison, augmentation components, and sections inclusion;
  records all seven declarations of EtaleRestrictedTotalConstruction.
- lem-weil-pbc-etale-restricted-augmentation-comm: the proved differential equation.
- def-weil-pbc-etale-restricted-augmentation: actual chain map with fixed components.
- lem-weil-pbc-etale-restricted-total-resolution: proved quasi-isomorphism/K-injectivity property.
- lem-weil-pbc-etale-restricted-sections-factors: existence of the unique monic factorization.
- def-weil-pbc-etale-restricted-sections-lift: universal-property construction and
  the proved arrow and uniqueness lemmas.
- lem-weil-pbc-etale-restricted-sections-lift-isIso: componentwise invertibility property.
- def-weil-pbc-etale-filtered-step-cohomology-iso: concrete composite isomorphism
  defined in the item's own module.

Change record: coord/changes/etale-filtered-step-canonical-comparison.md.

## Second reading by P1

1. Compared every delivered module with the repository: five modules are new.
   The existing iso-existence and final existential signatures are byte-for-byte
   unchanged. Only the compatibility signature changes, exactly as declared in
   the change record; its old arbitrary choice is replaced by the fixed composite.
   No target or existing definition changes. Declaration-use searches found only
   the final theorem as a consumer of the compatibility lemma; the external image
   filtration consumer uses the unchanged final theorem. Verdict: passes.
2. Compiled all six files with lcompile.py in import order: no errors or warnings.
   Inspected every definition and proof, including the finite-diagonal comparison,
   augmentation differential calculation, and restricted row-resolution proof.
   Exactly the three named and reported theorems contain sorry. There is no
   forbidden declaration, hidden proof hole, or arbitrary data witness. The
   factorThru equation and monic cancellation prove that its existence property
   determines the lift; IsIso determines the inverse. The scratch #print axioms probe checked every public declaration: only
   propext, Classical.choice, Quot.sound and expected sorryAx occur.
   The augmentation and finite-diagonal comparison are axiom-clean; resolution
   still inherits an upstream sorryAx. Delivery preflight checks them again. Verdict: passes with the
   explicitly reported open properties, not an axiom-clean completed proof.
3. Read the two new open property statements and their docstrings and nodes.
   Factorization uses the column summands and T.filtration_formula; invertibility
   identifies the same retained summands componentwise. Neither restates the
   cohomology theorem: both are assertions about fixed chain maps independent of
   p and derived cohomology. Checked empty diagonals (n < q), zero complexes,
   negative q and arbitrary p: retained indices are q <= s <= n, with r = n-s;
   omitted rows are zero. Independent leanfinder, loogle and grep queries looked
   for column-truncated total/filtration and factorThru-isomorphism lemmas. Searches
   found general truncation, image, and subobject ingredients, not these comparisons.
   Read the upstream stupid-truncation API and the library's bounded-below second
   filtration and total-resolution modules; no immediate replacement closes the
   open properties. Verdict: true, needed, strictly smaller decomposition.
4. Followed the proof from the final existential statement down to the explicit
   comparison. The restricted-resolution proof uses the existing generic total
   theorem, while the finite-sum comparison uses actual coproduct comparison and
   extension maps. Public imports support exposed definitions; the generic total
   resolution and K-injective comparison remain proof imports. No longer needed
   lists the old mapped-total and KInjectiveComputes routes and the old iso-existence
   dependency of the final proof. The old presentation dependency remains used
   through T's fields and the existing resolutionEtaleCohomologyIso; it is not
   pruned. The generic total-resolution dependency moves into the property module,
   and the comparison principle remains in the open compatibility plan. Checked
   sk-prop-h2.realized: its statement and step lists are empty and no realized
   unit route is bypassed. Verdict: passes.
5. Read all eleven delivered node records, their proof steps, proof_deps, origins,
   source and search records, and Lean declarations. The resolution node reflects
   restriction of T.a and application of cartanEilenberg_total_resolution; the
   iso and final nodes reflect the actual fixed comparison. All eight new nodes
   carry source, blueprint provenance, chapter, unit, searches, created and lean
   records. The two added holes have matching nodes and complete proof docstrings.
   Verdict: agrees with the Lean and preserves the unit route.

Second reading changed only documentation and Lean-signature node records: corrected the report's claim that the
restricted-resolution proof uses the sections lift arrow/uniqueness lemmas (it
uses T.rows and T.terms instead), and restored verbatim multiline old/new
compatibility signatures in the change record. Updated each node lean.statement
to the verbatim multiline declaration signature. No Lean proof or signature
was altered during this reading. One original hole is closed by decomposition;
two new holes remain, and the original compatibility hole remains. Net holes
closed minus added for this delivery is -1; no whole-closure pruning is claimed.
