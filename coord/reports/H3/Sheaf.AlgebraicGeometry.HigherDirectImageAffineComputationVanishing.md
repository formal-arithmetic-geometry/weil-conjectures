## What changed

The assigned theorem `AlgebraicGeometry.Etale.exists_higherDirectImage_affine_computation_eq_zero`
now has a complete Lean reduction, with its original signature and docstring unchanged.
The proof uses the existing natural comparison theorem, lifts the section on its image
sieve, obtains local raw-class zero witnesses, proves cover transitivity, extracts a finite
subcover by compactness, obtains a common later stage using `IsFiltered.wideSpan`, and
uses transition composition and sheaf separatedness to conclude.

New modules isolate local raw cohomology eventual vanishing and canonical abelian
transition composition. The raw-class statement includes local injectivity of
sheafification and affine cohomology continuity, but no higher-image comparison or
common-stage gluing. All new objects in these proofs are explicit
constructions; the comparison isomorphisms supplied by the existing theorem are used
only locally in a proposition proof. No definition, existing statement or public import
of the assigned module changes.

## Proved and sorry left

Closed the assigned hole in
`AlgebraicGeometry.Etale.exists_higherDirectImage_affine_computation_eq_zero`
(node `lem-sbc-higher-direct-image-affine-computation-vanishing`).

Two new holes remain:
- `AlgebraicGeometry.Etale.exists_higherDirectImage_raw_local_class_eq_zero`
  (`lem-sbc-higher-direct-image-raw-local-class-vanishing`): raw-Hom continuity
  with local sheafification refinement, with no higher-image comparison or finite gluing.
- `AlgebraicGeometry.Etale.abelianHigherDirectImage_transition_comp`
  (`lem-sbc-abelian-higher-direct-image-transition-comp`): composition for compatible
  coefficient maps, with no affine, qcqs, directedness or limit hypotheses.

This is a decomposition: one original hole closed, two new holes added; it is not an
axiom-free proof of the target. The natural comparison used by the reduction already
has its own existing hole and node. No partial proof contains `sorry`.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
and `Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit` from the assigned module.
Their nodes `sbc-lem-higher-direct-image-presheaf` and
`lem-weil-pbc-etale-cohomology-limit-complex-systems` remain needed underneath the
natural comparison and raw affine continuity, respectively; neither is globally pruned.
Second reading also removed redundant direct proof imports
`Mathlib.CategoryTheory.Sites.LocallySurjective` and
`Mathlib.AlgebraicGeometry.Sites.AffineEtale`: the remaining imports already provide
the declarations and instances used by the proof, as verified by compilation.
No old dependency node or module is eliminated from the transitive route. No unrelated
cohomology colimit or diagram-of-higher-images theorem is imported.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt stopped without constructing a reduction. Its missing comparison
now exists as `exists_abelianHigherDirectImage_natural_comparison`; its naturality is
essential, since an arbitrary isomorphism from the Nonempty presheaf comparison would
not identify the canonical maps. Module-coefficient transition theorems do not directly
specialize to the displayed AddCommGrpCat definition. The original DAG marked common-stage
assembly elementary without naming transition coherence; the new node supplies that
precise missing input.

The unit route is preserved: natural cohomology-presheaf comparison, affine complex
continuity, and finite-cover assembly are still the three steps. Checked the Stacks
source at `etale-cohomology.tex`, labels lemma-relative-colimit,
lemma-higher-direct-images and lemma-colimit-variant-complexes, in the local literature
copy. Edge cases: degree zero is section continuity; empty objects have zero raw group;
the finite subcover may be empty, handled by wideSpan and sheaf separatedness;
transition composition requires no geometric hypotheses.

## New nodes

`lem-sbc-higher-direct-image-raw-local-class-vanishing` isolates the injectivity half
of raw affine cohomology continuity with local sheafification refinement, following
09Z1, 03Q8 and 0EZM.
`lem-sbc-abelian-higher-direct-image-transition-comp` isolates the geometric-independent
composition law for the canonical derived-unit/coefficient maps.
Each has a self-contained statement, verbatim Lean signature, complete proof in words,
source, blueprint ancestry and three kinds of search. LeanSearch was unavailable;
LeanFinder and source searches found no usable duplicate. No change record is needed.


## Second reading by H3

1. Compared all delivered modules with the repository. Only the assigned module
   already exists there. Its existing theorem signature is byte-for-byte identical,
   its docstring and public imports are unchanged, and no definition changes.
   The two sibling modules are new. Verdict: no accidental interface change.
2. Compiled all three modules in import order through lcompile.py without errors
   or warnings. A scratch copy with explicit #print axioms checks for all three
   declarations reports only propext, Classical.choice, Quot.sound and sorryAx.
   The only delivered sorries are the two named theorems listed above; there are
   no definitions, forbidden declarations, or partial-proof holes in the delivery.
   The comparison witness is eliminated inside a proposition proof, never used
   to define arbitrary data. Verdict: valid conditional reduction, not an
   axiom-free proof. One hole closed, two added; net minus one.
3. Read both new signatures, docstring proofs and nodes. Checked degree zero,
   zero coefficients, empty etale objects, singleton diagrams and identity
   transitions. Raw local vanishing asserts separate later witnesses on a cover,
   with no common-stage assembly; transition composition is solely functoriality
   of the canonical map. Both are true proper parts of the argument, not renamed
   copies of the assigned theorem. Read Stacks etale-cohomology.tex at
   lemma-relative-colimit, lemma-higher-direct-images and
   lemma-colimit-variant-complexes. Independently searched LeanFinder for derived
   adjunction composition and eventual etale cohomology vanishing, Loogle for
   toSheafify and zero, and Mathlib sources for local injectivity and derived
   unit/counit composition. Searched the library's raw pullbacks and transition
   results. The nearby affine raw-class theorem proves surjectivity, not this
   vanishing assertion; the proved transition composition theorem concerns
   ModuleCat coefficients, not the displayed AddCommGrpCat construction.
   No directly usable duplicate or quick closure was found. Verdict: accepted
   decomposition with both smaller statements still open.
4. Read the main proof from its conclusion back through separatedness, wideSpan,
   compactness, the eventual-zero sieve, raw local vanishing and the natural
   comparison. These implement actual gluing rather than transferring the whole
   assertion to a new hole. Tested removing the two redundant Mathlib imports in
   a scratch copy, which compiled, and made that removal in the delivered module.
   All old direct proof dependencies are reported above and remain on the
   transitive route. Read sk-lem-failure-field.json: its realized fields are empty;
   this delivery neither replaces a realization nor bypasses a unit step.
   The higher-image comparison, affine continuity and finite-cover route stays.
   Verdict: route preserved and direct proof imports pruned.
5. Compared the existing node's diff: only proof, proof_deps and proof_origin
   change, matching the comparison, raw local vanishing and composition used by
   Lean. Both new nodes have matching verbatim signatures, source, complete proof
   plans, dependency unions, search records, creation metadata, blueprint ancestry,
   chapter, unit and Lean records. Verdict: DAG agrees with the reduction and the
   two remaining obligations.

Second reading changed only the two redundant Mathlib proof imports, corrected
copied author credits to H3 in the two new modules, and completed this report.
Existing signatures, definitions, proof bodies and the proposed DAG are retained.
