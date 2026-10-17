## What changed

Repair of the returned delivery: removed the private duplicate theorem
`CategoryTheory.page_quotient_zero_iff` from `FilteredComplexDecalagePageData`.
The kernel proof now contains the same short cokernel factorization argument inline,
without introducing a second private declaration with the existing theorem's statement.
This addresses the import-prune rejection without changing any public declaration.

The existing statement of `CategoryTheory.filteredComplex_decalage_comparison` is unchanged.
Its proof now constructs the pagewise chain isomorphisms, assembles their spectral-sequence
isomorphism and inverse, and proves the required page-two naturality square by cancellation
on concrete representatives. Naturality is actually proved for every page r ≥ 2.

Six new modules make the argument concrete:

- `FilteredComplexDecalagePageData`: constructs representative lifts and interval classes,
  the monic right-interval page embedding and its page-two equation; proves the boundary
  zero criterion, equality of representative kernels and filtered-map naturality.
- `FilteredComplexDecalageLeftRepresentatives`: proves that original r-cycle representatives
  map epimorphically to cycles of the left decalage interval, using degreewise quotient
  exactness and epimorphic refinements. This includes r=2 without a boundedness hypothesis.
- `FilteredComplexDecalageIntervalMaps`: constructs endpoint-square maps of quotient short
  complexes and proves naturality of their cone-to-quotient homology comparisons.
- `FilteredComplexDecalagePageImage`: proves the equality of the representative image with
  the spectral page embedding. The key calculation is that the epic left-interval map
  followed by the monic right-interval map is the endpoint-square cohomology map.
- `FilteredComplexDecalagePageIso`: proves existence and uniqueness of the normalized page
  isomorphism using the proved image and kernel equalities and equal-kernel epi descent.
- `FilteredComplexDecalagePageCoherence`: states the remaining differential/successor
  compatibility of those fixed isomorphisms. Its proved private helpers identify the
  spectral-object connecting map with the quotient connecting map followed by projection,
  including its sign, construct the cycle lift of an original representative's derivative,
  calculate the connecting map on those actual representatives, and prove that
  representative classes commute with the right-interval transition from r to r+1.

No existing definition or statement was changed, and no existing consumer needed adaptation.
The assigned module's elaboration options are local to its tactic proofs and its helper
binders are explicit; its public command interface is unchanged.
The chosen representative lift and chosen page isomorphism are both uniquely determined by
proved normalization statements; no arbitrary witness of an unproved mere existence theorem
is used as data. All new construction data are explicit subobjects, kernels or cokernels.

## Proved and sorry left

Original module: one local hole before, zero after. Closed declaration:
`CategoryTheory.filteredComplex_decalage_comparison`.

Added local holes: one, in
`CategoryTheory.filteredComplex_decalage_page_coherence`
(node `lem-sp-filtered-complex-decalage-page-coherence`). Its proof is exactly `by sorry`.
This is a **decomposition**, with local net hole change zero; it is not a claim that the
comparison has been proved without remaining obligations. The remaining statement only
asserts compatibility of already constructed, uniquely normalized page isomorphisms; the
existence, invertibility, uniqueness, representative kernel/image calculations and naturality
have complete Lean proofs.

In particular the following new central declarations have no local `sorry`:
`filteredComplexDecalageRepresentative_exists_unique`,
`filteredComplexDecalageRepresentative_cycle`,
`filteredComplexDecalageRepresentativeClass_zero_iff`,
`filteredComplexDecalageRepresentative_kernels`,
`filteredComplexDecalageRepresentativeClass_naturality`,
`filteredComplexDecalageLeftRepresentatives`,
`filteredComplexDecalageIntervalIso_map`,
`filteredComplex_decalage_page_image`, `filteredComplex_decalage_page_iso`,
and `filteredComplexDecalagePageIso_ext`.

The proved private `representative_class_transition` also supplies the right-endpoint
calculation needed by the successor proof. The remaining compatibility proof still needs
two concrete calculations. For differentials,
combine `spectralSequence_page_d_eq` and `d_ιE_fromOpcycles` with the proved private
`representative_connecting` (already specialized to original representatives), then cancel
the representative epimorphism and target
page embedding, using the canonical differential's representative equation. Page two uses
`spectralSequence_first_page_d_eq`; its embedding is already computed separately. For
successors, use `spectralSequence_iso` and `spectralSequenceHomologyData_left_i/right_p`
to calculate the map on successor representatives, then apply
`filteredComplexCanonicalSequence_coherence` (or the chosen normalized homology equation)
and cancel the epic cover `filteredComplex_successor_cycles_cover`. These calculations were investigated in this
session; the connecting-map bridge was proved rather than left as another hole.

All seven sandbox modules compile through `lcompile.py --all` without warnings. The r=2 edge case is a separate proof that both
image subobjects are top. Neither finite support, convergence nor first-quadrant conditions
were introduced.

## No longer needed

Removed the redundant direct proof import
`Sheaf.CategoryTheory.FilteredComplexDecalage` from the assigned module. Its definitions
and node `lem-sp-filtered-complex-decalage` remain necessary through the tower and new
representative proofs. No entire existing node or module is pruned. The updated assigned
node lists the actual page-comparison, coherence and naturality dependencies rather than
its former undeveloped substitution argument.

In the new modules, the generic representative-kernel and quotient-image comparison
imports were removed after replacing their private helper uses by direct Mathlib cokernel
arguments and the already proved general interval boundary criterion. The new data module
imports the underlying WeilConjectures spectral-sequence API directly instead of the
unneeded `SpectralObjectPageTwoMap` extension theorem. These original modules remain needed
elsewhere through the unchanged canonical model and page-two functor; none is claimed pruned.

No alternative double-complex, truncation-convergence or exact-couple route is imported.
The duplicate private `page_quotient_zero_iff` theorem is no longer present; the
imported module's theorem is private and therefore cannot be referenced by name, so its
few factorization lines are kept locally at the use site rather than introducing another
library declaration with the same statement.

## Where the brief, the DAG or earlier work was wrong

No false statement or target mismatch was found. The former plan's sentence “the comparison
sends representatives to their own classes” required substantial missing Lean interfaces:
actual representative lifts, the two boundary zero criteria, equal kernels, equal images,
and uniqueness of the normalization. Those interfaces and proofs are now present.

Tag 012K supplies the actual filtered-cycle and boundary formulas. The decalage substitution
is an agent derivation from them; Tag 015X motivates the second filtration and is not cited
as an existing Mathlib or Stacks theorem about our exact decalage construction.

The chosen cokernels are sensitive to syntactically different integer endpoint expressions.
The proofs keep `q + (r - 1)` consistently and parametrize the left-interval calculation by
its endpoints; no definitions were altered to hide these transports. The remaining reader
should similarly normalize indices before constructing interval maps.

## New nodes

`def-sp-filtered-complex-decalage-page-data`: actual representative/interval constructions,
normalization property and uniqueness by epi/mono cancellation; implemented and proved.

`lem-sp-filtered-complex-decalage-representative-kernels`: equality of the original page
quotient kernel and the concrete decalage-class kernel; proved, including the necessary
general interval boundary-zero calculation.

`lem-sp-filtered-complex-decalage-representative-naturality`: class maps commute with any
representative map over a filtered chain map; proved without requiring that map to be epic.

`lem-sp-filtered-complex-decalage-left-representatives`: epimorphic coverage of left-interval
cycles by original representatives; proved using refinements and the decalage formula.

`lem-sp-filtered-complex-decalage-interval-maps`: cone-to-quotient homology comparison for
squares changing both interval endpoints; proved from the constructed short-complex square.

`lem-sp-filtered-complex-decalage-page-image`: representative image equals the monic spectral
page embedding; proved from the left-interval epi and interval-map calculation.

`lem-sp-filtered-complex-decalage-page-iso`: unique normalized individual page isomorphism;
proved from equal kernels and images, and used to define the chosen comparison.

`lem-sp-filtered-complex-decalage-page-coherence`: the one remaining hole. It needs the
explicit differential and successor calculations described above, for the already fixed
normalized page isomorphisms. It asserts neither their existence nor their naturality and
cannot replace the original comparison theorem by itself.

No change record is needed: existing signatures, definitions and visibility are unchanged.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes.** I compared the assigned module with the repository
version. The existing declaration `CategoryTheory.filteredComplex_decalage_comparison` has
byte-for-byte identical statement text; the only changes are its proof and proof-only imports.
All other delivered Lean modules are new, and no change record or forced adaptation is needed.
Verdict: passed.

2. **Compilation and axioms.** `lcompile.py --all` compiles all seven modules without
warnings. The comparison theorem and every completed public helper use only
`propext`, `Classical.choice`, and `Quot.sound`; the sole remaining `sorryAx` occurs in the
named split theorem `CategoryTheory.filteredComplex_decalage_page_coherence`.
There are no `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definitions.
Verdict: passed, with the documented coherence hole left open.

3. **Statements and split nodes.** I checked the seven new node statements against their
Lean declarations, searched the repository and Mathlib-facing index for duplicate declarations,
and tested the representative constructions at the r = 2 edge case used by the proofs. The
split coherence statement is a strictly smaller compatibility obligation: it assumes the fixed
normalized page isomorphisms and asserts only differential and successor compatibility, rather
than restating the comparison theorem. Its docstring gives the remaining proof route and its
DAG node matches the declaration. Verdict: passed.

4. **Pruning and imports.** The removed direct `FilteredComplexDecalage` import is no longer
needed; the remaining public imports provide statement interfaces and the plain or `import all`
imports are used only by proofs. The report's no-longer-needed list agrees with the updated
comparison node's `proof_deps`; no unit route is bypassed. Verdict: passed.

5. **DAG and report consistency.** Existing node signatures and visibility are unchanged, and
all new nodes carry Lean records, proof steps, sources, and dependency lists matching the code.
A dry run of `deliver3.py H3 Sheaf.CategoryTheory.FilteredComplexDecalageComparison --no-push`
reported OK. Verdict: passed.

I changed only this report by adding this second-reading record; no Lean proof or statement
required repair.

## Second reading by H3

1. **Signatures and accidental changes.** I compared the assigned module with the repository
version. The public statement of `CategoryTheory.filteredComplex_decalage_comparison` is
byte-for-byte unchanged; its edits are proof-only and proof imports. The seven additional
modules are new, and no existing consumer or definition was adapted. Verdict: passed.

2. **Compilation and axioms.** I compiled all seven delivered modules with
`lcompile.py --all`; every file compiled without warnings. A direct declaration scan found no
`axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. Axiom probes for
the completed public declarations returned only `propext`, `Classical.choice`, and `Quot.sound`;
the only `sorryAx` is in the named split theorem
`CategoryTheory.filteredComplex_decalage_page_coherence`, and it is recorded in its node and
report. Verdict: passed with the documented decomposition hole.

3. **Statements and split nodes.** I checked each new node's Lean statement and declaration,
searched the repository and ran a fresh LeanFinder query for alternate declarations; the hits
were generic homological-complex APIs and no duplicate decalage comparison. The r=2 branch of
the page embedding and page-two comparison was compiled and is handled explicitly. The split
coherence statement assumes the already fixed normalized page isomorphisms and asserts only
differential and successor compatibility, so it is strictly smaller than the comparison target.
Verdict: passed.

4. **Pruning and imports.** The comparison's removed direct
`Sheaf.CategoryTheory.FilteredComplexDecalage` import is not needed by its proof; the remaining
public imports support signatures and the plain/`import all` imports support proof details. The
comparison node's proof and `proof_deps` follow the actual normalized-page, representative,
and naturality route. The unit record's `realized` route is unchanged and no unit-level step is
bypassed. Verdict: passed.

5. **DAG and report consistency.** I checked the new node records, declaration names,
statements, proof origins, sources, and dependency lists against the delivered files. The
comparison node retains its existing statement and records the new route; the coherence node
matches the sole remaining `sorry`. Verdict: passed.

I changed no Lean proof or statement during this reading. I appended this independent review
record to `report.md`; no change record or forced adaptation is required.
