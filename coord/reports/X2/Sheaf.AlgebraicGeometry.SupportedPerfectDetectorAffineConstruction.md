## What changed

Replaced the sole proof hole in
`Sheaf.AlgebraicGeometry.SupportedPerfectDetectorAffineConstruction` by a compiling reduction
that follows the node's affine Koszul route. All existing signatures and public imports are
unchanged. Two new modules state the unfinished geometric and transport steps:
`Sheaf.AlgebraicGeometry.AffineKoszulGeometricProperties` and
`Sheaf.AlgebraicGeometry.AffineDerivedOpenTransport`.

The main proof constructs the finite tuple from Mathlib's compact-open basis theorem,
reindexes it by `Fin r`, and proves the zero-locus equivalence. It writes the actual exterior
Koszul complex, sheafifies it termwise, and localizes. A proved private helper
`qcoh_of_qcoh_terms` proves quasi-coherence of its homology using the existing kernel and
cokernel closure results. The proof transports its perfection and support and applies the
existing `koszul_open_orthogonality` theorem to that exact complex. The equivalence adjunction Hom bijection and shift isomorphism transfer
subsingletonness in a real Lean proof; unit comparison then gives the assertion on X. The transport statement identifies its functor
with termwise restriction along the scheme isomorphism after localization, rather than
asserting a property of arbitrary supported perfect objects.

Updated the original node's proof, proof dependencies, and proof origin to match this Lean
argument. Added complete nodes, source citations, and proof docstrings for both new holes.
The unit `sk-thm-picard-duality` has no realized statement or step assigned to this item;
its route is retained and no unit or target statement changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.supported_perfect_detector_affine_construction`: 1 of 1 holes in the item.
The item's module has no remaining `sorry`. This is a decomposition, not a proof free of
unproved dependencies: two holes were added, for a net hole change of 1 closed minus 2 added.
The private `qcoh_of_qcoh_terms` helper is proved with no hole.

Every added hole:

- `AlgebraicGeometry.affine_koszul_geometric_properties`, node
  `lem-pc-affine-koszul-geometric-properties`: perfection and stalk vanishing for the
  explicit sheafified finite Koszul complex. Its proof is exactly `by sorry`.
- `AlgebraicGeometry.affine_derived_open_transport`, node
  `lem-pc-affine-derived-open-transport`: general transport along a specified scheme
  isomorphism, including localization comparison, adjunctions, support, the coherent shift structure,
  and unit comparison. Its proof is exactly `by sorry`.

The existing imported `AlgebraicGeometry.koszul_open_orthogonality` is still unproved in
the baseline; it was neither changed nor duplicated. The reduction uses it as intended
by stage 3. All three delivered Lean modules compile without warnings via `lcompile.py`.

## No longer needed

Removed the item's direct proof import
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral` (node
`lem-pc-ringed-spaces-derived-adjoint-general`). The main proof uses the more precise
transport interface instead. This is only a direct dependency reduction: the general
ringed-space adjunction remains in the new transport node's proof plan and is still
reachable elsewhere. No existing module is claimed to be globally pruned.

Kept `Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality` and its node
`lem-pc-perfect-generation-koszul-orthogonal`; the final proof explicitly applies it.
The original direct proof dependency `def-pc-perfect-complex` is also replaced by the
geometry and transport nodes; its module `Sheaf.AlgebraicGeometry.PerfectComplex` stays
publicly imported because the unchanged target signature uses `Scheme.IsPerfect`.
Neither that definition nor its module is globally pruned. The earlier attempt's false generalized
orthogonality lemma and construction-data split are not used, imported, or recreated.
The new geometry lemma omits quasi-coherence, because the main proof establishes it.

## Where the brief, the DAG or earlier work was wrong

The earlier orthogonality split was false: the zero object is supported and perfect,
but that does not make it a detector. This delivery requires the actual Koszul object
and its finite tuple and invokes the existing detector-specific orthogonality theorem.
Neither new statement repeats the target: the geometry lemma makes no detection or
adjunction assertion; transport applies to arbitrary objects and makes no detection
assertion. The main proof combines these steps with a separate existing theorem.

The node's plan left the affine-presentation, universe transport, and localized-site
comparison unstated. They are now explicit in the transport node. The restriction
adjunction theorem's existing interface is for total derived tensor pullback on ringed
spaces; identifying this with exact restriction and the localized open site is one of
the remaining transport steps, not an assumed definitional equality.

Edge cases were checked in the statements and proof: r=0 gives the structure sheaf in
degree zero and makes the geometry support premise false; the zero ring has no points;
U empty and U full are allowed. The compact-cover argument needs no nonempty finite set.
For Q=0 the equivalence still compares zero Hom groups and matching
units; neither new statement asserts that either unit must be invertible. Mathlib searches ran via
`msearch.py` and are recorded in `searches.jsonl`. LeanSearch returned HTTP 500 and is
recorded as unavailable. Local literature files were absent, so the source statements
and proofs were read from the Stacks Project's Tag 0A9A, 09IR, and 0663 pages online.

## New nodes

`lem-pc-affine-koszul-geometric-properties`, in
`lean/Sheaf/AlgebraicGeometry/AffineKoszulGeometricProperties.lean`, isolates the bounded
finite-free representatives and the localized Koszul contracting homotopy of Tags 0A9A
and 0663. It does not choose an arbitrary witness and contains no new definition.

`lem-pc-affine-derived-open-transport`, in
`lean/Sheaf/AlgebraicGeometry/AffineDerivedOpenTransport.lean`, isolates the general
scheme-isomorphism/localized-site transport and derived adjunction of Tag 079W used in
the affine presentation of Tag 09IR. The localization comparison fixes the functor up
to natural isomorphism; right adjoints and adjunction units are transported compatibly.
It has no finite tuple, Koszul object, or detector conclusion. No change record is
needed: no existing definition or statement was changed, and no adaptation was made.

## Second reading by X2

1. Interface check: PASS. Read the full diff against the repository. The existing
   `supported_perfect_detector_affine_construction` signature is byte-for-byte identical,
   and its public imports and docstring are unchanged. The only added declaration in
   that module is a private proved helper. Both other modules are new; no existing
   definition, target, statement, or externally visible declaration was altered.
2. Proof check: PASS as a decomposition. All three files compile using `lcompile.py`.
   Scratch copies with `#print axioms` show only `propext`, `Classical.choice`, and
   `Quot.sound` for `qcoh_of_qcoh_terms`; the main theorem and the two split theorems
   additionally use `sorryAx`, as reported. Scanned all delivered files: exactly the
   two named `:= by sorry` theorem bodies remain; no forbidden declaration form or
   hollow definition is present. The explicit Koszul object is real data. The
   localization comparison determines the transport functor up to natural isomorphism;
   right adjoints are unique up to the adjunction comparison. Downstream perfection,
   stalk vanishing, Hom vanishing, and invertibility of units are invariant under these
   comparisons, so this is not arbitrary object selection from mere existence.
3. Split statements: PASS. Read the mathematical proofs and Stacks Tags
   [0A9A](https://stacks.math.columbia.edu/tag/0A9A),
   [0663](https://stacks.math.columbia.edu/tag/0663),
   [09IR](https://stacks.math.columbia.edu/tag/09IR), and
   [079W](https://stacks.math.columbia.edu/tag/079W).
   The geometry theorem concerns only the explicitly constructed finite Koszul complex;
   the transport theorem concerns any scheme isomorphism and arbitrary derived objects,
   without a detector conclusion. Each is a strict part of the argument, and neither
   restates the target. Checked r=0, zero ring, zero tuple, a tuple containing a unit,
   identity isomorphism, and empty/full opens: the assertions hold in each case.
   Independently searched with alternate concepts using leanfinder, loogle, grep, and
   `rg` in both library roots. Mathlib supplies restriction/stalk comparisons, exterior
   bases, and abstract localization tools, but no complete split statement. The existing
   regular-immersion Koszul theorem requires regularity and does not cover arbitrary
   tuples. Neither split can be fully closed by a short application of these results.
4. Route and pruning: PASS after reporting repair. Checked the finite basic-open cover,
   zero-locus equivalence, actual sheafification/localization, kernel/cokernel homology
   argument, and direction of the shift/Hom equivalence. The final application is to
   the existing `koszul_open_orthogonality` for that same complex. The unit has empty
   realized statement/step lists for this item, and its route is unchanged. Public
   imports of new modules supply symbols in their signatures; all additions used only
   for proofs in the main module are plain imports. Corrected `No longer needed` to
   list both old DAG dependencies removed directly, without claiming global pruning.
5. DAG check: PASS. Compared all three verbatim Lean statements with their node records,
   checked that every `proof_deps` is exactly the union of step `uses`, and read each
   source, proof origin, creation/blueprint record, and search record. The main node
   describes its actual proof, including the existing detector application. The two
   new nodes have the required complete statements, source-backed proof plans, Lean
   records, and three kinds of search. No change record is needed.

Second-reading changes: added the plain proof import
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral` to the transport module,
as required for the existing adjunction declaration named by its DAG proof plan; corrected
pruning accounting in the report; added this independent review and additional searches.
No proof body, statement, definition, or new hole was changed by the second reading.
