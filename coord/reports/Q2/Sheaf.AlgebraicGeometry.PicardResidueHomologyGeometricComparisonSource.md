## What changed

The source theorem now composes two additive equivalences. Two intermediate comparison modules were added for residue homology to derived fibre cohomology and for derived fibre cohomology to structure-sheaf cohomology.

## Proved and sorry left

This is a decomposition, not an axiom-free proof or a claim of positive ledger progress.

One original local hole is closed:
- AlgebraicGeometry.Scheme.picard_residue_homology_geometric_comparison_source,
  node new-picard-residue-homology-comparison-source.

Two fresh named holes are added:
- AlgebraicGeometry.Scheme.picard_residue_homology_source_residue_comparison,
  node new-picard-residue-homology-comparison-source-residue.
- AlgebraicGeometry.Scheme.picard_residue_homology_source_fibre_comparison,
  node new-picard-residue-homology-comparison-source-fibre.

Both are exact public theorem holes in new modules, each with a source and a full
natural-language proof. The original theorem composes their additive equivalences.
It still depends on sorryAx. Thus zero of the one original theorem is proved
without sorryAx; one of one original local bodies is reduced, with two split-off
statements. Direct hole accounting is one closed minus two added; the maintainer's
pinned sorry ledger determines the full import-closure figures.

## No longer needed

No repository module or original planned node is pruned: the original node's
proof_deps was empty. The original module's existing public imports are preserved.
Its two new comparison imports are plain proof imports.

Within the new residue module, the unnecessary geometry, coefficient and
direct-image imports copied by the first worker are removed. Its public imports
are only AffineResidueCycleHomology, DerivedFiberBetti and PerfectComplex; the
affine K-flat model, module quotient API and module-flatness API are proof imports.
Within the new fibre module, AffineResidueCycleHomology and PerfectComplex are
removed. Its comparison, scalar transport, sections-of-higher-image and
single-object derived-functor imports are plain proof imports for its documented
proof dependencies. These removals from newly proposed modules do not prune any
previously landed library module.

## Where the brief, the DAG or earlier work was wrong

The DAG presented the full geometric comparison as one unimplemented step. The
composition is a complete reduction of that unchanged statement, but not an
axiom-free proof. The first worker copied all the original hypotheses into both
intermediates, omitted their module docstrings, and left the new nodes with
conclusion-only statements and uncited non-elementary steps. The second reading
repairs these faults; it does not claim that merely relocating holes is progress.

## New nodes

`new-picard-residue-homology-comparison-source-residue` and `new-picard-residue-homology-comparison-source-fibre` are the two intermediate comparison statements. Their proofs use the affine K-flat residue model, strict-perfect projective retractions, proper flat derived base change, and the supplied trivialization `τ`.

## Earlier second reading (a previous round; superseded)

The item signature is unchanged. The two intermediate statements are strict parts of the argument: one identifies the explicit quotient with derived fibre homology, and the other identifies derived fibre homology with structure-sheaf cohomology. Their additive equivalences compose by `AddEquiv.trans`.

## Second reading by Q2

1. **Existing interfaces. PASS.** I diffed every proposed module against this
   machine's repository version. Only GeometricComparisonSource existed;
   the other two modules are new. I also compared the complete theorem signature
   as a string, including all instances, binders and the conclusion: it is byte
   for byte identical. The existing definition bodies, public imports and
   visibility are unchanged. There are no definition or target changes and no
   change records are needed. The main body only defines its local E, obtains
   two additive equivalences inside a proposition proof, and composes them.
   No data definition chooses an arbitrary witness from a sorry theorem.

2. **Lean proof and axioms. PASS as a decomposition.** All three final modules
   compile cleanly in import order through lcompile.py. A scratch copy of the
   main module printed axioms for all three declarations: each reports only
   propext, Classical.choice, Quot.sound and sorryAx. The main module contains
   zero sorry tokens; each new module contains exactly one, the named theorem
   listed above with body exactly by sorry. There is no axiom, unsafe, opaque,
   implemented_by, extern or kernel-check bypass. No new definition has a hole.
   Every final source line is at most 100 characters.

3. **Each split-off statement. PASS after repairs.** I read the actual
   definitions of affineResidueCycleHomology, IsStrictlyPerfect,
   derivedFiberCohomology and schemeDerivedDirectImage, and the signatures of
   affine_kFlat_residuePullback_model, affineFree_residueSections_cohomologyLinearEquiv,
   exists_localizedStrictPerfectResidueHomology_iso,
   nonempty_kFlat_stalk_residueCohomology_linearEquiv,
   isIso_derivedBaseChange_of_flat_invertible, isIso_canonicalSinglePullbackMap,
   tensorPullbackCompositionIso and
   exists_addEquiv_sections_higherDirectImage_H.

   The residue lemma is now for any E represented by K. It needs neither f, L,
   k, s, hw nor tau. It proves only the affine quotient-to-derived-fibre step.
   Its docstring explains projective retractions, bounded K-flatness, natural
   counit reconstruction, scalar-field identification, differential compatibility,
   exact sections and the module homology quotient. The fibre lemma no longer
   assumes U, p, K, hK or hE (or localized derived-category instances); it proves
   only the geometric base-change/trivialization step. Its docstring specifies
   the cartesian square, invertibility hypotheses, residue field isomorphism,
   fibre-product identification and higher-direct-image sections comparison.
   These are independent strict parts of the original argument.

   Small cases checked mathematically: for K=0 both residue sides vanish;
   for a two-term identity differential in degrees 0 and 1 the entire
   degree-one cycle module is killed by boundaries, so the quotient is zero;
   for a single term in degree 1 it is the residue extension of that term.
   Finite projective nonfree terms remain valid because the construction uses
   retractions, not frames. For A=k[t] and p=(0), the residue field is k(t), not
   A/p; affinity and the field isomorphisms are essential. An empty U cannot
   satisfy hwU. For f=id and a fibre-trivialized line bundle, both fibre H1
   groups vanish. Empty geometric fibres give two zero groups. Positive-genus
   proper smooth fibres can have nonzero H1, so the argument uses an equivalence,
   not vanishing. No Noetherian, connectedness or closed-point assumption was
   inserted.

   I read Stacks
   [01IB](https://stacks.math.columbia.edu/tag/01IB),
   [064K](https://stacks.math.columbia.edu/tag/064K),
   [06YJ](https://stacks.math.columbia.edu/tag/06YJ),
   [010V](https://stacks.math.columbia.edu/tag/010V),
   [0A1D](https://stacks.math.columbia.edu/tag/0A1D),
   [0B91](https://stacks.math.columbia.edu/tag/0B91),
   [0BF2](https://stacks.math.columbia.edu/tag/0BF2) and
   [01XK](https://stacks.math.columbia.edu/tag/01XK).
   The 0BF2 displayed fibre comparison explains the application, whereas 0A1D
   and 0B91 supply the actual base-change hypotheses. Properness plus local
   finite presentation gives the required finite presentation for 0B91.
   The open/closed immersion residue maps are isomorphisms, so the identification
   with the fibre at s introduces no field-extension assumption.

   Independent searches used different queries: Loogle homology/quotient;
   LeanFinder derived pullback at residue points and homology as cycles modulo
   boundaries; msearch grep residueSections/derivedFiberCohomology/direct-image
   cohomology; and repository/upstream rg. LeanSearch returned Internal Server
   Error, recorded without a mathematical verdict. LeanFinder found
   ShortComplex.moduleCatLeftHomologyData and its quotient API; I read
   ShortComplex.moduleCatHomologyIso and named it in the residue plan. This
   proves the final algebraic quotient identification, not the affine derived
   identification. The finite-free affine theorem assumes free term
   isomorphisms, which hK's projective retracts do not provide. The localized
   theorem is degree zero and uses stalk tensors rather than the actual
   section quotient; the K-flat stalk theorem assumes a global sheaf model.
   None is a duplicate of either new statement. The geometric argument now
   explicitly reuses the existing flat-invertible base-change and affine-base
   higher-image sections theorems rather than restating them.

4. **Top-down route and pruning. PASS.** The main proof first opens the original
   hole and composes the two necessary comparisons through
   derivedFiberCohomology W E 1 w. Each intermediate has a distinct endpoint and
   strictly smaller scope. No lemma merely renames the whole original assertion.
   The original proof_deps was empty, so there is no omitted old dependency to
   list under No longer needed. The item and both new nodes remain in
   sk-prop-av-cube, sec-abelian-varieties. I read that unit's complete statement,
   its one step applying the general cube theorem and its realized record
   (empty statement and empty step array entries in the repository). No unit
   record, realization or route is changed; this local reduction supplies the
   same geometric comparison used below that route.

5. **DAG/Lean agreement. PASS after repairs.** The parent proof and its exact
   dependency union are the residue and fibre comparison nodes. The two new
   statements now include every hypothesis through their verbatim full Lean
   signatures. Each proof is expanded into real steps: elementary retract and
   scalar calculations are distinguished from the named existing comparison
   dependencies. Their proof_deps equal the union of uses and every referenced
   node exists. I checked each dependency's Lean signature before citing it,
   updated sources/proof_origin and replaced unsupported search summaries with
   the actual recorded searches. New nodes have source, searches, created,
   blueprint provenance, chapter/unit, status, lean_audit and complete lean
   records. Existing node changes are restricted to the allowed proof fields.

**Second-reader changes.** Removed irrelevant hypotheses from the two new
statements; adapted only the main proof's calls; supplied both module docstrings
and full natural-language proofs; pruned imports copied into the new modules;
used plain imports for the actual lower comparison tools; made the two new node
statements self-contained, corrected their proof dependencies and search records;
and corrected the report to call the result a decomposition with two remaining
holes. No lower hole was closed during this reading.
