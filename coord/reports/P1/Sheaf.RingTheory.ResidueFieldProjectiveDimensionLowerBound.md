## What changed

Proved `IsLocalRing.finrank_cotangentSpace_le_of_hasProjectiveResolutionLE` without changing
its signature or public imports. Replaced the proposed Koszul/minimal-resolution route with
two already proved declarations in
`WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension`:
`IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField` and
`IsRegularLocalRing.projectiveDimension_quotient_maximalIdeal`.

The Lean glue unpacks the given bounded resolution, uses Mathlib's
`ProjectiveResolution.extMk_surjective` and `extMk_zero` to prove the Ext-vanishing projective
dimension bound, obtains regularity, transports the residue field to the universe-shrunk
quotient, rewrites projective dimension as the number of maximal-ideal generators, and uses
Mathlib's cotangent-space equality to conclude the natural-number inequality. No witness is
chosen to define data from an unproved existence theorem.

Updated the item's proof docstring and DAG proof, proof dependencies and origin. Recorded
both source-library results in two new nodes, with `lean.existing = true`; there are no new
Lean modules and no new unproved statements. These nodes attach existing proofs rather than
split work off. The source Serre proof uses induction, change of rings and a residue-field
retract, independently of this item; the import-cycle checker confirms that its module does
not reach this item. The item is not a statement or proof-step realization in `sk-thm-p1`:
this change is below the unit level, with every unit realization retained.

Local compilation passes without warnings. Separate `#print axioms` checks on the two reused
source declarations show exactly `propext`, `Classical.choice` and `Quot.sound`. The dry run
checks the delivered theorem as well. Edge cases reviewed: embedding dimension zero,
resolution length zero, arbitrary `d` larger than the minimal length, and arbitrary universe
`u`; the proof includes each without an extra hypothesis. A singular local ring is not
silently excluded: regularity is deduced from its bounded residue-field resolution.

## Proved and sorry left

Closed one hole:
`IsLocalRing.finrank_cotangentSpace_le_of_hasProjectiveResolutionLE`
(node `lem-weil-pbc-residue-field-pd-ge-embedding-dimension`).

Zero holes remain in the item; zero holes were added or split off. This is a proof, not a
decomposition. Both declarations attached to the new nodes are already fully proved and
have only the three permitted axioms.

## No longer needed

Removed proof imports:

- `Sheaf.Paper.FreeComplexMapsToResolution`
  (`lem-weil-pbc-free-complex-maps-to-resolution`).
- `Sheaf.RingTheory.MinimalFiniteFreeResolutionLocal`
  (`lem-weil-pbc-minimal-finite-free-resolution-local`).

Those modules and their Koszul-comparison/minimal-resolution branches are unnecessary for
this proof. Other targets may still reach them; this report does not assert their global
unreachability.

Removed old direct proof-dependency edges to `def-weil-pbc-noetherian-ring`,
`def-weil-pbc-free-module`, `def-weil-finitely-generated-module`,
`def-weil-pbc-exact-sequence`, `lem-weil-pbc-minimal-finite-free-resolution-local`, and
`lem-weil-pbc-free-complex-maps-to-resolution`. The Noetherian hypothesis remains in the
unchanged signature and is required by the source Serre theorem. Retained
`def-weil-pbc-finite-global-dimension`; both public imports remain needed by the signature.

The proof uses neither a newly constructed Koszul complex, its mod-maximal-ideal
injectivity, nor minimal finite free resolutions. No additional old direct proof import
remains to prune. Added only the proof imports
`Mathlib.CategoryTheory.Abelian.Projective.Ext` and
`WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension`, each used explicitly.

## Where the brief, the DAG or earlier work was wrong

The statement is correct and unchanged. The old plan missed the fully proved source-library
Serre theorem and regular-local projective-dimension formula. The Stacks proof of 00OC
cites 00OA, so using that natural-language proof alone would be circular here. The actual
source Lean proof of Serre's theorem instead uses an independent induction argument; its
axiom check and import-direction check establish that reuse here is legitimate.

Searches: repository/DAG declaration and concept searches found no node carrying either
source declaration; `blueprint_refs.py` found zero blueprint matches for the two focused
queries. LeanFinder searches returned cotangent-space, DVR and Krull-dimension lemmas only.
Loogle found no usable bounded-resolution bridge. LeanSearch was attempted for Serre and
for the regular-local residue-field formula, but returned service unavailable; no absence
claim is inferred from that failure. Mathlib/source grep found the regular-sequence quotient
formula in Mathlib and the two exact fully proved declarations in the source library.

## New nodes

`lem-weil-pbc-regular-of-finite-residue-field-pd` attaches
`IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField`, the exact regularity
implication needed after the Ext-vanishing bridge. Its proof record describes the independent
source induction; it introduces no hole. Source: the existing Lean proof and the statement
of Stacks 00OC (1) implies (3).

`lem-weil-pbc-regular-residue-field-pd-eq-generators` attaches
`IsRegularLocalRing.projectiveDimension_quotient_maximalIdeal`, including its universe
shrinking hypothesis. Its proof record follows the existing regular-sequence construction
and Mathlib's quotient projective-dimension formula. It introduces no hole.

No change record is required: no existing statement, definition, signature or public
visibility changed, and no other module was adapted.

## Second reading by P1

1. PASS: diffed the only delivered Lean module against the repository. The existing
   theorem signature is byte for byte unchanged; both public imports and exposure are
   unchanged. Only proof imports, proof documentation and the proof changed. There are
   no definition or statement changes, forced adaptations or change records.
2. PASS: compiled the module locally without errors or warnings. A scratch copy with
   `#print axioms IsLocalRing.finrank_cotangentSpace_le_of_hasProjectiveResolutionLE`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`. Independently recompiled
   the axiom probe for both source declarations with the same result. No holes or
   forbidden declarations occur. The bounded resolution is unpacked as a proof
   hypothesis, with no arbitrary data defined from an unproved existence theorem.
3. PASS: no statements were split off. Both new nodes attach existing, fully proved
   source results; their signatures match those declarations. Reviewed the independent
   Serre induction and regular-sequence quotient formula. Length zero, zero embedding
   dimension, nonminimal bounds and universe shrinking are covered. Independent
   LeanFinder search for vanishing projective-resolution terms returned only the
   dimension definitions and inequalities already used; Loogle did not resolve the
   projective-resolution identifier, so that search gives no absence evidence. Local
   Mathlib/source/Sheaf searches found no shorter bounded-resolution bridge or duplicate
   lower-bound theorem.
4. PASS: the proof starts at the target and uses proved source/Mathlib results throughout.
   Both proof imports are needed: deleting the Ext import in a scratch copy fails at
   `P.extMk_surjective`; the source import supplies both regular-local results. The two
   public imports provide signature objects. Checked all seven old direct proof
   dependencies: the report lists all six retired edges and the retained global-dimension
   definition. The item's node is absent from the unit's `realized` statement and steps;
   no unit or chapter route is changed.
5. PASS: existing node changes are confined to `proof`, `proof_deps`, `proof_origin`.
   Its four steps agree with the Lean: Ext vanishing, Serre regularity, the shrunk
   residue-field formula, and cotangent-space rank/cast conversion. Each new node has
   the required source, complete argument, dependency union, search records, creation,
   blueprint ancestry, chapter/unit and exact existing-declaration record.

Second reading changed only this report, adding the independent checks and verdicts.
No Lean proof or DAG repair was needed. Closed one original hole; added zero holes.
