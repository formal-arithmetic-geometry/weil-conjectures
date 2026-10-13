## What changed

Proved `affineOpenSections_pair_eventual_agreement` without changing its signature.
The proof constructs the affine overlap over D(j), kills the difference of its two
restricted sections by unit naturality, and descends its zero open on the cofiltered
tail using `isLimitBaseChangeCone` and `exists_map_eq_top`. Every test object factors
through that eventual overlap and then through the zero open.

Added `Sheaf.Paper.EtaleUnitZeroNeighbourhood`, which proves the zero-neighbourhood
statement for a section whose unit is zero on the whole base-changed object. Its
pointed witness and open-union argument adapt the proved geometric-stalk construction
in `EtaleSectionZeroNeighbourhood`; no existing module is adapted.

Added proof-only imports of this new module and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`. Updated the item's
DAG proof to match this route and supplied the new theorem's node.

## Proved and sorry left

Closed the sole original hole: `affineOpenSections_pair_eventual_agreement`.
Added zero holes: `etaleUnit_zero_neighbourhood` and all private helpers are proved.
No `sorry` remains in the delivered modules. This is a proof, not a decomposition.

## No longer needed

Second reading removed the redundant proof-only import
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` from the new helper module;
its needed openness instances are already supplied by the etale imports.

No original import was removed: the original imports supply the unchanged signature.
The item's planned use of `lem-weil-pbc-etale-section-zero-neighbourhood`
(`Sheaf.Paper.EtaleSectionZeroNeighbourhood`),
`lem-weil-pbc-etale-inverse-image-restriction`
(`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`), and
`lem-weil-pbc-cartesian-square-pasting`
(`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`) is unnecessary.
The original proof-dependency entry `def-weil-pbc-category-colimit` is unnecessary
as a separate proof step (its cone vocabulary remains in the statement).
No localization of the adjunction, localization-restriction comparison, or pullback
pasting theorem is used. The affine-overlap tail instead uses the already proved
`lem-weil-pbc-scheme-over-limit`. The removed planned dependencies may remain needed
elsewhere in the library; this report only prunes this item's route.

## Where the brief, the DAG or earlier work was wrong

The planned localization step can be replaced by direct unit vanishing on the
whole base-changed overlap and the general-site comap stalk isomorphism.
The affine overlap is affine because its common base D(j) is affine, not because
arbitrary intersections of affine opens are affine. No hypothesis or interface
was changed. The open-immersion assumptions on D are retained exactly as supplied.

Checked the source statements at Stacks Tags 09XM, 03Q1 (3), and 03Q6 (2).
For empty base change the new theorem constructs an empty union and applies
separatedness for the empty covering. Empty overlaps, a zero section or zero sheaf,
and singleton diagrams require no extra assumptions. The tail argument uses
compactness of its affine stages, with no compactness assumption on the zero open.

The unit's realized statements and proof steps are not bypassed: this item is
below the unit level, and the existing unit record stays unchanged.

## New nodes

`lem-weil-pbc-etale-unit-zero-neighbourhood`:
the global declaration `etaleUnit_zero_neighbourhood` in
`Sheaf.Paper.EtaleUnitZeroNeighbourhood`. This is a proved, local
zero-neighbourhood theorem for one section; it has no inverse system or pair of
representatives. It supplies the first step of the overlap proof. Searches are
recorded in `searches.jsonl` and the node; LeanSearch was unavailable, while
LeanFinder and grep found no exact theorem. Blueprint searches for "zero
neighbourhood" and "equality locus" found no match. The existing pointed-map
zero-neighbourhood theorem has a different hypothesis and is used as the model
for the proof, rather than restated as an additional hole.

## Second reading by P2

1. PASS: Compared the item module with the repository using `diff`; the existing
   declaration signature is byte for byte unchanged. No existing definition,
   visibility, target statement or public import changed; no change record is needed.
   The only additional public declaration is the proved theorem in the new module.
2. PASS: Both modules compile locally through `lcompile.py`. Neither contains
   `sorry`, axioms, unsafe declarations, opaque declarations or external overrides.
   A scratch import probe with `#print axioms` for
   `affineOpenSections_pair_eventual_agreement` and `etaleUnit_zero_neighbourhood`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound` for each.
   There are no definitions choosing data from an unproved existence statement:
   the pointed witnesses used in the open union come from the proved private lemma.
3. PASS: There are no split-off holes. Read the new proved theorem and its pointed
   helper: the supplied left adjoint is compared with the canonical one via
   `leftAdjointUniq`; the unit-compatible comap-stalk isomorphism detects the zero
   germ; its equality witness yields an etale neighbourhood with zero restriction.
   The union of its images is covered by those neighbourhoods, so separatedness
   proves the required zero restriction. Empty base change gives an empty cover;
   zero sections and empty overlaps require no added hypothesis. Repeated searches
   with different wording through LeanFinder, Loogle and grep, and searched both
   library roots. The ringed-space germ lemma has the wrong sheaf/site; the existing
   `etaleSection_zero_neighbourhood` assumes a chosen map into V and vanishing
   after its terminal restriction, rather than whole-object unit vanishing.
   The set-valued agreement-open criteria also have different coefficients and
   adjunctions. None is an exact replacement for the new theorem.
4. PASS: The target opens its original hole, subtracts sections on the affine
   overlap, uses the proved local zero-neighbourhood result, and descends open
   containment directly by `isLimitBaseChangeCone` and `exists_map_eq_top`.
   Each test object factors through that eventual overlap and its zero open.
   No unnecessarily holed localization theorem is used. Checked the original
   proof-dependency list: all four discarded entries are named above under
   No longer needed; the limit-containment entry stays. Checked sk-thm-p1's
   `realized` record: neither this item nor any discarded dependency realizes
   a unit step, so the unit route is retained. Original public imports supply
   the unchanged interface; proof-only imports remain private to these proofs.
   The original theorem docstring still describes localization; the actual route
   is the direct whole-base-change unit argument documented in this report and DAG.
5. PASS: Compared the existing node with the repository; only its proof,
   proof_deps and proof_origin change. Its proof_deps is the union of step uses,
   and the Lean declarations implement all three steps. The new node has its
   source, complete proof, dependency lists, searches, creation and blueprint
   records, chapter/unit, and verbatim Lean signature. Checked its steps against
   the pointed helper and the open-union proof. Sources 09XM, 03Q1(3), and 03Q6(2)
   support the equality-open, pullback-stalk and limit arguments respectively.

Changed only one Lean import: removed redundant UniversallyOpen from the new
module after compiling a scratch copy without it. Added this review and its
independent search/axiom evidence; no proof or statement repair was needed.
