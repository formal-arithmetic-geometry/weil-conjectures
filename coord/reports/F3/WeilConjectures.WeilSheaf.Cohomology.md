## What changed

The two original declarations in `WeilConjectures.WeilSheaf.Cohomology` keep their exact
signatures. Their negative-degree branches now use the lower bound for a right derived
functor applied to a degree-zero object, after exact extension by zero. Global sections of
a zero Weil sheaf give a subsingleton carrier. The positive-degree branches apply the two
new sheaf-level vanishing statements listed below. All existing definitions and public
imports are unchanged. The three added imports in the item are proof-only imports.

The second reader moved the two open statements into their own modules under
`Sheaf.WeilSheaf`, as required by the brief. They concern zero cohomology sheaves of the
compactly supported direct image, before taking global sections. Their docstrings and nodes
now give the integral-lattice, finite-reduction, and Mittag--Leffler argument in full.

## Proved and sorry left

This delivery is a decomposition, not two completed proofs: two original direct holes are
closed and two strictly smaller geometric obligations remain. Net holes closed minus added
is zero; neither original theorem is claimed to be axiom-free or fully proved.

Original holes closed by declaration name:

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine`.

Their negative-degree branches are proved, using the private helpers
`isZero_homology_compactSupport_of_neg` and `subsingleton_globalSections_of_isZero`.
There is no direct `sorry` in the item's module. The two added holes, and the only direct
holes in the delivery, are:

- `AlgebraicGeometry.WeilSheaf.isZero_homology_compactSupport_of_isFinite_of_pos`,
  module `Sheaf.WeilSheaf.FiniteBoundaryPositive`,
  node `lem-a1-finite-boundary-cohomology-positive`.
- `AlgebraicGeometry.WeilSheaf.isZero_homology_compactSupport_of_isAffine_of_two_lt`,
  module `Sheaf.WeilSheaf.AffineCurveRangePositive`,
  node `lem-zl-affine-curve-range-positive`.

Each hole is the entire proof of a public named theorem with its source, complete proof
in words, and matching DAG node. No data is defined using a new unproved existence theorem.

## No longer needed

No imports or modules are pruned. The original finite-boundary node's dependency
`def-weil-ordinary-compact-cohomology` is retained. All seven original dependencies of the
affine-curve node are retained through its positive-degree child:
`lem-sc-compactification`, `def-compact-support-direct-image-detailed`,
`lem-sc-cohomological-dimension`, `sbc-thm-finiteness-finite-type`,
`prop-weil-pbc-direct-image-limits`, `lem-weil-pbc-mittag-leffler`, and
`def-weil-pbc-qbar-category`. They are delegated to the remaining geometric argument,
not made unnecessary. The parent proof records explicitly include the compact-support and
cohomology definitions used by the negative-degree proof. Thus no old proof dependency is
silently discarded.

## Where the brief, the DAG or earlier work was wrong

The first version reported the branches as proved without making the two-for-two
hole decomposition explicit. Its new nodes had no dependencies, shared an unrelated generic
proof paragraph, and did not explain the adic inverse-limit step. Its affine docstring
omitted the finiteness/Mittag--Leffler argument needed to avoid an extra degree-three term.
Its finite-scheme explanation omitted reduction: a nonreduced finite scheme need not itself
be a coproduct of field spectra. These points are repaired.

The available finite direct-image exactness and curve cohomological-dimension declarations
concern etale finite-torsion coefficients; they do not immediately prove the required
adic Weil compact-support comparison. No short proof of either remaining bridge was found.
The literature source files are not installed in this read-only checkout, so the source
arguments were checked against their full imported DAG proof text and the unit records.

## New nodes

`lem-a1-finite-boundary-cohomology-positive` states positive-degree vanishing of the Weil
cohomology sheaf of compactly supported direct image from a finite scheme. It separates the
geometric upper bound from the proved general lower bound and from taking global sections.
Its plan uses zero-dimensional etale cohomology, finite-reduction comparison, and the
Mittag--Leffler passage to adic coefficients, including the degree-one limit term.

`lem-zl-affine-curve-range-positive` states vanishing of that sheaf above degree two for a
smooth affine curve. Its plan retains smooth proper compactification, finite-coefficient
curve cohomological dimension, proper finiteness, derived limits, and Mittag--Leffler, exactly
the route of the original node. It adds no connectedness or lisse hypothesis. There are no
interface changes to existing declarations and no change records are needed.

## Second reading by F3

1. Compared the delivered item against the repository with `diff` and with the declaration
   parser: all existing signatures are identical, all definitions are identical, and the
   original public imports and visibility are unchanged. Only the assigned module and the
   two new modules are delivered; no adaptation of another group's module is involved.
   Verdict: pass.
2. Compiled all three modules in import order through `lcompile.py`, without errors or
   warnings. Checked for forbidden declarations and definition holes. A scratch copy prints
   the axioms of both helpers, both original declarations, and both split statements; all
   axioms are among `propext`, `Classical.choice`, `Quot.sound`, and the permitted `sorryAx`
   from open statements. The only direct sorries are the two listed new public theorems.
   Verdict: valid reduction, with two explicitly open geometric obligations.
3. Read both new statements and their docstrings. Checked the empty finite scheme, nonreduced
   finite schemes (nilpotent invariance), a point, disconnected smooth curves, zero sheaves,
   degree one in the finite case, and degree three in the curve case. Degree zero and the
   allowed curve degrees zero through two are not asserted to vanish. The finite and curve
   limit terms require Mittag--Leffler; the repaired explanations include it. Searched using
   `msearch.py` leanfinder (exact finite adic direct image), loogle
   (`DerivedCategory.isZero_of_isLE`), and grep, then searched `lean/` by homology,
   compact-support, finite-direct-image, and cohomological-dimension vocabulary. Found the
   finite-torsion results and generic derived bounds, but no exact adic bridge. Each new
   obligation omits the already proved negative branch and precedes the global-sections
   argument, so it is strictly a part of the parent argument. Verdict: pass as decomposition.
4. Traced the proof from each original hole. The negative branch uses the existing generic
   right-derived lower bound directly; the remaining obligations preserve the original
   geometric routes. Checked `dag/units/sk-i-dl-a1-local.json` and
   `dag/units/sk-l-dl-a1-endpoints.json`: both have empty `realized` attachments and neither
   names these nodes as a realized unit step. No realized route is bypassed. The original
   three public imports supply the existing API; the three new private imports supply the
   lower-bound API and the two new statements. New modules import only what their statements
   need. The old dependency list is accounted for under No longer needed. Verdict: pass.
5. Compared all four node files with their Lean declarations and the original plans.
   Corrected the finite parent's inaccurate reference to a finite pushforward in the
   negative proof: the implementation uses the proper map of the chosen compactification.
   New nodes now have self-contained statements with context, exact Lean signatures,
   accurate module/file/declaration records, recorded searches (LeanSearch unavailable; LeanFinder, Loogle, and grep checked), sources, creation and
   blueprint records, and proof dependencies equal to the union of their step uses.
   Existing nodes change only their proof, proof_deps, and proof_origin. Verdict: pass.

Changes made at second reading: moved both open statements to separate Sheaf modules;
reformulated them as cohomology-sheaf vanishing; expanded their proofs in words and corrected
nilpotent and inverse-limit details; repaired their node statements, searches and dependencies;
corrected the parent routes and rewrote the report to count this as a two-for-two decomposition.

Search availability correction: the required LeanSearch service returned Internal Server Error
for both new nodes. Their records now explicitly say unavailable, with no mathematical
verdict. The successful LeanFinder, Loogle and grep searches supply the independent checks.
