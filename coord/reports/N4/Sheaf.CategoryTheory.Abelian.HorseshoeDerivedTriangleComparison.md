## What changed

Added explicit injective resolution comparison and its naturality, and reduced the target
triangle construction to the endpoint homology formula and one boundary compatibility theorem.
The explicit comparison and its homology theorem compile without `sorry`; the target
uses the named boundary theorem below.

## Proved and sorry left

Proved: `CategoryTheory.injectiveResolutionDerivedComparison_homology` and
`CategoryTheory.injectiveResolutionDerivedComparison_naturality`.

Sorry left: `CategoryTheory.horseshoe_comparison_boundary`, which is a strict substatement of the
target: only the third square of the triangle, with explicit comparison maps and no homology
conclusion (node `lem-sc-p1-horseshoe-comparison-boundary`).
Closed `CategoryTheory.horseshoe_derived_triangle_comparison` by decomposition:
one hole closed, one strictly smaller boundary hole added. The whole delivered set compiles.

## No longer needed

Removed the redundant public import `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
from the new explicit-comparison module: `PlusSingle` already exposes its declarations.
The item's three original public imports stay because its signature uses their declarations.

The following old proof dependencies are no longer direct dependencies of the item's proof;
they remain in the new boundary lemma's proof plan or the proved comparison helpers:

- `def-sp-injective-resolutions`
- `lem-weil-pbc-degreewise-split-connecting-morphism`
- `lem-weil-pbc-degreewise-split-derived-triangle`
- `def-weil-abstract-derived-category`
- `def-weil-triangulated-category`
- `lem-weil-pbc-bounded-below-injectives-kinjective`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-triangle-morphism-extension`
- `lem-sf-derived-ses-triangle`
- `lem-weil-pbc-derived-direct-image-triangulated`
- `lem-weil-pbc-complex-ses-triangle`
- `lem-sp-derived-functor-single-identification`

No library module is claimed as globally pruned. The boundary node preserves the original
split-triangle route; this is a decomposition with net zero holes.

## Where the brief, the DAG or earlier work was wrong

The original target proof plan combines the construction, triangle compatibility, and endpoint
homology into one theorem. The Lean API supports a substantially shorter decomposition: explicit
comparison, naturality, and one boundary square. The boundary square is the only remaining
mathematical step. The original statement and all its binders remain unchanged.

Checked the cited Stacks pages 014Q, 05TE, 015B and the supporting exactness result
0159; these are available on the Stacks website although the local literature text is absent.
The preserved split-triangle route is also described in Stacks Section 13.10.
No unit statement or step is bypassed (the unit's `realized` arrays are empty).

Edge cases: degree zero is included in the homology calculation; it uses extension
homology naturality with `rfl` and no positive-degree assumption. The comparison is
valid for zero objects and for nonexact additive functors (its proved statements need
only additivity). The remaining boundary theorem has the original termwise exactness
and augmentation assumptions, retains the canonical sign, and is valid for a split
sequence as well as a nonsplit one. A zero functor makes all boundary maps zero.

Validation: the delivered set compiled with no warnings through `lcompile.py`, and
`deliver3.py --no-push` printed OK, pending the second reading. The unchanged
`NatComplexDerivedBoundary` source was compiled in the sandbox because its `.olean`
was missing from the shared snapshot; it is not delivered or adapted. Axiom probes
were run by the dry-run tool. There are no holes inside definitions or private lemmas.
The reduction has net zero holes; it is a decomposition, not a complete proof.

## New nodes

Added `lem-sc-p1-injective-resolution-derived-comparison`,
`lem-sc-p1-injective-resolution-derived-comparison-naturality`, and
`lem-sc-p1-horseshoe-comparison-boundary` in the target chapter. The first two are proved; the
third is left as a named theorem with a complete proof plan in its docstring.

## Second reading by N4

1. **Unchanged interface — pass.** Diffed the existing module against the repository:
   only its proof and two plain proof imports changed. The entire existing theorem
   signature, including all augmentation/exactness assumptions and both endpoint
   homology conclusions, is byte for byte unchanged. There are no adapted modules,
   statement changes, or change records.
2. **Kernel proof and construction — pass as a decomposition.** Recompiled all four
   modules through `lcompile.py`, with no errors or warnings. The sole source hole is
   `CategoryTheory.horseshoe_comparison_boundary`. Explicit scratch `#print axioms`
   probes show only `propext`, `Classical.choice`, `Quot.sound` for the comparison
   definition, its homology theorem and its naturality theorem; the boundary lemma
   and the item additionally use `sorryAx`. No forbidden declarations or attributes,
   private holes, or hollow definitions occur. The comparison uses Mathlib's actual
   `desc` construction, not a witness selected from the new boundary theorem.
3. **Split statement — pass.** The remaining lemma fixes the explicit endpoint maps
   and states exactly the third triangle square. It drops the existential triangle
   construction and both homology assertions, which are separately proved; it is
   a strict part of the argument, not a renamed target. Its cited docstring explains
   row splitting, the cone sign, augmentation transport, negative-Ext vanishing,
   derived-unit shift compatibility, and identification with the explicit lifts.
   Checked zero objects, the zero functor, degree zero in the homology formulas,
   and split sequences: no positive-degree, nonzero, or exact-functor assumption
   was smuggled in. The negative-Ext vanishing is used before applying v, so it does
   not incorrectly assert vanishing after deriving v. Independent LeanFinder and
   Loogle queries (recorded in `searches.jsonl`) and grep of Mathlib, Sheaf and the
   upstream derived-functor files found cone/single triangle isomorphisms and
   naturality tools, but no theorem directly closing the specified boundary square.
   Inspected `mapTrianglehIso`, `triangleOfSESIso`, and the proved
   `triangle_morphism_extension`: they support the documented route but do not
   provide its derived-unit comparison in one application.
4. **Shortest route and pruning — pass after reporting repair.** The first two
   squares are proved by naturality and both homology identities by the explicit
   comparison formula; only the boundary square remains. Removed one redundant
   public Mathlib import and successfully recompiled the set. The corrected
   `No longer needed` section lists every old direct proof dependency absent from
   the new proof, without claiming those retained by the boundary plan are globally
   pruned. Read `dag/units/sk-thm-picard-duality.json`: its realized statement and
   step arrays are empty, and the original split-triangle route remains in the
   boundary lemma; no realized unit step is bypassed.
5. **Nodes — pass after formatting repair.** Checked the existing node's three
   proof steps and dependency union against the constructed triangle and endpoint
   formulas. Checked each new node's chapter/unit, source, creation, searches,
   blueprint provenance, statement dependencies, proof plan, and Lean declaration.
   New `lean.statement` records now copy the exact multiline source signatures.
   The boundary node retains the original mathematical dependencies; the item's
   node records the actual reduction, not the old unimplemented proof plan.

Changes by this reader: removed one redundant public import, made the three new
Lean signature records verbatim, and completed the direct-dependency pruning report.
No additional hole was closed or added. The two new helper theorems are fully proved;
the original item is reduced to one new named boundary hole, so net hole progress is zero.
