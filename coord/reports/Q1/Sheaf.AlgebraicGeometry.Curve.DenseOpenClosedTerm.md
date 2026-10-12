## What changed

Proved AlgebraicGeometry.IsCurve.dense_open_closed_term in
Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm without changing its statement or docstring.
The proof constructs the actual open-closed short complex, forgets module coefficients,
proves that its closed complement has dimension at most zero, and computes both H¹ groups
through finite edge maps and the zero-dimensional cohomology theorem. The canonical H⁰
comparison is obtained from the zero-dimensional global-sections comparison and the already
proved cohomology_edgeMap_baseChange / bijective_edgeMap_baseChange declarations.
A proved private helper expresses cancellation of finite edge-map comparisons. No new deferred statement is introduced.

Added proof imports for DenseIrreducibleOpens, EtaleSheafHExtDerivedComparison,
ZeroDimensionalBaseChangeGeometricPoints, EtaleCohomologyPullbackDegreeZero,
EtaleEdgeMapBaseChange, CohomologyClopen, IdealSheaf.Subscheme, and Etale.Gabber.
Updated the item's DAG proof and proof_deps to match this argument.

Read Stacks Tag 0GJA, proof and remark (c), at
https://stacks.math.columbia.edu/tag/0GJA. All steps preserve the unit's dense-open
open-closed reduction. Empty schemes, full opens, zero-dimensional curves, nonreduced curves,
zero rings, and arbitrary (possibly infinite, nontorsion) module stalks are covered.

## Proved and sorry left

Proved the module's sole original sorry:
AlgebraicGeometry.IsCurve.dense_open_closed_term
(lem-pbc-k2-dense-open-closed-term).
Also proved private bijective_finite_pushforward_comparison.
No sorry remains in the delivery and no new sorry is added. This proof uses the library's
named zero-dimensional and dense-irreducible-open statements, as required by stage 3;
it does not claim that their entire transitive closure is already sorry-free.
The final module compiles cleanly with lcompile.py.

## No longer needed

Removed direct proof imports:
- Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit
- Sheaf.Paper.InverseImageStalkGerm
- WeilConjectures.SixFunctors.Finite.Exact
- Sheaf.AlgebraicGeometry.CurveCoefficientPair (unused; the curve setting is already
  available through the retained public Assertions import)

Removed direct proof dependencies from this node:
- lem-weil-pbc-closed-point-residue-field-base
- lem-weil-pbc-cohomology-pullback-derived-unit
- lem-weil-pbc-extension-by-zero-adjunction
- lem-weil-pbc-finite-type-over-noetherian
- lem-weil-pbc-inverse-image-stalk-germ
- lem-weil-pbc-noetherian-finitely-many-components
- lemma-weil-pbc-finite-direct-image-exact

These are no longer direct inputs to this proof. Some remain transitive inputs of the
retained geometry, global-sections or finite-edge-map modules; no claim is made that
those nodes disappear from the targets' entire closure. Kept public statement imports.
No other planned branch is required directly, and no new modules or nodes were created.

## Where the brief, the DAG or earlier work was wrong

The plan suppresses the conversion between derived cohomology and the Ext encoding Sheaf.H,
and the canonical compatibility of finite edge maps with base change. Both already have
usable named declarations: nonempty_sheafH_extDerivedIso and cohomology_edgeMap_baseChange.
The geometry can use exists_dense_irreducible_opens and inducing-map dimension monotonicity,
so no new finite-complement statement is necessary. The statement itself is unchanged
and no mathematical dispute was found.
The referenced local literature/stacks-project/etale-cohomology.tex file is absent on this
machine; the cited Tag 0GJA was read from the official Stacks site.
LeanFinder found only ring-theoretic etale-locus/cotangent results, Loogle did not know the
project-specific cohomologyMap identifier, and Mathlib grep found no matching comparison.
LeanSearch returned HTTP Internal Server Error and is recorded as unavailable in searches.jsonl.


## Second reading by Q1

1. Compared the delivered Lean module and node with the repository using diff and
   checked the existing theorem signature byte for byte. PASS: the signature, docstring,
   public imports and all existing definitions are unchanged. The only new declaration
   is a proved private finite-edge-map cancellation helper. No change record is needed.
2. Independently compiled the module with lcompile.py: clean, 18.5 seconds. Scanned
   for sorry, axiom, unsafe, opaque, implemented_by and extern: none. Compiled a scratch
   copy with #print axioms for both declarations: exactly propext, Classical.choice,
   Quot.sound and sorryAx, the latter inherited from still-open library inputs.
   PASS: no hole remains in this delivery; this closes one original hole and adds zero.
3. No split-off statements or new nodes exist. Checked the helper's composition
   cancellation against the edge-map base-change identity and finite exchange.
   PASS: it is a genuine proof for arbitrary abelian sheaves, with no constructibility
   or torsion restriction. Independent Mathlib grep for finite-pushforward comparison,
   closed cohomology and dense complements found no whole-statement replacement.
   Library search found finite_pushforward_pullback_comparison, whose public statement
   uses CurveCoefficientPair and converted coefficients; its generic helper is private.
   Thus it cannot replace this unrestricted helper directly. Checked empty X, full U,
   dimension zero, nonreduced X and zero coefficients: no nonempty-point choice or
   finiteness assumption on stalks is introduced.
4. Read sk-thm-p1.json and its realized routes, and independently read
   [Stacks Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA), proof and remark (c).
   PASS: the actual open-closed short complex, zero-dimensional closed complement,
   finite edge maps and canonical degree-zero comparison preserve the unit's dense-open
   reduction. Every retained proof import supplies declarations used by this argument;
   statement imports remain public and added proof imports are private. The existing
   private generic finite comparison elsewhere gives the same cancellation argument,
   with no shorter applicable public replacement. The report lists all seven old
   proof dependencies removed from the node; none is a unit-realizing node bypassed here.
5. Compared both node versions and read all eleven dependency records. PASS: only
   proof, proof_deps and proof_origin changed; proof_deps is exactly the union of step
   uses, and the steps match the Lean argument. The curve-setting dependency is used
   through IsCurve from Assertions; its legacy CurveCoefficientPair module is unnecessary.
   No new-node fields or statement-change record are required.

Second-reading changes: corrected the omitted CurveCoefficientPair import removal in
"No longer needed" and added this independent review and explicit axiom results.
The checked Lean proof and node need no repair.
