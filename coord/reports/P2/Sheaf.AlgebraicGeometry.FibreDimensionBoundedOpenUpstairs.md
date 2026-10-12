## What changed

Replaced the earlier principal-open restatement with a genuine reduction.
`Algebra.fibre_dimension_bounded_open_upstairs` now applies the existing theorem
`Algebra.exists_quasiFinite_over_polynomial_algebra` (Tag 00QE), constructs `D(g)`, and
applies `Algebra.fibre_dimension_le_of_quasiFinite_polynomial_localization` pointwise.
The latter is a new intermediate theorem in
`Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairsAux`: its inputs are a given
quasi-finite polynomial factorization and a prime avoiding g, without an initial local
dimension hypothesis or a neighbourhood-existence conclusion. It is strictly the
fibre-comparison part of the original proof, not the original statement repackaged.
All existing signatures and public imports remain unchanged. Updated the main DAG node
and replaced the earlier uncommitted auxiliary node. No definitions or target statements
changed, no forced adaptations, and no data definitions choose unproved witnesses.
The existential factorization is eliminated only inside a proof of a proposition.

## Proved and sorry left

Closed the original hole in `Algebra.fibre_dimension_bounded_open_upstairs`
(node `lem-weil-pbc-fibre-dimension-bounded-open-upstairs`).
Added one hole: `Algebra.fibre_dimension_le_of_quasiFinite_polynomial_localization`
(node `lem-weil-pbc-fibre-dimension-bound-of-polynomial-factorization`). Its proof is
exactly `by sorry`; its docstring and node give the residue-field base change,
global-dimension bound and open-localization argument. This is a decomposition:
one original hole closed and one genuinely smaller new hole added, net zero holes.
The existing 00QE and 00QG theorems remain dependencies; they were not proved here.
The former original hole `Algebra.exists_basicOpen_fibre_dimension_le` was from an
uncommitted earlier attempt and is removed, not counted as project progress.
Both sandbox modules compile together with `lcompile.py --all` (exit 0).
The required delivery dry run now prints OK: local compilation and preflight pass,
except for the second reading reserved for the next worker. Nothing was pushed.

## No longer needed

Second reading also removed the auxiliary module's unused proof-only imports
`Mathlib.RingTheory.Localization.BaseChange` and
`Mathlib.RingTheory.TensorProduct.MvPolynomial`; no additional project node or
module is claimed pruned by removing those imports.

Removed the main module's direct proof imports
`Sheaf.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra` and
`Sheaf.RingTheory.QuasiFiniteFourRings`; their dependency imports are retained in the
new intermediate module, so they are not pruned from the target closure.
Removed `Sheaf.Topology.DimensionSupremumLocalDimensions` and its node
`lem-weil-pbc-dimension-supremum-local-dimensions` from this proof route: the needed
local <= global inequality follows directly by taking the whole-space neighbourhood
in the infimum defining local dimension. No other original nodes are claimed pruned.
Retained/reinstated `Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra`, which the earlier
attempt incorrectly said was no longer needed. Removed the uncommitted restatement
node `lem-weil-pbc-fibre-dimension-bounded-open-upstairs-basic-open`.

## Where the brief, the DAG or earlier work was wrong

The earlier auxiliary principal-open existence statement just repackaged the original
statement and violated the brief's prohibition on moving a sorry under another name.
It also lacked a blueprint tag and complete proof in its declaration docstring, recorded
only one search kind and claimed dependencies were pruned when they remained needed.
Those defects are corrected. The original mathematical DAG plan remains valid; only
the full supremum-of-local-dimensions result is unnecessary for its one inequality.
No unit statement or realized step is bypassed: the original node is not itself one of
`sk-thm-p1`'s realized nodes, and its source argument through 00QE and 00QG is preserved.
The literature checkout is absent locally; the cited Stacks 00QH and 00QG pages were
read from the official Stacks site. LeanSearch currently returns Internal Server Error;
LeanFinder, Loogle and local source searches were also performed.

The first dry run reproduced the delivery tool failure from the earlier attempt:
`deliver3.py` line 65 imports `refuse_missing` and `source_roots` from `import_cycles`,
but the repository's `tools/import_cycles.py` lacks `refuse_missing`, raising
`ImportError: cannot import name 'refuse_missing' from 'import_cycles'`.
A later dry run, after both modules compiled, passed that API import but failed with:
`FAILED: missing import source modules` for Mathlib.RingTheory.FiniteType,
Mathlib.RingTheory.LocalRing.ResidueField.Fiber, Mathlib.Algebra.MvPolynomial.Basic,
Mathlib.RingTheory.Localization.Away.Basic, Mathlib.RingTheory.Localization.BaseChange,
and Mathlib.RingTheory.TensorProduct.MvPolynomial. The source file for FiniteType was
checked and exists in both the specified source checkout and the compiler's package
checkout. Thus this latest failure is in source-root discovery by the delivery guard,
not an unavailable module or a Lean compilation error.
No tool or read-only repository file was edited to work around either failure.
On this continuation both modules were compiled again with `lcompile.py --all`
(exit 0), and `deliver3.py --no-push` printed OK. The previous source-discovery
blockage is resolved in the current tool installation. No tool or repository file
was changed by this worker. Nothing was pushed.

## New nodes

`lem-weil-pbc-fibre-dimension-bound-of-polynomial-factorization` records exactly the
remaining steps after Tag 00QE: quasi-finite base change, the 00QG global bound, and
transport to the original fibre point on the principal open. Its statement includes
all objects and hypotheses. The cases n = 0, empty D(g), and noninjective polynomial
maps are covered by the same argument. There are no change records.

## Second reading by P2

1. Compared the main module with the repository using diff. The existing theorem
signature and docstring are byte for byte unchanged. Only its proof and private
proof imports change. The auxiliary module is new; there are no changed definitions,
changed target statements, or change records. Verdict: pass.

2. Compiled both delivered modules with lcompile.py in import order. A scratch copy
with explicit #print axioms for both declarations printed only propext,
Classical.choice, Quot.sound, and sorryAx. The latter is expected from the named
auxiliary hole and existing 00QE/00QG dependencies. The main theorem contains no
sorry; the sole added sorry is exactly the named auxiliary theorem reported above.
There are no forbidden declarations, hollow definitions, or witness-selecting data
definitions. Verdict: pass as a decomposition, net zero holes, not a complete proof.

3. Read the auxiliary statement, docstring, node, and the actual declarations of
00QE, 00QG, and the four-rings theorem. Verified the source reduction against
[Stacks 00QH](https://stacks.math.columbia.edu/tag/00QH),
[00QG](https://stacks.math.columbia.edu/tag/00QG), and
[00PN](https://stacks.math.columbia.edu/tag/00PN).
The canonical R-algebra condition on f supplies the commuting base-change square;
localization preserves the original fibre point on D(g). The bound remains valid
for n = 0, noninjective f, and arbitrary commutative base rings; an empty D(g),
including a zero ring, has no q satisfying hg. This lemma does not assume the
original local-dimension equality or assert existence of a neighbourhood: it is
strictly the remaining fibre-comparison argument. Repeated semantic and grep
searches with different terms using msearch.py and rg on both source roots. Found
no duplicate. The upstream scheme dimension equality needs universal closedness
and surjectivity, neither available here. Verdict: pass. Closing this hole requires
polynomial base change and fibre-point transport, rather than a short tactic repair.

4. The main proof first applies the existing 00QE theorem and explicitly chooses
D(g), then uses the smaller comparison lemma pointwise. Checked the unit
sk-thm-p1 realized statement and all four realized step lists: this node is below
those steps and no unit route is bypassed. The old proof dependencies other than
the supremum-of-local-dimensions theorem remain needed through the auxiliary;
they are moved, not claimed globally pruned. Removed two unused proof-only
Mathlib imports from the auxiliary: Localization.BaseChange and
TensorProduct.MvPolynomial. Retained its declared Sheaf proof-dependency imports
as the plan for its outstanding proof. All public imports serve signatures.
Verdict: pass; no further closure pruning claimed.

5. Checked that the main node records the actual 00QE / basic-open / comparison
proof and that the auxiliary node's dependency union equals the uses in its proof
steps. Its Lean statement matches the new declaration verbatim, and it has the
source, blueprint ancestry, creation, search, and status fields required by the
brief. Corrected stale d / V notation in the auxiliary node to n / D(g), and
recorded the second reader's additional search. Verdict: pass after those fixes.

Second reading changed only the two unused proof imports, auxiliary DAG proof
notation and search evidence, and this report. No Lean proof or signature changed.
