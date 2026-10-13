## What changed

The original module now contains a complete Lean proof of
`AlgebraicGeometry.polynomial_chart_flat_stalk_iff_fibre_depth_and_dimension`
from the existing local algebra inputs and one new geometric comparison. Its
signature and all original public imports are unchanged. All added imports are
ordinary proof imports:

- `Sheaf.AlgebraicGeometry.PolynomialChartLocalAlgebra`
- `Sheaf.RingTheory.MiracleFlatness`
- `Sheaf.RingTheory.FlatLocalDepthFormula`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`
- `Sheaf.RingTheory.DepthLeSupportDimension`
- `Sheaf.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`

The private, proved helper `regular_local_depth_eq` chooses actual finite
maximal-ideal generators, applies the existing regular-generators theorem, and
uses the definition of depth and the support-dimension bound to prove depth
exactly equals dimension. No new hole is needed for this calculation.

The forward proof applies the flat local depth formula, proves depth zero of
the zero-dimensional closed fibre by the support bound, uses faithful flatness
and the existing local dimension inequality to squeeze the two dimensions,
and obtains both conclusions. The reverse proof cancels the common finite
transcendence-degree contribution, converts the given depth equality into the
bound required by miracle flatness, applies that theorem, and transports
flatness back to the original stalk map.

The new module `Sheaf.AlgebraicGeometry.PolynomialChartLocalAlgebra` isolates
only the geometric/localization comparison. It asserts no depth or
Cohen-Macaulay condition. It provides a regular local source and a local map
to the *actual* fibre stalk already used in the original statement, finite
local dimensions with a common residual contribution, closed-fibre dimension
zero, the quasi-finite dimension bound, and the stalk/fibre flatness comparison.
Its docstring specifies the concrete polynomial localization and transported
map that establish existence. These witnesses are eliminated inside a theorem
proof; no definition chooses arbitrary data from an unproved existence theorem.

The original node's proof, proof_deps and proof_origin now match this reduction.
No target, definition, existing statement, unit, or chapter is changed. No
adaptation of another existing module is needed.

## Proved and sorry left

Holes closed: one, the original syntactic hole in
`AlgebraicGeometry.polynomial_chart_flat_stalk_iff_fibre_depth_and_dimension`
(node `lem-sbc-polynomial-chart-fibre-flat-criterion`). Its proof now contains
no sorry.

Holes added: one,
`AlgebraicGeometry.polynomial_chart_local_algebra`
(node `lem-sbc-polynomial-chart-local-algebra`), with proof exactly `by sorry`.
This is the only sorry in either delivered module. It isolates the original
plan's affine/stalk identifications, geometric dimension comparison, and
closed-fibre flatness transport. It does not contain the depth calculation or
miracle-flatness inference proved in the original module.

This is a substantive decomposition, not an axiom-free proof: one hole closed,
one added, net zero before the ledger's closure calculation. Existing imported
inputs may also rest on sorry, including the faithfully-flat local dimension
theorem; their declarations and nodes are reused unchanged, as stage 3 requires.
The regular local depth helper is proved without adding a hole.

Both modules compile together in import order with lcompile.py, with no compiler
warnings. Verification of coercions includes the distinct natural-number,
extended-natural-number, and WithBot dimension expressions.

## No longer needed

None of the original public imports is removed. No original mathematical
proof dependency is globally pruned by this delivery. The affine fibre,
stalk-localization, open-subspace dimension, polynomial regularity,
finite-residue, field dimension, quasi-finite dimension, standard-smooth
polynomial dimension, and fibrewise flatness inputs move into the plan of the
geometric comparison node; the depth, faithful-flat dimension and miracle
flatness inputs are directly used by the original module. Removing them from
its *direct* proof_deps is a relocation, not pruning. All added proof imports
are used. The previously rejected directional modules remain outside lean/
in scratchpad and are not delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier submission merely restated the equivalence's directions and was
correctly rejected. This delivery replaces it: the parent contains the actual
local algebra argument, including applications of five original planned theorem
modules, a proved regular-depth helper, a proved zero-dimensional-fibre-depth
calculation, and dimension cancellation. The single new geometric assertion has
no depth hypothesis or depth conclusion, so it is strictly a part of the
argument, not the original criterion under another name.

The original module had no imports for the proof dependencies listed by its
node; the needed proof imports were added explicitly. A full direct application
of the planned local algebra results first needs the scheme/affine coordinate
comparison now isolated in the new node. The local dimension d of a polynomial
fibre ring is not generally the number n of variables: at nonclosed points
there is a nonzero residue transcendence-degree contribution t. The bridge
keeps this contribution and uses n=d+t, rather than incorrectly asserting d=n.
The source for the field dimension-at-point formula is Tag 00P1.

Edge-case checks of the new statement: for n=0, n=d+t forces d=t=0 and r<=d
forces r=0; all depth and miracle-flatness calculations still work with the
empty parameter list. At nonclosed points t may be positive, and cancellation
works without assuming x is closed in its fibre. Nonreduced Artinian closed
fibres cause no issue: their dimension and depth are both zero, without requiring
them to be fields. The base T may be non-Noetherian: the fibre coordinate algebra
is finite type over a residue field, so only its localized fibre stalk is
asserted Noetherian. If U is empty, there is no point x to which the statement
applies. No hidden nontriviality assumption is imposed on T.

The unit record sk-prop-normal-form has no realized nodes in its two step lists.
Its statement and steps are untouched, and the polynomial chart/miracle flatness/
fibrewise flatness route is preserved. Blueprint searches for the comparison,
00RE and 00R7 found no matching imported blueprint node. LeanFinder and Loogle
found stalk-localization ingredients but no combined comparison; LeanSearch was
unavailable. Searches are recorded in the new node and searches.jsonl.

## New nodes

`lem-sbc-polynomial-chart-local-algebra`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-polynomial-chart-local-algebra.json`,
records `AlgebraicGeometry.polynomial_chart_local_algebra` in the new module
`lean/Sheaf/AlgebraicGeometry/PolynomialChartLocalAlgebra.lean`. Its complete
statement includes the actual fibre stalk, all finite dimension witnesses,
the local ring structures and map, and the flatness comparison. Its three proof
steps specify the concrete affine/local constructions, the geometric dimension
comparison, and the application of the existing closed-fibre criterion; their
union is its proof_deps. Its source, natural-language proof, three search kinds,
Lean signature, creation record, and inherited chapter/unit are included.
No change record is required because no existing interface changes.


## Second reading by C4

1. I compared both delivered Lean modules with the repository versions. The criterion's
public theorem signature and all original public imports are byte-for-byte unchanged;
the only interface additions are the separately recorded local-algebra theorem and its
module. Verdict: pass.

2. I compiled the two modules together with `lcompile.py --all`; both compile without
errors or warnings. The only remaining `sorry` is the named
`AlgebraicGeometry.polynomial_chart_local_algebra`, recorded by node
`lem-sbc-polynomial-chart-local-algebra`. An axiom probe shows the proved private
helper uses only `propext`, `Classical.choice`, and `Quot.sound`; the two public
criterion declarations transitively use `sorryAx` only through that explicitly split
node. There are no forbidden declarations or hollow definitions. Verdict: pass.

3. I checked the split statement against the local argument and the cited Stacks
proof. It supplies the regular local source, local map, finite dimension witnesses,
zero-dimensional closed fibre, quasi-finite dimension inequality, residue
transcendence contribution, and the exact stalk-flatness equivalence. It has no depth
hypothesis or conclusion, so it is a strict geometric reduction rather than a
restatement of the criterion. Its edge cases include `n = 0`, nonclosed points with
positive residue transcendence degree, and nonreduced zero-dimensional fibres.
Verdict: pass.

4. I checked the proof route and imports. The parent uses the split comparison, the
regular-parameter depth calculation, the flat-local depth formula, faithful-flat
dimension comparison, and miracle flatness. The imports are ordinary proof imports
where appropriate, and no original public import was removed. The unit's statement
and steps remain untouched; its `realized` fields were already empty because this
criterion is below the unit route. Verdict: pass.

5. I checked both DAG nodes. The parent node's `proof`, `proof_deps`, and
`proof_origin` match the Lean reduction, and the new node records its exact Lean
statement, source, proof steps, dependency union, searches, and creation metadata.
The dependency records point to existing declarations or Mathlib matches. Verdict:
pass.

I changed only this report by adding this second-reading section and removed a temporary
axiom-probe file. No Lean proof or node metadata required repair.
