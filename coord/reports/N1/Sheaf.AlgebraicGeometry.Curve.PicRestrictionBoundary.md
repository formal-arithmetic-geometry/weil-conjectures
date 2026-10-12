## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary` with a
complete Lean reduction. The statement and all public imports are unchanged.

Added `Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact`, isolating only step 1 of the
original argument: surjectivity of Picard restriction and its boundary-generated kernel.
The parent proves all of the subsequent degree-zero quotient argument. It constructs the
normalization homomorphism, proves degree zero and invariance under restriction, proves
surjectivity from the degree kernel, computes the image of its kernel using
`MonoidHom.map_closure`, and applies `QuotientGroup.quotientKerEquivOfSurjective`. Compatibility
on representatives is proved by `rfl`; the equivalence is induced by the specified restriction.

Updated `lem-sc-pic-restriction-boundary`'s proof, proof_deps and proof_origin to this route.
The unit `sk-prop-ext-invariance` has empty realized-step lists; its compactification and
boundary route is retained. No definition, existing statement, or target was changed.

## Proved and sorry left

Proved (no direct sorry): `AlgebraicGeometry.Scheme.Hom.pic_restriction_boundary`, node
`lem-sc-pic-restriction-boundary` (1 of 1 original sorries reduced).

One newly split-off sorry remains:
`AlgebraicGeometry.Scheme.Hom.pic_restriction_exact`, node `lem-sc-pic-restriction-exact`, in
`Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact`. It asserts only the geometric exactness
step, with no degree-zero subgroup, normalization, boundary differences, quotient equivalence,
or representative compatibility. Its entire proof is `:= by sorry`, with the source and
complete divisor-class proof in its docstring and node. The parent's proof therefore still
rests transitively on sorry. No other sorry was added.

Edge checks: empty boundary requires no chosen point and makes the third clause vacuous.
For a singleton boundary the difference subgroup is trivial. The normalization still works
for any number of boundary points and for all integer degrees, including negative degrees.
For the affine line compactified by the projective line, Pic⁰ and the affine Picard group are
both trivial, in agreement with the statement. The exactness lemma also allows empty boundary.

## No longer needed

Removed these proof-only imports from the parent:

- `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition`: node
  `lem-sc-pic-proper-decomposition` is not used. The parent constructs the required
  normalization by the specified boundary point directly, using the existing degree-one
  formula. No abstract proper Picard decomposition is needed for this proof.
- `Sheaf.AlgebraicGeometry.DivisorClassCurve`: this comparison is not used directly in the
  parent. Node `lem-sc-divisor-class-curve` remains a planned dependency of the new geometric
  exactness node, so its mathematical necessity is not pruned.
- `WeilConjectures.AlgebraicGeometry.Curve`: its direct import is redundant; its degree-zero
  definition remains available through the public statement imports. Node `def-sc-pic0` is
  still used and is retained in proof_deps. The module is not globally pruned.

Added just the proof-only import `Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact`.
The public imports of Compactification, Picard and QuotientGroup.Basic all remain required.
No other old dependency node is removed.

## Where the brief, the DAG or earlier work was wrong

The original step 1 labels the whole geometric restriction argument elementary and suggests
that the divisor-class comparison supplies it. That declaration supplies isomorphisms and
representative modules for each curve separately. It does not state their compatibility with
restriction, nor a restriction homomorphism on divisors and its principal-divisor kernel.
Existing Curve.Affine only explains this argument in its docstring and states an abstract
Jacobian quotient; it does not give the required exactness for the specified compactification.
The new node records this missing geometric step explicitly.

The original abstract proper Picard decomposition is unnecessary: the chosen boundary point
already supplies the splitting needed here via `picDegreeHom_ofClosedPoint`.

Searches used LeanFinder, Loogle, Mathlib grep and local rg on both Lean roots. No existing
scheme Picard restriction exactness declaration was found. LeanSearch returned Internal Server
Error; this is recorded as unavailable rather than as a mathematical no-match result.
The blueprint file is not present in this read-only clone; the proof and source place are
those preserved in the item's DAG node and existing declaration docstring.

## New nodes

`lem-sc-pic-restriction-exact` (`dag/nodes/sec-curve-estimates/lem-sc-pic-restriction-exact.json`)
is the geometric first step of the original source argument. It has the unchanged ambient
curve and compactification hypotheses and states surjectivity and the boundary kernel only.
Its new module is `lean/Sheaf/AlgebraicGeometry/Curve/PicRestrictionExact.lean`. Its planned
proof retains the existing divisor-class comparison. There are no change records because no
existing definition, signature, or public import changed.

## Second reading by N1

1. Compared both delivered modules with the repository versions. Existing declaration signatures and public imports are unchanged; the parent proof-only import changes are recorded in the report, and the new exactness declaration has its own node.
2. Compiled both modules locally with `lcompile.py --all`; compilation succeeds. The parent has no `sorry`; the only remaining `sorry` is the named `pic_restriction_exact` theorem, with its source, proof plan, and DAG node. No forbidden declarations or hollow definitions were added.
3. Checked the split statement against the parent use and edge cases. `pic_restriction_exact` is the strict geometric restriction and boundary-kernel step, omitting the degree-zero quotient construction; it is true and exactly sufficient for the reduction. Searches found no existing equivalent declaration.
4. Reviewed the proof route and pruning. The parent uses the explicit degree splitting and quotient first-isomorphism route, while retaining the unit's compactification and boundary restriction route through the exactness node. Removed imports and dependency changes are listed above; no further unused dependency was found.
5. Compared DAG proof steps, dependencies, origins, and the new node with the Lean proof. They agree, and the unit metadata remains unchanged.

Changed nothing during this second reading.
