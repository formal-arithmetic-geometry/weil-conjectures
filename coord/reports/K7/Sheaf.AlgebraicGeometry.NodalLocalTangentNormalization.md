## What changed

Replaced the single sorry in `AlgebraicGeometry.NodalLocal.tangent_normalization`
with a complete Lean assembly of the ring comparison, scheme normalization fibre,
and geometric branch square. The original theorem's elaborated statement is unchanged.
The canonical grading and degree-zero residue isomorphism are constructed directly.
The normalized chart formula now proves uniqueness and compatibility with the residue
structural map, rather than asking a remaining lemma for those conclusions.

Moved the existing definitions, instances and Comparison structure to the new module
`Sheaf.AlgebraicGeometry.NodalLocalTangentData`, publicly imported by the original item.
This avoids a cycle between the new proof lemmas and the statement data. Existing names
and signatures are preserved. `Comparison.IsNatural` factors through the definitionally
equal ring-level `IsNaturalIso`. The change record is
`coord/changes/nodal-local-tangent-proof-interfaces.md`.

Seven sandbox modules compile together cleanly through lcompile.py, rechecked at
2026-10-23 12:47 UTC. The complete proof
uses the existing separable quadratic completion theorem, so its reducedness, dimension,
Noetherianity and finite-type hypotheses are genuinely obtained from the original nodal
hypothesis. The geometric square is transported by IsPullback.of_iso; both projection
equations are proved. No source-library file is changed.

## Proved and sorry left

The item's one original hole, `AlgebraicGeometry.NodalLocal.tangent_normalization`, is
closed by a complete assembly proof. This is a decomposition, not a sorry-free proof:
three genuinely separate remaining results are added, for a net hole change of -2.

New fully proved declarations, all under `AlgebraicGeometry.NodalLocal`:

- `pieceEquiv`, `pieceEquiv_coe`, `tangent_internal`, `canonicalGrading`, `zeroHom`,
  `residueToZero`, `tangentZeroIso`, `tangentZeroIso_apply` construct the grading and
  residue isomorphism without mathematical holes.
- `exists_normalization_division`, `normalized_chart_equiv_unique`,
  `normalized_iso_unique`, `normalized_iso_over_residue` prove the division-existence,
  chart uniqueness, scheme-isomorphism uniqueness and structural residue-square clauses.

Every sorry left in this delivery is exactly the body of one public theorem:

- `AlgebraicGeometry.NodalLocal.quadratic_tangent_comparison`, in
  `Sheaf.AlgebraicGeometry.NodalLocalAlgebraComparison`, node
  `lem-sfb-nodal-quadratic-tangent-comparison`.
- `AlgebraicGeometry.NodalLocal.reduced_normalization_local_fibre`, in
  `Sheaf.AlgebraicGeometry.ReducedNormalizationLocalFiber`, node
  `lem-sfb-reduced-normalization-local-fibre`.
- `AlgebraicGeometry.NodalLocal.geometric_branch_square`, in
  `Sheaf.AlgebraicGeometry.NodalGeometricBranchSquare`, node
  `lem-sfb-nodal-geometric-branch-square`.

These results assert respectively only the ring-theoretic comparison, only the generic
scheme-normalization fibre square, and only geometric scalar extension of normalization
residues. None contains the whole original conclusion. No sorry occurs in a definition,
instance, private helper or unfinished proof. Their source and full proof in words are
in their docstrings and matching nodes.

Edge cases checked in the mathematics: split nodes, nonsplit real quadratic nodes,
characteristic two (including F₂), non-rational separable closed points, arbitrary
coefficient-field automorphisms in the ring presentation, non-reduced or non-quasi-compact
ambient schemes in the local-fibre lemma, and empty schemes (there is no point to supply).
Regular denominators require unit leading coefficient in the split residue algebra;
merely nonzero does not suffice. None of the statements makes that invalid inference.

## No longer needed

No existing mathematical node or module is withdrawn or claimed globally pruned.
The newly reviewed completed-model, completed-denominator, homogeneous-fraction and
quadratic-branch nodes remain the proof dependencies of the local algebra result;
the completed-denominator theorem now has a Lean declaration, while the other three
still have no Lean records in the current shared checkout. Their mathematics is
retained, rather than replaced by an alternate route.

All original public imports are retained transitively through the data module.
The following old direct private imports are removed from the item (they supply no
part of its new assembly proof):

- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`
- `Sheaf.TraceFormula.CurveNormalizationCompletion`
- `Mathlib.RingTheory.AdicCompletion.LocalRing`
- `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`
- `Sheaf.RingTheory.SeparableClosedPointFormalPresentation`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.RingTheory.Localization.Integral`
- `Mathlib.RingTheory.AdicCompletion.Completeness`
- `WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions`
- `Mathlib.AlgebraicGeometry.Noetherian`

The remaining theorem modules have no speculative private proof imports. Their planned
mathematical dependencies are recorded in their nodes. The item privately imports only
the existing separable completion theorem and the four actual proof modules it applies.

## Where the brief, the DAG or earlier work was wrong

The shared DAG changed during this session: the earlier ten-step parent proof was
replaced by a reviewed five-step assembly and four statement-only child nodes. Three of those four
children and the cited normalization-affine-stalk node currently have no Lean records,
so their declarations cannot be imported. This delivery retains their mathematical
route and records the precise remaining Lean interfaces instead. In particular the
local algebra node cites the four current child nodes; it does not report them pruned.

No false original statement was found. The generic componentwise normalization fibre
argument must handle the ambient scheme's possible nilpotents and infinitely many
global components; the retained local-fibre proof does so on a Noetherian affine
neighbourhood, using only the finitely many components meeting it. No global reducedness
or quasi-compactness hypothesis is added.

The existing parent has generic-tool approvals. The new geometric branch node uses
`lem-trf-curve-normalization-completion` and
`lem-trf-separable-closed-point-formal-presentation` only as the same generic local
algebra tools; please carry the corresponding approvals to that node at independent
review. No worker-written approval is inserted.

## New nodes

`def-sfb-nodal-tangent-comparison-data` attaches the relocated existing mathematical data
and its definitionally equal ring-level naturality predicate to the data module.

`lem-sfb-nodal-tangent-canonical-grading` records the proved internal grading and
representative-preserving degree-zero residue isomorphism.

`lem-sfb-nodal-normalized-chart-uniqueness` records the proved homogeneous-chart
uniqueness and residue compatibility argument, with its division-existence helper.

`lem-sfb-nodal-quadratic-tangent-comparison` isolates the ring-theoretic part of Stacks
0CBT. It retains the current DAG's completed-model, denominator, fraction and coefficient
chart nodes. It excludes scheme normalization and geometric completed branch data.

`lem-sfb-reduced-normalization-local-fibre` isolates the generic local componentwise
normalization square (Stacks 035P, 0CDV and 0307), without a nodal assumption.

`lem-sfb-nodal-geometric-branch-square` isolates the scalar-extension square for the
actual normalization residue algebra and geometric completed branches, without Proj.

All new nodes inherit the parent's chapter and unit, carry all three kinds of Mathlib
search, and have verbatim Lean signatures and source proofs. Change record:
`coord/changes/nodal-local-tangent-proof-interfaces.md`.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
