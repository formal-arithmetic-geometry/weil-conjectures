## What changed

Filled `AlgebraicGeometry.Etale.affineSpaceAdjunction_baseChange` in
`WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange`.
Its adjunction clause applies the existing source-library
`nonempty_rightDerivedLowerShriek_adjunction_affineSpace`.
Its compatibility clause is assembled by two proved private helpers:
`affineLineBaseChangeModel` restricts the projective-line case to the standard affine chart;
`affineSpaceBaseChangeModel` iterates the affine line using the sum/reindex isomorphism.
The induction works over arbitrary bases, so no additional quasi-separatedness assumption
or affine-open descent lemma is needed.

The only new proof import is `Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange`.
That module states the remaining geometric projective-line case, with its source and
complete proof plan. All existing source signatures, attributes, public imports,
non-theorem bodies and already proved public theorems are unchanged.

The parent `prop-asd-smooth-base-change` retains its canonical-map and tensor proof;
its isomorphism step now records the adopted affine-space reduction explicitly.
Two new node records distinguish this ordinary-etale source realization from the
broader classical-pro-etale unit statement.

Validation: both delivered Lean files compile together through `lcompile.py --all`.
The private induction is checked by Lean in dimension zero and the successor case.
The new statement also covers the zero coefficient ring, empty schemes, identity
base changes and non-flat base changes: neither the statement nor its diagonal/trace
proof plan requires nonemptiness, a nonzero coefficient ring or flatness.

## Proved and sorry left

Original item: 1 hole. Closed:
`AlgebraicGeometry.Etale.affineSpaceAdjunction_baseChange`
(node `lem-asd-upstream-affine-space-base-change`).
There are zero direct holes left in the assigned module.
The private helpers `affineLineBaseChangeModel` and `affineSpaceBaseChangeModel`
are fully proved.

Added exactly 1 hole:
`AlgebraicGeometry.Etale.projectiveLineExceptionalBaseChange`
(node `lem-asd-projective-line-exceptional-base-change`, module
`Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange`).
It is the single projective-line model step, without the affine restriction,
all-dimensional induction, or the independent adjunction clause of the original theorem.
Thus this is a decomposition: 1 original hole closed, 1 lower hole added, net 0.
No claim is made that the original theorem is free of transitive sorries.
In particular, its existing affine-space adjunction dependency remains unproved.

## No longer needed

No original imports were removed; no source declarations or modules were withdrawn.
No globally pruned module is claimed.

The proof does not add `Sheaf.SixFunctors.ExceptionalBaseChangeAffineLocality` or
`Sheaf.SixFunctors.ExceptionalBaseChangeOpenRestriction`: the direct affine tower
avoids that separate descent argument. The conditional affine-space theorem in
`BaseChangeCharts` assumes an affine base; the private induction proves exactly the
arbitrary-base variant needed here. All existing public imports stay verbatim.

For this ordinary-etale source realization the classical-comparison inputs of
`sk-lem-geo-affine-local` are not used: `lem-sfb-finite-classical-unbounded-comparison`,
`lem-sfb-unbounded-site-comparison`, `lem-sfb-unbounded-direct-image-comparison`,
`lem-weil-pbc-comparison-pullback`, `lem-cbc-proetale-extension-zero-comparison`,
`sk-thm-pe-direct-image-comparison`, and `lem-weil-extension-by-zero-exact`.
The geometric Noetherian/finite-type checks and Nagata existence inputs of that
broader unit proof are unnecessary here: the standard relative projective
compactification is already available for each affine-space projection.
The unit's clause (2), its quasifinite/sum-extension comparisons, and its further
etale-localization coherence remain with their existing declarations and nodes;
this delivery does not remove any of them.

The projective-line calculation remains the required geometric model. Its
Noetherian-base `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` interface is
not imported, since it does not apply to the arbitrary schemes in this source
signature. Its geometric diagonal/trace argument is recorded in the new node.

## Where the brief, the DAG or earlier work was wrong

No DAG node has `lean.module` equal to the assigned module in this snapshot,
although the source docstrings cite `sk-lem-geo-affine-local` and
`prop-asd-smooth-base-change`. The former has no Lean attachment and states a
classical-pro-etale result over the standing field; the latter is attached to
`Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange` and its current proof calls
this source-library theorem. The new proved realization node records the exact
ordinary-etale source conjunction without replacing either existing statement.

The declared projective-line and affine-space Sheaf interfaces impose Noetherian
hypotheses that this adopted source theorem does not have. They cannot be applied
by inferring that an arbitrary affine scheme is Noetherian. The projective-line
split explicitly keeps the general-base gap visible, and its proof plan uses the
geometric-stalk projective-bundle calculation over arbitrary schemes.

## New nodes

`lem-asd-projective-line-exceptional-base-change` records
`AlgebraicGeometry.Etale.projectiveLineExceptionalBaseChange`, the remaining
projective-line model. Its proof plan is the Kummer splitting, trace/diagonal
adjunction and counit-mate calculation, with the general-base requirement explicit.

`lem-asd-upstream-affine-space-base-change` records the now completely assembled
source theorem `AlgebraicGeometry.Etale.affineSpaceAdjunction_baseChange`.
The first clause uses its pre-existing adjunction declaration; the second restricts
the projective-line model to the affine chart and inducts on the dimension.
No definitions or interfaces were changed, so no change record is needed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
