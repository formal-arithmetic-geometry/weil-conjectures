## What changed

Replaced the hole in `WeilConjectures.integralScalarPullbackConeProZero` by a
complete reduction to an ordinary diagonal factorization and a proved explicit
mapping-cone homotopy. The item's signature and original public imports are
unchanged. Two private proof imports supply the new modules.

`Sheaf.Algebra.Homology.DiagonalConeTransitionHomotopy` proves the general
statement for a complex in a functor category. Its homotopy is the second cone
projection, followed by the diagonal chain map, followed by the first cone
inclusion one degree lower. The cone differential, the two triangle identities,
and the chain-map identity give exactly the original cone transition. The proof
uses the actual cone in the category of strict diagrams and then evaluates;
there is no replacement cone, unspecified isomorphism, or passage to a derived
category.

`Sheaf.Paper.IntegralScalarPullbackTransitionFactorization` isolates the remaining
ordinary coefficient construction: a sufficiently late map from the target
reduction to the earlier source reduction, factoring both strict transitions.
It contains no cone or homotopy. It holds for arbitrary complexes, so the item's
K-flatness and termwise flatness hypotheses are retained but not needed for the
combining proof. Its docstring gives the ramification, quotient, generator and
chain-map argument, including the unramified and zero cases.

The shared checkout restored the quarantined dependency chain during this
session. This delivery preserves those declarations and does not claim that
shared restoration as its own change.

## Proved and sorry left

Original hole closed by decomposition:
`WeilConjectures.integralScalarPullbackConeProZero`
(`lem-pur-integral-scalar-pullback-cone-pro-zero`).

Proved without any new hole or project proof assumption:
`HomologicalComplex.diagonalConeTransitionHomotopy`
(`lem-pur-diagonal-cone-transition-homotopy`).

One new hole, the only sorry in the delivered files:
`WeilConjectures.integralScalarPullbackTransitionFactorization`
(`lem-pur-integral-scalar-pullback-transition-factorization`).

This is a decomposition: one original hole is closed and one strictly smaller
geometric construction is left. There is no net hole reduction. The remaining
statement constructs a chain map with two quotient identities; all cone signs,
the nullhomotopy and its compatibility with strict tower evaluation are proved.

## No longer needed

None of the original public imports is removed and no module is withdrawn.
The original arithmetic DVR and completed constant-sheaf reduction dependencies
remain needed by the lower factorization node; they are not globally pruned.
The cone homotopy needs no products, Roos construction, derived category, inverse
limit or good-complex hypothesis. The principal Koszul module remains imported
because the item's unchanged statement uses its degreewise rearrangement.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is changed or disputed. The original DAG treated the
coefficient diagonal construction and the explicit cone calculation together.
The delivery formally separates them and closes the cone calculation in Lean.
This avoids returning the same cone-vanishing obligation under a new name.
The temporary missing-import issue disappeared when the shared checkout restored
the quarantined prerequisites; no deletion, interface repair, or workaround is
part of this delivery.

## New nodes

`lem-pur-diagonal-cone-transition-homotopy` is a fully proved general lemma for
an arbitrary indexing category and abelian coefficient category. Its explicit
homotopy works for unbounded complexes and arbitrary diagram morphisms.

`lem-pur-integral-scalar-pullback-transition-factorization` is the remaining
ordinary finite-filtration construction. It preserves the original normalized
section equation and states only the diagonal and its two triangle identities.
The chosen late index and the map come from ramification and quotient maps;
there is no selected object or arbitrary existence witness inside a definition.
No change record is needed: every existing signature, definition, attribute and
public import remains unchanged.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
