## What changed

Completed `AlgebraicGeometry.unitBinomial_finite_surjective_etale` in
`Sheaf.AlgebraicGeometry.UnitBinomialFiniteEtale` without changing its statement,
public imports, definitions, or attributes. The basis uses `AdjoinRoot.powerBasis'`
reindexed by `natDegree_X_pow_sub_C`; for the zero ring it uses Mathlib's unique
basis with the specified `Fin n` index set. Finiteness, surjectivity, and etaleness
follow from the proved monic-quotient, faithful-flatness, and Kummer algebra APIs,
translated to spectrum morphisms.

Added private proof imports of `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, and
`WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale`. Updated only this item's
DAG proof, proof dependencies, and proof origin. No shared interface changes or
consumer adaptations are required.

The source paragraph in Stacks `etale-cohomology.tex`, Tag 03PL,
`lemma-kummer-sequence`, was read. Edge cases: the zero ring retains all n basis
indices; the degree argument uses bottom rather than zero in that case; n=1
works in each API; n=0 is excluded. All hypotheses, including invertibility of n
and of u, remain exactly as stated.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.unitBinomial_finite_surjective_etale`
(node `lem-sfb-unit-binomial-finite-etale`). Added 0 holes. No sorry remains in
any delivered module, and no decomposition or new theorem is introduced.

The final proof compiled cleanly with `lcompile.py` in 3.6 seconds, without
warnings. The delivery also runs its compile and axiom probes.

## No longer needed

Removed the four redundant private imports:
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`,
`Mathlib.RingTheory.RingHom.FaithfullyFlat`, and
`Mathlib.RingTheory.Etale.StandardEtale`. The added proof imports provide the APIs
actually used and their required transitive imports. Public imports stay verbatim.

This proof does not use
`lem-sfb-monic-quotient-faithful-tensor-coordinates`
(module `Sheaf.RingTheory.MonicQuotientFaithfulTensorCoordinates`) or
`lem-sfb-unit-binomial-derivative-presentation`
(module `Sheaf.RingTheory.UnitBinomialDerivativePresentation`): the proved source
helpers already supply faithful flatness and binomial etaleness. It also does not
need `lem-weil-pbc-standard-etale-monic-derivative` as a direct proof dependency:
the source helper uses its own already proved standard-etale pair with g=1.
These three dependencies are removed from this item's DAG proof. The modules
and nodes themselves are preserved; this delivery makes no claim that other
parents do not need them. The unit record realizes no statement or step at this
node, and no unit or chapter route is bypassed.

## Where the brief, the DAG or earlier work was wrong

There is no statement error. The planned tensor-coordinate and explicit
two-variable inverse-derivative constructions are unnecessary for this theorem:
existing source-library proofs suffice. The source helper
`AdjoinRoot.etale_X_pow_sub_C` was already recorded as closed in the audit of
`lem-sc-kummer-exact`.

Fresh LeanFinder and Loogle searches found the generic Mathlib standard-etale
interfaces, rather than this entire statement. The prescribed grep search and
local source searches found `AdjoinRoot.etale_X_pow_sub_C`,
`AdjoinRoot.faithfullyFlat_of_monic`, and their existing use in the source
Kummer-cover construction. Their signatures and proofs were read before use.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
