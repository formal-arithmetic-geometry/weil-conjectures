## What changed

Proved the original conjunction in `Sheaf.Paper.IntegralSupportReductionNormalization`
without changing its statement or any existing public import. The invertibility part
uses the proved constructible-reduction, open-support and proper-support bounds,
and the actual normalized reconstruction counit.

For refinement, construct the integral morphism obtained by transporting the explicit
system comparison through the two supportValue isomorphisms. Counit naturality gives
the required square with this morphism. A categorical finite-square calculation and
the coefficient datum's inverted compactification square compute all its reductions.
The existing Milnor joint-faithfulness theorem on integral constructible objects then
identifies it with the inverse datum comparison. This does not assume faithfulness of
finite evaluation on arbitrary derived coefficient systems.

Added finite-coordinate modules for the single support adjunct and the single finite
evaluation of a directed refinement. Their statements separate the projection
normalization for one compactification from the finite proper/open mate computation.
The scalar projection calculation uses a local reduction alias and proved categorical
transport lemmas to keep the coefficient presentations aligned. Proved private hom-map
formulas expose supportValue and the finite-reduction isomorphism without unfolding
their derived-category presentations during whole-goal rewriting. All transparency
attributes are local; no shared definition or attribute changes.
The item's additional imports are private proof imports. Only the item, these new modules,
and their DAG records are changed. The blueprint unit route is preserved.

## Proved and sorry left

The original hole in
`WeilConjectures.FixProjectionCompactification.integralSupportReductionNormalization`
is closed by a complete assembly proof. Its invertibility assertion is proved from
existing stated dependencies. The refinement assertion is decomposed into genuinely
finite coefficient identities, together with proved integral joint faithfulness.

The single-support identity
`WeilConjectures.FixProjectionCompactification.integralSupportAdjunctFiniteCoordinates`
is proved from whole-support-tower normalization and scalar-adjunction naturality.

One new hole remains:
`WeilConjectures.FixProjectionCompactification.systemRefinementFiniteCoordinates`,
node `lem-sf-system-refinement-finite-coordinates`. It computes one finite evaluation
of the explicit proper/open refinement map on a finite constructible input. It has
no integral operation datum, reconstruction map, normalization assumption on the
whole input system, invertibility assertion for supportReduction, or system-map
equality conclusion. Thus this is a strictly smaller geometric calculation, not
the original obligation renamed. Its docstring and node give the origin-witness,
finite gamma, compositor and finiteRefinementNormalization argument.

Validation: remote `lcompile.py --all` compiled all three modules successfully.
No diagnostic profiler or trace options remain. The original theorem signature
is unchanged, and all three DAG Lean signatures match their files.

Original holes closed: 1. New holes added: 1. This is a decomposition, not a claimed
net reduction of the target-closure hole count. No hole remains in the item itself.

## No longer needed

No existing module is withdrawn and no public import is removed. Globally pruned
modules: none.

The original node's direct proof dependencies on
`lem-sf-open-tensor-normalization`, `lem-sf-integral-direct-image-constructible`,
`lem-pur-integral-operations-preserve-constructible`, and
`lem-sf-proetale-constructible-origin` are replaced by the already stated and proved
`lem-sf-constructible-reduction-good`, `lem-sf-open-support-step-bounds`
and `lem-sf-proper-support-step-bounds`. The larger unfinished refinement-diagram
admissibility theorem is not used.
The original direct dependency on `lem-coef-integral-residue-tor` is also
unnecessary in the assembly;
its use inside the existing supportValue construction is preserved.
These underlying results can still be needed transitively; no global withdrawal
of them is claimed.

The direct invocation of
`lem-sf-integral-compactification-system-realization` is unnecessary: the supplied
realization record is used, and the finite formulas plus Milnor injection perform
the assembly. The two-input theorem `lem-sf-refinement-projection-counit` is not
applied. Its module and the item's statement dependency remain because that module
defines the directed systemComparison occurring in the unchanged statement.

## Where the brief, the DAG or earlier work was wrong

No existing statement was found false and no shared interface was repaired. The old
plan described the normalization of the refinement map without giving a declaration
for its single finite-level formula. That formula is now an explicit smaller item.
The existing varying-ring theta_evaluation has a different system domain and absolute
separatedness hypotheses; those are not assumptions of this item. Its signature
does not supply the finite formula for the present canonical bridges directly.
The whole-support-tower normalization already states the projection formula needed
for the single support adjunct; it need not be split off as another unproved lemma.

The alternative route through joint faithfulness is valid on the integral
constructible domain: the imported theorem proves it using finite shifted Hom
groups and the Milnor injection. It makes no claim that evaluations are faithful
on general derived coefficient systems, and requires no absolute separatedness
of X or Y over the base field.

## New nodes

`lem-sf-integral-support-adjunct-finite-coordinates` records the proved one-input,
one-compactification projection calculation. It uses the proved individual
reduction/open/proper domain bounds and the existing whole-support-tower normalization, then cancels
the explicit datum value transports under the finite scalar adjunction.

`lem-sf-system-refinement-finite-coordinates` records the remaining finite geometric
calculation, at one quotient and an arbitrary system whose chosen evaluation is
identified with a finite constructible input. It retains the actual directed
systemComparison, supportEvaluation and the normalized finite datum comparisons.

No change record is needed: no existing statement, definition or other module is
changed.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
