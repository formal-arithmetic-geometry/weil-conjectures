## What changed

`Sheaf.Paper.FieldShriekCompositionCoefficientSquare` now proves
`WeilConjectures.sfCompositionOnCoefficientStage_comm` from the two-field integral square
in the new module `Sheaf.Paper.IntegralCompositionCoefficientSquare`. The assigned
statement, its binders and its public imports are unchanged. The added proof import is
private. All added helpers are private and proved.

The proof specializes the rational scalar functor's pure-tensor specification to
coefficient one, proves the corresponding formula for the compact-support functor,
and transports the three beta components and two compositor components using their
actual normalization hypotheses. It localizes the integral square, expands the
composite stage beta, and combines the heterogeneous component equalities. It never
uses faithfulness of finite evaluation functors.

The remaining integral statement has two finite coefficient fields and one input.
It has no algebraic closure, coefficient-stage system, rational compositor, or raw
localization hypothesis. It is the integral portion of the original node's proof,
not the stage-system statement renamed. Its source and complete proof plan are in its
docstring and its new DAG node. The original node now records the implemented route.

Validation: the assigned module compiled on the server without warnings in 44.1 seconds.
The new integral statement also compiled in the sandbox import-order check.
The assigned theorem signature is byte-for-byte unchanged.

## Proved and sorry left

Closed the original hole in `WeilConjectures.sfCompositionOnCoefficientStage_comm`
(node `lem-zl-field-shriek-composition-coefficient-square`); no sorry remains in the
assigned module.

Added one hole: `WeilConjectures.sfIntegralComposition_coefficient_comm`
(node `lem-zl-integral-composition-coefficient-square`), in its own new module.
This delivery is a decomposition: one original hole closed, one strictly integral
hole added, net zero holes closed. No definitions contain sorry.

Edge cases checked against the constructions: identity coefficient embeddings use
the same coefficient-one formula; zero arrows and objects are preserved by the actual
functors; no inhabitedness or separatedness of the structure morphisms is added.

## No longer needed

No existing Lean imports, declarations or modules are removed or withdrawn.
`prop-weil-pbc-rational-transport` / `Sheaf.Paper.PbcRationalTransport` is unnecessary
for this proof: ordinary `Functor.map_comp` localizes the established arrow equality,
and the existing explicit scalar functor specifications fix its maps. No replacement
existence or uniqueness theorem for rational functors is needed.

The other original proof dependencies move to the new integral node, where they
remain needed: compatible compactification towers, operation-reduction scalar mates,
scalar associativity, projection-normalized qcqs realization, integral coefficient
comparisons and compactification-refinement coherence. They are not globally pruned.
The declared constant-coefficient tower square
`PurStrictScalar.scalar_compactification_composition` is also recorded for the new
integral node; the remaining work is its transport to the normalized completed
functors and beta maps. The existing constructible mapping-limit theorem
`integralConstructibleReductionHom` supplies the separated-case reconstruction
argument; the new node explains the finite-affine-cover extension needed here,
since the structure morphisms need not be separated. The original module needs only the new integral theorem and the rationalization,
finite-action and stage-system definitions for the remaining transport proof.

## Where the brief, the DAG or earlier work was wrong

The existing dependency declarations do not directly state the integral compositor
square with the supplied `SfIntegralCompositionSpec` and
`SfCompactSupportIntegralBetaSpec` hypotheses. The new theorem isolates this integral
step. In particular scalar coefficient associativity alone is not the geometric
compact-support composition square. The unit route and all existing statements stay
unchanged.

## New nodes

`lem-zl-integral-composition-coefficient-square` states the actual integral scalar
square for two normalized compositors and the three normalized beta maps. It retains
the geometric and normalized strict-tower dependencies of the original proof, with
Stacks 0F7J and the operation-reduction coefficient paragraph as its sources. Its Lean
attachment is `WeilConjectures.sfIntegralComposition_coefficient_comm` in
`Sheaf.Paper.IntegralCompositionCoefficientSquare`. No change record is needed:
no existing definition, signature or public import changes.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
