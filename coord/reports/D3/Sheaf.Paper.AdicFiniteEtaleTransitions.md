## What changed

Filled the proof of `AlgebraicGeometry.Scheme.adicFiniteEtale_transitions`, preserving
its signature and public imports. The proof lifts the conjugated quotient isomorphism
and its inverse by Hom-set bijectivity. Injectivity proves the inverse laws. It then
proves the quotient cocycle by applying comparison, cancelling `alpha n`, substituting
the compatibility equations, and using comparison/scalar naturality and normalization.
The double extension is bounded by its isomorphism to a single extension, so the final
faithfulness application has its domain hypothesis checked.

The shorter route uses the existing
`AlgebraicGeometry.ProEtale.coefficientComparison_boundedClassical` on bounded objects;
constructibility of scalar extensions is unnecessary. Added and proved
`AlgebraicGeometry.Scheme.adicScalarExtension_bound` in `AdicScalarExtensionBound`:
the existing coefficient-model flat-model criterion supplies a flat representative
supported in the exact Tor interval, which is K-flat. Additive scalar extension
preserves its zero terms. The universal computation and cohomology transport give
the asserted bound for every coefficient ring map.

Three strictly smaller interface obligations are stated in separate new modules:
`AdicExactComparison`, `AdicReductionCocycle`, and `AdicComparisonComposition`.
They concern the already fixed functors and normalizations, without any chosen etale
origins or markings. Each has a source, proof in words, and DAG node. No data is
chosen from these new existence statements to define a public object.

The main theorem compiles in 5.6 seconds; the proved scalar bound compiled in
9.5 seconds, and the three statement modules each compiled in under 9 seconds.
All verification uses `lcompile.py`. The final delivery runs the mandatory checks.
No shared definitions, other existing modules, target signatures, or source-library
interfaces were changed. There are no forced adaptations or change records.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.adicFiniteEtale_transitions`
(node `lem-sfb-adic-finite-etale-transitions`): 1 of 1 item holes.
The proof combining the remaining obligations is complete Lean.

Also proved, with no hole, the new theorem
`AlgebraicGeometry.Scheme.adicScalarExtension_bound`
(node `lem-sfb-adic-scalar-extension-bound`). Both private helpers,
`liftIsoOnProperty` and `adicBounded_of_iso`, are proved.

Exactly three new holes remain, each with body exactly `by sorry`:

- `AlgebraicGeometry.Scheme.adicExactComparison`,
  node `lem-sfb-adic-exact-comparison`.
- `AlgebraicGeometry.Scheme.adicReduction_cocycle`,
  node `lem-sfb-adic-reduction-cocycle`.
- `AlgebraicGeometry.Scheme.adicComparison_composition`,
  node `lem-sfb-adic-comparison-composition`.

This is a decomposition, not a complete axiom-free proof of the original obligation:
1 existing hole closed, 3 holes added, net 2 additional holes in this packet.
The scalar-bound substep is proved without adding a hole.

## No longer needed

No preexisting Lean import was removed: the item previously imported only its public
data module. All five new proof imports are used. The original direct proof dependency
on `lem-sfb-adic-finite-stratification-pullback`
(`Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback`) is unnecessary: bounded
full faithfulness avoids constructibility and simultaneous stratification entirely.
For the same reason this argument does not need
`lem-weil-pbc-locally-constant-tensor` (`Sheaf.Paper.LocallyConstantTensor`) or the
constructibility part of `def-pe-etale-constructible-module` (its bounded predicate
remains in the unchanged statement).

The parent's old direct proof dependencies on the following nodes were also replaced
by the stated narrower supporting results and bounded classical comparison:

- `lem-pc-kflat-resolution`;
- `lem-pur-derived-change-of-rings`;
- `lem-pur-kflat-change-of-rings`;
- `lem-pur-resolving-class-derived-adjunction`;
- `prop-weil-pbc-inverse-image-modules-exact`;
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`;
- `sk-thm-pe-classical-sheaves`;
- `sk-thm-pe-constructible-comparison`;
- `lem-weil-pbc-ringed-topos-kflat-pullback`;
- `lem-weil-pbc-independent-sheaf-tensor-colimits`.

This list describes direct parent dependencies, not a claim that all those modules
leave the targets' import closure: some remain behind the existing data and comparison
results, and K-flat resolution and preservation are dependencies of the normalization
substeps. No module or declaration is withdrawn. The parent retains
`lem-sfb-adic-finite-reduction-data` and its complete unit route.

## Where the brief, the DAG or earlier work was wrong

The prior plan required proving scalar-extension constructibility in order to use
comparison. The already proved bounded classical Hom-set bijection has no
constructibility hypothesis. Keeping the supplied boundedness, and proving the exact
scalar bound through the existing flat-model criterion, avoids that entire detour.

The existing full-faithfulness theorem applies to a derived functor with a specified
factorization through canonical exact module comparison. `adicFinitePullback` is
instead supplied by a K-flat universal pair for the algebraic lift. No existing
statement identifies those exact presentations, so `adicExactComparison` isolates
that necessary identification rather than silently identifying the functors.

Likewise the data module specifies reassociations and scalar/pullback comparison by
unique K-flat normalization, but does not expose their cocycle and composition
identities. The two new normalization statements supply precisely the equations used
by the parent; neither asserts any existence or coherence for etale origins.

Edge cases: the scalar bound uses an arbitrary ring map, including the identity and
maps to the zero ring, and any small site, including an empty site. The comparison
identification imposes no bounds or Noetherianity. Both normalization equations allow
equal indices/identity maps. The main proof contains no strict inequality between
indices and does not normalize `alpha 0`; all markings remain arbitrary.

The current unit text and Stacks `proetale.tex` compare-constructible-derived (09AL),
describe-constructible-complexes (09C2), and `sites-cohomology.tex` tensor arguments
were read. Blueprint searches for scalar extension and 09AL and library searches
found no existing declarations with the three missing normalized statements.
No mathematical falsehood or target-statement discrepancy was found.

## New nodes

`lem-sfb-adic-scalar-extension-bound`: proved cohomological support after arbitrary
scalar extension of a finite-Tor object. It uses the existing flat-model criterion,
bounded-above flat K-flat theorem, and universal scalar computation.

`lem-sfb-adic-exact-comparison`: identification of the normalized adic derived
pullback with localization of canonical exact module comparison. This is a single
functor identification independent of boundedness and of the family being descended.

`lem-sfb-adic-reduction-cocycle`: the canonical pro-etale reductions of any object
satisfy the scalar reassociation equation. This is the triple tensor-balancing
substep, with no etale origins, constructibility, Tor hypotheses or markings.

`lem-sfb-adic-comparison-composition`: normalized comparison with geometric inverse
image respects two successive scalar changes, for arbitrary coefficient rings and
ring maps. This is the comparison square needed before applying faithfulness.

All four nodes inherit the parent's chapter, unit, and recorded blueprint ancestor;
the parent proof and its `proof_deps` now follow the Lean argument.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
