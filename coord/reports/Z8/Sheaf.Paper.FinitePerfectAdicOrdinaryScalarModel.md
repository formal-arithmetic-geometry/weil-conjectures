## What changed

Moved the existing ordinary source, target, exactness, and compositor declarations
into `Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModelBase`, preserving every public
name and signature.  The item module now imports that base and two new theorem
modules.  Its final theorem is proved by combining the rank-one comparison with
its finite-presentation extension.  The extraction is recorded in
`coord/changes/ordinary-scalar-model-definitions-extraction.md`.

The two unresolved mathematical steps are named public theorems with complete
source-based proof plans and are left as whole `:= by sorry` declarations.
All four delivered Lean modules compile in import order with `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.finitePerfectAdicOrdinaryScalar_model`.
Its proof is a real application of the two strictly smaller split statements.

Added these two named holes:

- `AlgebraicGeometry.Scheme.finitePerfectAdicOrdinaryScalar_components` in
  `Sheaf.Paper.FinitePerfectAdicOrdinaryScalarComponents`, for the rank-one
  quotient comparison and its one-step square.
- `AlgebraicGeometry.Scheme.finitePerfectAdicOrdinaryScalar_compatibility` in
  `Sheaf.Paper.FinitePerfectAdicOrdinaryScalarCompatibility`, extending the
  rank-one square through finite presentations.

No definition contains `sorry`.

## No longer needed

No existing mathematical dependency is pruned.  The completed Koszul comparison
import remains needed by the existing exactness construction through
`completionRingIso`; the scalar-realization, scalar-coherence, completed-reduction,
and flat-quotient declarations remain used by the split statements and the base
module.  The former private helper proof route is removed from the item module
because the two split obligations now carry that route explicitly.

## Where the brief, the DAG or earlier work was wrong

The original single theorem bundled two independent nontrivial arguments: the
rank-one completed reduction and the extension from finite free presentations.
The Lean interface had no module boundary from which new theorem modules could
refer to the ordinary source and target definitions without creating an import
cycle.  Extracting the existing definitions into a base module resolves that
interface issue while preserving the item statement and the unit route.

## New nodes

- `new-s3-finite-perfect-adic-ordinary-scalar-definitions`: the extracted ordinary
  source, target, and compositor definitions, recorded so the base module has a
  declaration node.
- `new-s3-finite-perfect-adic-ordinary-scalar-components`: the rank-one ordinary
  source-target isomorphism family and its consecutive square.
- `new-s3-finite-perfect-adic-ordinary-scalar-compatibility`: extension of that
  square from the rank-one quotient module to arbitrary quotient modules using
  exactness and finite presentations.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicOrdinaryScalarCompatibility": "ad5187ffa8b92ab024b116e184ffe5c000385db6", "Sheaf.Paper.FinitePerfectAdicOrdinaryScalarComponents": "f51063ba6fe9cbd55dfa0e215a35ce8ede085be9", "Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModel": "2a8c62c7f1a3f4be7dada4f7cc3c5baff3a2651b", "Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModelBase": "8c0aed8d7b24698f87189acc18ee14521fe2ca46"}, "results": {"Sheaf.Paper.FinitePerfectAdicScalarModelFactors": {"hash": "b3dda743bc55501f2fb576331942c80bc4d9b4f1", "status": "OK"}}, "seconds": 48, "time": "2026-10-28T08:19:39+0800", "transitive": 0, "version": 1}
```

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
