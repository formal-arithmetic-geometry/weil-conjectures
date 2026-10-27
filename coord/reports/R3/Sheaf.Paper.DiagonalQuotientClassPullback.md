## What changed

Replaced the hole in `Sheaf.Paper.DiagonalQuotientClassPullback` by a complete categorical
pasting proof. The private `scalar_pullback_paste` uses naturality of the scalar/pullback
mate, the integral class square, and both scalar class squares. It derives invertibility
of the needed source component from the supplied normalized source isomorphisms, then
cancels it. It requires no global invertibility theorem for the scalar/pullback comparison.
The theorem's signature and both public imports are preserved. A second proved private
helper, `diagonal_scalar_paste_generic`, performs the derived-category instantiation over
abstract coefficient rings. This and explicit associativity rewrites prevent expensive
unfolding of concrete inverse-limit coefficients during elaboration.

Added `Sheaf.Paper.DiagonalScalarPullbackComparison`, constructing the comparison from
`CondensedRing.derivedComapUpperStarIso` and the actual scalar adjunctions. This is a real
construction for arbitrary coefficient maps, including nonflat quotients. Its
`ScalarPullbackEndpointSquare` wrapper states the shifted equation once with abstract
modules, keeping concrete inverse-limit twists out of equation elaboration.

The two new proof imports isolate its shifted line normalization and its supported-source
normalization. Neither lower statement mentions a diagonal class, diagrams, traces, or
class compatibility. The first concerns only the quotient line along one scheme map;
the second concerns only supported coefficient objects, for arbitrary coefficient rings.
Their combination with the three given class equations is proved in the assigned module.
The DAG now follows this argument.

## Proved and sorry left

One original hole closed:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalQuotient_classPullback`.
The assigned module has zero remaining holes. Its two private pasting lemmas, both
comparison definitions, and the endpoint-square proposition contain no holes.

Two holes added, each the whole proof of a public named theorem in its own module:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalQuotient_linePullbackNormalization`
  (`lem-diagonal-quotient-line-pullback-normalization`).
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalSupported_pullbackScalarNormalization`
  (`lem-diagonal-supported-pullback-scalar-normalization`).

This is a decomposition: one upper hole closed and two strictly smaller endpoint
coherence obligations added, not a claim of a completed proof without new obligations.
Both new statements have complete proof descriptions and source references. Edge cases
include n = 0, π = 0, unit π, ramified quotient levels, and zero coefficient rings; the
statements impose no flatness or nonzero assumptions. Invertibility comes only from the
explicit Endpoint and SourcePullback data.

All four modules compile through lcompile.py without debugging options. The final
assigned module compiles without warnings in 11.1 s; the comparison, line normalization,
and supported normalization compiled in 9.7 s, 20.3 s, and 5.6 s respectively. The
independent delivery probe remains the final check.

## No longer needed

The original two public imports remain necessary for the statement. No existing Lean
module is withdrawn. The following planned proof dependencies are removed from the
assigned node, and neither is imported by this proof or its new normalization modules:

- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, module
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: the argument only uses a
  scalar adjunction mate and its two endpoint identities, not a general tensor comparison.
- `lem-weil-pbc-proetale-abelian-closed-support`, module
  `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`: ordinary supported pullback
  isomorphisms are already supplied; their normalization is used, not their existence.

The former endpoint/scalar/source definition dependencies are retained where used in the
new nodes. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The live queue identifies this as a proof-route item with one hole. The rework archive and
build-error file retain the older failed-import report, but the existing item compiles
against the current published dependencies; there is no current declaration collision
in this file requiring a rename.

The old DAG did not supply a declaration identifying the scalar/pullback comparison with
the two prescribed endpoint boundaries. Those missing steps are now explicit. The
existing `CondensedRing.derivedPullIso` assumes flat scalar extension and therefore is
not directly applicable to this quotient statement. The constructed comparison uses
exact restriction instead and makes no such assumption.

## New nodes

`def-diagonal-scalar-pullback-comparison` records the exact restriction/pullback
isomorphism and its scalar adjunction mate. Both definitions and the endpoint-square proposition are constructed with existing
APIs and contain no postponed data or proof.

`lem-diagonal-quotient-line-pullback-normalization` records the shifted line endpoint
identity. It has only one geometric map and no supported source or class arrow.

`lem-diagonal-supported-pullback-scalar-normalization` records the degree-zero supported
source identity. It is independent of the quotient line and class arrows.

All three come from paragraph (3) of the latest diagonal coefficient proof. Searches
using LeanFinder, Loogle, LeanSearch, and local rg identified generic naturality and
adjunction APIs, but no existing statements of these endpoint identities. No existing
public statement, definition, attribute, or public import is changed, so no existing
consumer adaptation or interface change record is needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalQuotientClassPullback": "55ae679ac597bd83fcc4d679a18b9ee3e2615b93", "Sheaf.Paper.DiagonalQuotientLinePullbackNormalization": "89384d15172e0ea7eafe1b60297ea4488bf2e03e", "Sheaf.Paper.DiagonalScalarPullbackComparison": "8b8eb1906197f0994015eb28d39bd7be564e5dde", "Sheaf.Paper.DiagonalSupportedPullbackScalarNormalization": "c2dece57417bab6fe26f7bb96f7501fe7f556e66"}, "results": {"Sheaf.Paper.DiagonalQuotientBaseChange": {"hash": "eca8dea5122642169084816f470e4460889d77f4", "status": "OK"}}, "seconds": 163, "time": "2026-10-28T03:47:25+0800", "transitive": 0, "version": 1}
```

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
