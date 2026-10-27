## What changed

Replaced the hole in `diagonalUniformizer_finiteModels` by a construction from a
proved regular-unit normalization and one strictly smaller single-scheme line step. The finite realization uses the existing
`finiteDiscreteCoefficientEquivalence` with the concrete internal-action encoding;
its functor, underlying sheaf comparison, and coefficient ring isomorphism are real
constructions. The regular-module normalization is proved in
`DiagonalFiniteEncodingUnit`, using the module-localization unit and the
constant-sheaf adjunction at the terminal pro-etale object. Its additional regular-module hypothesis excludes
scalar-twisting encodings, and is proved for the concrete encoding in the item.
The normalized unit equation determines the chosen unit isomorphism uniquely,
because the underlying comparison is invertible and the forgetful functor is faithful.

Constructed the ordinary pushforward square for every scheme morphism from the
existing sectionwise encoding comparison and its proved underlying equation.
Constructed the supported-source comparison by taking this square at the diagonal
and composing its regular-module component with direct image of the specified unit
isomorphism. The source normalization follows by cancellation of underlying
isomorphisms. Neither construction is a new hole.

The separate single-scheme theorem `diagonalQuotientRootEndpoint` isolates the
completed-integral-line reduction and root normalization, without any coefficient
realization existence, supported source, or pushforward assertion. The item uses
it at P and W with the supplied finite roots; its proof plan constructs the
existing canonical integral root maps. The statement uses the existing
`QuotientLineRealization` package, keeping serialization of the expanded root
projection expression out of the theorem signature.
Its endpoint is uniquely determined by the root generators. The integral root
map is determined by its limit projections, and the finite root isomorphism
by its kernel inclusion. Thus choosing the resulting line package does not
choose arbitrary data from a mere existence theorem. No existing signature,
public import, shared definition, or source-library file changed.

Validation: `lcompile.py --all` accepted all three modules together with exit code 0
and no compiler warnings. Compared the original and delivered signatures and public
imports of the item; both are identical.

## Proved and sorry left

Original holes: 1, in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_finiteModels`.
Its proof body is replaced by a complete combination of the proved unit
normalization, the existing ordinary comparisons, and the lower line statement.
This is a decomposition, not a sorry-free proof of the mathematical result.

Proved without sorry:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.finiteEncoding_unitComparison`
(`lem-diagonal-finite-encoding-unit`), including its exact underlying-sheaf equation.
The private realization construction, discrete-quotient argument, normalized
ordinary squares, and supported-source calculation are also complete.

Holes added: 1, the entire proof of the named public theorem
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalQuotientRootEndpoint`
(`lem-diagonal-quotient-root-endpoint`), the single-scheme quotient root endpoint.

No sorry remains in the assigned module or the unit-normalization module. No
definition contains a sorry. Net hole change in this packet is zero; it remains
a decomposition of the original hole, with substantial coefficient and functor
glue proved, rather than a claim of net proof progress.

## No longer needed

The construction does not use `diagonalFiniteRoots_exists`, node
`lem-diagonal-finite-root-map`, module `Sheaf.Paper.DiagonalFiniteRootMap`: the
original theorem already supplies `rootsP` and `rootsW`. Its dependency is removed
from the item's proof route. No public import is removed, and no module is withdrawn. The main module needs no
direct import of `DiagonalIntegralRootMap`: its canonical map construction is
retained in the proof plan of the single-scheme line lemma.

The separate existential `finiteDiscreteSchemeRing_constant` is unnecessary:
`finiteDiscreteSchemeRingIso` supplies the explicit pullback comparison directly.
The scheme-ring construction remains needed through `FiniteDiscreteCoefficientEncodingData`
and the new unit step, so its node and module are not globally pruned.

`ambTateRootProjectionReduction` does not directly prove this item's root endpoints:
it uses constant ring sheaves and `SheafOfModules`, whereas `quotientLine` is extension
of scalars of an inverse limit over completed condensed coefficients. Its root
projection argument is retained below the new single-scheme node, not bypassed or
claimed globally unnecessary. The restriction-encoding module also stays needed:
its existing ordinary pushforward comparison and normalization are used directly.

## Where the brief, the DAG or earlier work was wrong

The old proof plan combined the following distinct steps without a Lean bridge:
regular-unit normalization of the finite encoding, ordinary pushforward
normalization, and transport of completed-condensed root lines to finite ordinary
root lines. The existing inverse-image encoding theorem does not itself state the
ordinary square, but its module already proves the needed ordinary comparison.
This delivery uses those proved internal entry points and performs the supported
source calculation explicitly.

An arbitrary equivalence G with equality of forgetful functors can twist scalars
by a ring automorphism. Therefore preservation of underlying groups alone does not
justify the prescribed unit normalization. The new unit lemma includes the exact
regular-module normalization, and the item's concrete action encoding satisfies it.
No original statement is marked disputed or changed. The unit and chapter routes
are retained.

## New nodes

`lem-diagonal-finite-encoding-unit`, module
`Sheaf.Paper.DiagonalFiniteEncodingUnit`, isolates the unit part of proof step 1.
It also names the existing inverse encoding and constructs its natural underlying
comparison. Its complete proof constructs the regular-module comparison from the localization
unit at the terminal object, then proves its precise normalization with the
constant-sheaf counit identity and the adjunction triangle. It applies to zero rings and empty
schemes, and uses no finiteness assumption on B.

`lem-diagonal-quotient-root-endpoint`, module
`Sheaf.Paper.DiagonalQuotientRootEndpoint`, isolates the line part of proof step 2
for one scheme and prescribed finite roots, with the canonical integral root map. Its proof describes
local primitive-root generators, reduction by the positive exponent, transport
of the free-module adjunction through the underlying-sheaf comparison, descent,
and uniqueness. It preserves the case n=0, arbitrary ramification, and the empty scheme.
The proof plan cites `lem-poincare-compatible-primitive-roots` only for its
general abelian root-diagram basis, reindexed to positive levels. This supplies
the actual cover and compatible generators, which the integral-root-map
existence theorem alone does not supply. It avoids the much larger theorem
`det-def-sp-tate-twist-locally-free`; no duality or trace assertion is used. The
maintainer may record this generic tool approval; this packet does not write
`tool_uses`. No change record is needed because all existing
interfaces are unchanged.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
