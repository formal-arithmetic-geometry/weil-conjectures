## What changed

Proved the arrow-isomorphism assembly in `Sheaf.Paper.FiniteCoefficientExchangeEncoding`
from one inverse-image comparison theorem. The original two public theorem signatures,
public imports, and mathematical coefficient/adjunction/exchange maps are unchanged.
Factored the canonical pullback-square expression in the unclaimed
`Sheaf.Paper.FiniteProperExchange` into the explicit, hidden definition
`finitePullbackSquare`, and added the proved `finiteProperExchange_eq_mate` API.
The existing exchange signature, attributes and mathematical map are unchanged;
its body now refers to that named square. The middle equality transport is
implemented by equality induction. The proved `finitePullbackCongr_eqToIso`
identifies it with the old `eqToIso (congrArg ... h)` transport, so the square and
exchange are the same maps. This fixes the profiled kernel timeout at equality
transport, following the existing ordinary `leftDerivedUpperStarCongr` convention. The item imports the square body only
for its private composition-cube proof. Change record:
`coord/changes/G5-finiteProperExchange-counit-api.md`.
Local irreducibility annotations on coefficient and derived-functor constructions
prevent large definitional unfolding; `respectTransparency` is enabled.
The new statement uses
explicit functor result types. Its internal functor alias extracts the source
functor of the published `leftDerivedUpperStarIsoMapDerivedCategory`, retaining
exactly its existing K-flat instance arguments rather than re-synthesizing them.
This chooses no mathematical data: the source functor is definitionally the existing
`(CondensedRing.upperStar R f).leftDerivedFunctor`. The private `encoding_congr` lemma proves the equality-transport case by induction
on the scheme-morphism equality.

The private abstract `exchangeArrowIso` helper performs the mate calculation over
abstract categories; specializing it avoids kernel conversion of large concrete
module-object instances. It has a complete proof and introduces no new hole.
The assembly uses `composition_square_aux` on the two composition equations to prove
the inverse-image cube. It defines the two direct-image comparisons as actual mates,
proves them invertible using equivalence of the coefficient functors, applies the
proved `coefficient_exchange_of_counit_at` theorem, and constructs the arrow
isomorphism with `Arrow.isoMk`. Thus it proves the direct-image/exchange part of the
argument without a new K-injective or derived-adjunction comparison obligation.

Added `Sheaf.Paper.FiniteCoefficientPullbackEncoding`, which states only that the
actual coefficient encoding commutes with total inverse images and their published
composition isomorphisms. Its three abbreviations expand to the existing functors
and a dependent family of natural isomorphisms. They choose no data and contain no
holes. The new theorem has no direct-image or exchange arrow in its statement.
The new node records the existing underived encoding comparison, general-universe
constant-section naturality, and exact localization route. Updated the item's node
proof and dependencies to match the Lean assembly.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientExchangeEncoding`
(node `lem-sfb-finite-coefficient-exchange-encoding`) by a complete assembly proof.
The existing proved corollary `finiteCoefficientExchangeEncoding_isIso` is retained.
The item module has zero holes. The added `CondensedRing.finiteProperExchange_eq_mate`,
`finitePullbackCongr_rfl` and `finitePullbackCongr_eqToIso` are proved without any
new hole; its definition node is
`def-sfb-finite-proper-exchange`.

Added one hole:
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback.finiteCoefficientPullbackEncoding`
(node `lem-sfb-finite-coefficient-pullback-encoding`). Its proof is exactly `by sorry`,
with a source and complete proof in words in its docstring and node.
This is a decomposition: one hole closed and one strictly narrower inverse-image
obligation added, net zero holes. It is not reported as an unconditional proof of
coefficient exchange. No hole is added to a definition or a private declaration.

## No longer needed

No original public import or module is withdrawn. The following old direct proof
plan dependencies are removed from the item's `proof_deps`:

- `lem-sfb-internal-module-operations-transport`: the new inverse-image comparison
  uses the more concrete, already proved normalized encoding comparison.
- `lem-weil-pbc-finite-discrete-coefficient-sections`: its recorded Lean theorem
  takes the coefficient ring in `Type 0`. The general-universe proved
  `canonicalAbelianMap_naturality` supplies the required normalization instead.
- `lem-sfb-constant-scalar-geometric-adjunctions`: the concrete encoding comparison
  already proves the needed fixed-scalar identification.
- `lem-derived-exact-equivalence-squares`: total direct-image comparisons are
  invertible mates along coefficient equivalences, so no separate universal
  right-derived square is required.
- `lem-kun-derived-adjoint-square-comparison`: the defining-mate equations suffice for
  the direct-image/exchange assembly.
- `lem-weil-pbc-conjugate-iso-unit-equation`: no longer directly used in the item;
  it remains part of the residual inverse-image proof route.
- `lem-weil-pbc-proetale-derived-pullback-composition`: no longer directly used in
  the item; it remains part of the residual inverse-image proof route.

None of these removals asserts global unreachability: other consumers and the
residual theorem may still need their modules. No source-library declaration is
removed or changed. The general mate-invertibility and coefficient-exchange lemmas
are used as categorical tools; they do not bypass a unit's geometric route.

## Where the brief, the DAG or earlier work was wrong

The existing `finiteCoefficientDerivedExchangeIdentification` requires qcqs
hypotheses at all four schemes; the item is on arbitrary schemes. It cannot be
used directly. The existing `encoding_pullback_fixed` is objectwise on hearts and
has neither inverse coefficient-isomorphism transport nor the total-derived
composition equation, so it cannot by itself close this item.

The original plan derives both direct-image squares by resolutions and compares
specified derived adjunctions. This is unnecessary once the inverse-image comparison
is composition compatible: the existing mate-invertibility theorem applies because
both vertical coefficient functors are equivalences. The actual exchange arrows
then satisfy the required rectangle by the proved counit-mate calculus.

The `finiteDiscreteCoefficient_coefficientUnit_pushforward` interface is restricted
to a Type-zero coefficient ring. There is already a proved replacement in the
required universe, `canonicalAbelianMap_naturality`. The new residual node uses it
and the proved private `encodingPushforwardNatIso` in the module of the existing
underived pullback comparison, rather than duplicating that construction.

The new statement was checked on the zero ring, zero complexes, empty schemes,
identity and repeated morphisms. The identity-on-sections comparisons and exact
localization apply unchanged. No properness, constructibility, qcqs, boundedness,
or invertibility of exchange is introduced. No target or existing statement is altered. The proved equal factoring
of the exchange construction is documented in
`coord/changes/G5-finiteProperExchange-counit-api.md`; no consumer adaptation is needed.

## New nodes

`lem-sfb-finite-coefficient-pullback-encoding` states the inverse-image comparison
and its composition equation for the actual `coefficientEncoding`, arbitrary
normalized encodings, and arbitrary schemes. It is strictly a part of the original
argument: it contains no direct images or exchange arrow. The delivered proof
constructs the right-adjoint comparisons, proves their invertibility, proves the
square cube from the two path composition equations, and applies the counit-mate
calculus; none of those conclusions is assumed by the new statement.

The source is the blueprint finite-coefficient transport step, expanded using its
existing normalized encoding and exact-localization dependencies. Searches checked
LeanSearch, Loogle/mates, Mathlib source, the whole blueprint index, and the project's
encoding modules. No existing declaration gives this composition-compatible family
for arbitrary coefficient-isomorphism transport and arbitrary schemes.

Validation: all three delivered Lean modules compile cleanly through `lcompile.py --all`
(36.3, 53.3 and 52.6 seconds). Both original item theorem signatures and all original
public imports were checked verbatim; the new theorem matches its node statement.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
