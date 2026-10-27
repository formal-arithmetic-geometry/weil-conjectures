## What changed

Proved the assigned exceptional-preservation theorem by transporting the existing rational
constructible adjunction through the constructible scalar-extension equivalence from
finite-subextension-valued algebraic-closure coefficients to all continuous-map coefficients.
The coefficient rings themselves remain distinct. The supplied adjunction, compactification,
and statement are unchanged.

The proof constructs the canonical proper-pushforward mate and proves it invertible on
constructible objects using the existing mate Hom-bijection. Combining this map with the
open-extension coefficient isomorphism identifies the actual compactification composites.
The existing rational restriction theorem supplies the constructible adjunction. The proved
generic localizing-generator comparison identifies its transported right adjoint with the
supplied localizing right adjoint. Finally an exact coefficient equivalence handles hΛ.

All additional helpers are private and proved. The categorical mate, equivalence-test,
restriction, closure-transport and adjunction-transport calculations are generic to avoid
unfolding the concrete sheaf functors. Private instances expose the existing finite-type,
quasi-compact and separated assumptions through `Over.mk`. The intended ambient
`finiteTorAmplitude` predicate is explicitly qualified to avoid an imported namespace clash.
The item node records this dependency route.
No definitions, public signatures, source-library files, or consumers were changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousQbarExceptional_preserves_constructibleFiniteTor`.
One original hole closed; zero new holes; zero split-off statements. There are no remaining
`sorry` declarations in this delivery. Existing stated dependencies, including rational
restriction, constructible topology comparison and the topology-mate Hom-bijection, are used
with their existing proofs unchanged; this delivery does not claim to close their holes.

## No longer needed

No modules are withdrawn. No original imports are removed; all new imports are proof-only.
The old proposal to repeat affine-space purity, closed-support,
and finite-open-cover preservation directly for the all-continuous coefficient is unnecessary
in this module. The existing rational restriction theorem retains those steps of unit
`sk-thm-restriction`; the scalar-extension comparison transports its conclusion. Thus the
old direct references `def-weil-closed-immersion` and `def-sbc-affine-space` leave this node's
proof dependencies, while their role in the unit's rational geometric route is retained.
The finite-type and compactification existence dependencies remain needed by the proof's
geometry. The original constructibility and localizing-closure definitions remain in the
statement dependencies; the updated proof dependencies list the actual invoked interfaces.
No dependency is claimed globally unused merely because it is absent here.

## Where the brief, the DAG or earlier work was wrong

The original node correctly distinguished the two algebraic-closure coefficient rings, but
its direct continuous-coefficient geometric plan is longer than necessary given the existing
constructible topology equivalence and normalized mate Hom-bijection. The updated node uses
these existing declarations. It never asserts an isomorphism of coefficient rings or an
ambient derived-category equivalence for their sectionwise inclusion.

The localizing closure is the actual ambient-intersection closure, not a smaller-coproduct
variant. The final coefficient-isomorphism transport preserves that recorded closure. Its
private argument follows the existing consumer ExceptionalInverseImageExistence, which
cannot be imported because that consumer already imports the assigned module.

The endpoint Hom test and equivalence transport require no nonempty-scheme or nonzero-object
assumption; empty schemes and zero complexes are included. No new mathematical statements
with postponed proofs are introduced.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
