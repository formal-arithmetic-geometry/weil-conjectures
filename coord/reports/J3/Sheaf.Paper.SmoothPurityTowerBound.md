## What changed

Proved `AlgebraicGeometry.ProEtale.sp_tower_bound` in
`Sheaf.Paper.SmoothPurityTowerBound` with its original signature and the two original
public definitions unchanged. Private, fully proved helpers compare section-normalized
ordinary and derived evaluations, detect lower cohomological bounds levelwise, and
transport constructibility and Tor amplitude through isomorphisms. The proof combines
these comparisons with `compactSupport_uniform_tor_bound`, the existing smooth fibre
dimension lemma, and compatibility of total right derivation with D+.

Updated `sk-lem-sp-tower-bound`'s proof and proof dependencies to describe this route.
The public imports and the recorded unit-route import are retained. Two proof imports supply right-derived D+ compatibility
and the smooth dimension bound. The coefficient-sheaf definitions are locally
irreducible only during the ordinary comparison, keeping elaboration from unfolding
constant sheafification. After proving transport, the Tor-amplitude and constructible
sheaf predicates, and the derived comparison helpers, are locally irreducible so later
applications use their interfaces. This changes no exported declaration or definition.

Validation: the current module compiled without errors or warnings in 43.4 seconds
through lcompile.py after the resumed dry run exposed a 60-second timeout. The
delivery dry run checks the final packet and its axiom probe.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.sp_tower_bound` (1 of 1 original holes;
node `sk-lem-sp-tower-bound`). Added: 0 holes. Remaining holes in the delivered
module: none. Split off: none. All private helpers are proved.

The proof applies the existing `compactSupport_uniform_tor_bound`, whose proof is now
present in the shared sources. This delivery adds no dependency declaration or hole.

## No longer needed

Removed direct proof imports `Sheaf.Paper.ConstantModelTorAmplitude` and
`Sheaf.Paper.SmoothPurityCoefficientTowers`. The unit-route import
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` is retained.

The well-definedness theorem of `det-def-sfb-constructible-tor-amplitude` concerns
the condensed constant-model predicates and is not used by this proof. The actual
finite-level `HasProEtaleTorAmplitude` definition suffices. The original proof's
Tor-unit tests are unnecessary: the input definition already gives a common
cohomological interval, and the uniform theorem's tower clause supplies the output
cohomological interval as well as the Tor interval.

The direct finiteness theorem of `def-weil-l-adic-coefficient-extension` is not applied:
positive ell-power quotient finiteness is available from the existing normalized-tower
and Base interfaces, and annihilation by ell^(n+1) follows directly in the quotient.
The coefficient-extension and coefficient-tower modules remain transitively needed
for the definitions; neither is globally pruned. The node's proof dependencies now
record the abelian evaluation interface and the pro-etale Tor-amplitude definition.

`Sheaf.Paper.SmoothPurityTowerLevels` stays imported to retain the blueprint unit route.
No whole module is claimed globally pruned. The required change record is
`coord/changes/smooth-purity-tower-bound.md`.

## Where the brief, the DAG or earlier work was wrong

The retained proof attempt was unverified. The compile service now responds, and the
Lean elaboration failures have been repaired. Expensive dependent scalar transports
were handled by a generic pushforward comparison before specialization, with local
coefficient abstraction. Profiling and local irreducibility of the subsequent transport
interfaces repaired the resumed compile timeout. There is no increase of the compile
or heartbeat limits.
The node's original proof unnecessarily rederived input cohomological vanishing from
Tor amplitude and finite coefficient properties from ramification; the existing
interfaces already provide them. No statement or definition repair was necessary.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
