## What changed

The assigned theorem retains its exact name, type, universes and hypotheses. Its proof
specializes the finite-free coefficient-extension theorem to `extensionArrow t`, uses
three independent scalar-transport lemmas, and combines the six clauses.

The compact exchange clause is proved here by an explicit proper/open pasting argument:
expand both compact exchange maps, use naturality of the direct-image comparison,
substitute the proper coefficient square and then the open coefficient square, cancel
the scalar/pullback inverse pair, and apply proper-exchange naturality to scalarOpen.
The comparison naturality clause is proved directly, without constructibility or Tor
hypotheses, from the existing direct-image naturality and scalarOpen naturality.

The definitions moved with unchanged types and values into
`Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions`. The assigned module publicly
reexports them. This allows the three independent scalar lemmas to refer to the
specified maps without an import cycle. This separation is required by their mathematical
dependencies, not by the compiler limit. The new definition module has no sorry.

The declaration block was compared with the current shared source. The only body edit
is explicit unfolding in the pro-etale branch of scalarOpen before applying its original
composite-adjunction expression; it has the same value. Local irreducibility prevents
expansion of chosen adjoints and derived functors during elaboration. Every signature
and visibility is preserved. The final proof compiled without warnings in 6.5 seconds. The change
record is `coord/changes/K8-finite-free-projection-exchange-data-location.md`.
The local proof commands are also recorded there. No existing consumer is adapted. The unchanged consumer
`Sheaf.Paper.FiniteUniversalSmoothTrace` compiled against the sandbox overlay
without warnings in 9.5 seconds.

## Proved and sorry left

One original hole is closed in the assigned module:
`WeilConjectures.FiniteFreeProjectionExchange.finite_free_projection_exchange`
(node `lem-pur-finite-free-projection-exchange`).

This delivery is a decomposition, not a complete proof of the mathematical dependencies.
It adds three named holes, each in its own module and with a complete proof in words:

- `WeilConjectures.FiniteFreeProjectionExchange.finite_free_scalar_projection`
  (`Sheaf.Paper.FiniteFreeScalarProjection`, node
  `lem-pur-finite-free-scalar-projection`): the normalized tensor family and the
  proper/open/compact projection squares for a general finite-free finite-ring map.
- `WeilConjectures.FiniteFreeProjectionExchange.scalar_exchange_constituents`
  (`Sheaf.Paper.ScalarExchangeConstituents`, node
  `lem-pur-scalar-exchange-constituents`): the proper and open coefficient exchange
  squares for a general map of finite rings; it does not state compact exchange.
- `WeilConjectures.FiniteFreeProjectionExchange.finite_free_compact_scalar`
  (`Sheaf.Paper.FiniteFreeCompactScalar`, node
  `lem-pur-finite-free-compact-scalar`): invertibility and coherent refinement of the
  finite-free compact coefficient comparison; it does not state projection or exchange.

There are zero sorries in the assigned module, three added sorries in total, and none
inside a definition or private helper. Net hole change for this reduction is 1 - 3 = -2.
The required dry run passed at commit `7e1288c0b6` with review class CODEX.
The automatic axiom probe for the assigned module timed out on that run; the
delivery tool explicitly schedules it for the merge to repeat. It reported no
forbidden axiom. This does not assert a completed axiom audit for the packet.

The private direct naturality, compact-comparison naturality, exchange factorization,
proper-exchange naturality and compact-exchange pasting lemmas are fully proved.

The lower statements are genuine, separate parts of the original source argument.
None has the original conjunction as its conclusion, none assumes that conjunction,
and none is the target under a different name. They are general scalar-transport
results, independent of the finite-field datum and coefficient-extension stages.
The assigned proof supplies their arithmetic specialization and the compact-exchange
pasting rather than merely applying a renamed target.

Edge cases were checked mathematically: identity coefficient maps and identity
refinements recover the unit equations; the zero target coefficient ring gives the
zero category and is covered by a finite free module of rank zero; empty schemes give
zero sheaves; arbitrary Cartesian pullbacks are allowed because constituent comparison
squares are identities of mates and do not assert base-change invertibility. The finite
free case lets scalar extension be computed by finite direct sums on all derived
objects, so the strengthened invertibility statement needs no boundedness hypothesis.
Refinement is only asserted on the bounded-below etale origins already used by the
published refinement isomorphisms.

## No longer needed

The former proof-only imports below are not used by the Lean terms of the assigned
module or the unchanged definitions and have been removed. Several remain the stated
proof dependencies of the new separate source lemmas; those dependencies are not claimed
to be mathematically pruned. A future proof imports the interfaces it actually uses.

- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`
- `Sheaf.Paper.SfDirectImageCTFNonproper`
- `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`
- `Sheaf.SixFunctors.EtaleOpenTensor`
- `Sheaf.SecSmoothPurity.OpenScalarExchange`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.Paper.FiniteCoefficientFlatModel`
- `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.Paper.CoefficientRealizationTransport`
- `Sheaf.Paper.ProperOpenCoefficientRefinement`
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`
- `Sheaf.Paper.OpenExtensionFiniteTor`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `WeilConjectures.Compactification.NagataCompactification`

The assigned node's immediate proof dependencies now consist of the finite-free
coefficient theorem, direct-image naturality and the three new scalar lemmas. Its old
tool approvals not used by this immediate proof were removed, preserving their order.
The removed top-level approval entries, in their original order, are:

- `cor-cbc-derived-extension-zero-base-change`
- `cor-sf-direct-image-ctf-nonproper`
- `cor-sf-direct-image-ctf-proetale`
- `lem-amb-etale-compact-comparisons`
- `lem-cbc-extension-zero-base-change`
- `lem-coef-etale-open-tensor`
- `lem-fix-open-scalar-exchange`
- `lem-kun-dimension-finite-type`
- `lem-pc-kflat-resolution`
- `lem-pur-derived-change-of-rings`
- `lem-sf-flat-model`
- `lem-sf-open-comparison-unit-normalization`
- `lem-sf-open-tensor-normalization`
- `lem-sf-pf-coefficient-realization-transport`
- `lem-sf-proetale-constructible-origin`
- `lem-sf-proper-open-coefficient-refinement`
- `lem-sf-proper-open-comparison-site-normalization`
- `lem-trf-open-ctf`
- `lem-weil-finite-compact-projection-formula`
- `lem-weil-pbc-comparison-direct-image-canonical-mate`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-site-morphism-composition`
- `lem-sf-comparison-tor-amplitude`
- `thm-nagata-compactification`

These are removed from this node’s immediate proof, not declared globally obsolete.

No module is claimed globally pruned: the original public imports and transitive API
are preserved through the definitions module. The blueprint unit's route is retained.

## Where the brief, the DAG or earlier work was wrong

The inherited report described an unavailable object file and an unreachable compile
server. The published imports are now available; these were transient infrastructure
failures, not a mathematical obstruction. The interrupted compiler/delivery results
were checked before repeating work; no previous successful delivery was found.

The original ten-step plan names the structural computations but provides no Lean
interface directly expressing their normalized fixed-module scalar squares. The three
new lemmas isolate those computations. Existing coefficient/site and intrinsic ringed
interfaces use different presentations; they do not directly inhabit these equations.
The packet does not claim that merely invoking conditional coefficientRealizationTransport
verifies its primitive hypotheses. Instead it records the remaining hypotheses as
separate source lemmas and proves the compact-exchange pasting explicitly.

A compiled tentative split into two broad halves was discarded in favor of the three
independent scalar results above. No provisional ComparisonPart or GeometryPart
placeholder is part of the delivery.

The downstream helper exited 137 without output; an independent source import scan
found one direct/transitive consumer, `Sheaf.Paper.FiniteUniversalSmoothTrace`.
The move preserves all names, types and values, so no forced adaptation is needed.

## New nodes

`def-pur-finite-free-projection-exchange-data` records the moved, unchanged specified
maps and equations. It has no proof hole and is publicly reexported by the assigned module.

`lem-pur-finite-free-scalar-projection` records source Steps 3--5 and 8: normalized
ordinary balancing, proper/open projection squares and their compactification composite.

`lem-pur-scalar-exchange-constituents` records source Steps 3, 4, 6 and 7: the
scalar/inverse-image cube, its proper mates and the open-unit exchange equation.

`lem-pur-finite-free-compact-scalar` records source Steps 2, 9 and 10: finite-free
invertibility and etale/pro-etale coherent compactification refinement.

Each new theorem has its own module, exact Lean statement, source, proof in words,
three logged Mathlib searches and declared dependencies. The existing item node's proof,
proof dependencies and proof origin follow the actual combining proof.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
