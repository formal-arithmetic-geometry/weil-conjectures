## What changed

`AlgebraicGeometry.ProEtale.CondensedRing.finiteProperBaseChange` is reduced, with the original
three-clause signature, to the recorded finite internal/etale realization, the proper
geometric-fibre torsion bound, the etale finite-Tor proper-image theorem, and canonical
operation comparisons. The Lean proof enlarges a Tor interval to `[min a b,b]`, handles
the zero ring by replacing the annihilating exponent by `r+1`, constructs the coefficient
ring isomorphism from locally bijective constant functions, and transports constructibility
and Tor amplitude along actual exact equivalences.

For exchange, the existing source-library theorem
`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper` applies to the retained bounded-below
etale antecedent and permits arbitrary base-change schemes. For projection, the proof
uses the derived tensor connectivity estimate to supply the comparison theorem's actual
bounded-below domain, applies the torsion etale projection formula, and invokes the proved
source-library `isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived`.
Naturality transports the antecedent isomorphisms in both variables.

Four new modules construct the exact coefficient-encoding functor and isolate the
exchange and projection comparisons. Each comparison is a separate change of presentation,
with no properness, constructibility or invertibility hypothesis. The exchange is an
arrow isomorphism with a proved invertibility corollary. For projection, the retained
statement is precisely equivalence of invertibility under the constructed encoding,
the consequence of the canonical-arrow comparison that the main proof needs. It spells
out the published right-adjoint projection expression. Two constructed named propositions
retain its internal and ordinary invertibility properties without repeatedly calculating
the morphism endpoints. Their equivalences to the published `IsIso` expressions are proved
by reflexivity; no mathematical condition is added. The ordinary named property's API
also proves invariance under isomorphisms in both inputs by naturality. The main proof
uses this API rather than recalculating the derived projection's endpoints.
The item DAG follows this proof. A proved private combination lemma works with an
abstract coefficient ring and its actual normalized encoding; the public theorem
specializes it to the sheafified coefficient ring. This avoids repeating the coefficient
construction in the combination proof.
Source-library declarations, signatures, definitions,
attributes and public imports are untouched.

`finiteProperAmbientExchange` is now an abbreviation of the same constructed mate through the shared
`finiteProperExchange` definition. The latter is in its own module because the comparison
statement and the item both need the canonical arrow, without an import cycle.
Its horizontal functors and square wrapper are explicit; they are the data inserted by
the original coercions. Local instance families and irreducibility settings avoid repeated
monoidal and derived-functor unfolding. In particular, local coefficient monoid instances
name the actual bundled structures; they avoid repeated expansion of sheafification when
specializing the generic proof. The change record lists the sole existing user.

## Proved and sorry left

Closed the one original hole of
`AlgebraicGeometry.ProEtale.CondensedRing.finiteProperBaseChange`
(node `det-thm-sfb-proper-base-change-finite`). Its module has zero remaining `sorry`.
Its coefficient identification, preservation, Tor-connectivity and naturality helpers
are private and proved. The private `EncodedEtaleOrigin` dependent-pair type retains the actual antecedent,
Tor interval, and comparison isomorphism from the same realization argument. Its data
are constructed and contain no holes. Standard dependent pairs avoid generated specialized
inductive declarations and their repeated category calculations.

Added two holes, in genuinely separate canonical-arrow comparison statements:

- `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientExchangeEncoding`
  (`lem-sfb-finite-coefficient-exchange-encoding`).
- `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientProjectionEncoding`
  (`lem-sfb-finite-coefficient-projection-encoding`).

This is a decomposition: one original hole closed and two comparison holes added,
not a net reduction of holes. Neither lower statement asserts proper base change,
proper-image constructibility, or the projection formula. The coefficient functor and
its equivalence instance and the shared canonical exchange construction have zero holes.
Existing imported theorem holes are retained
under their existing nodes; they are not newly introduced by this delivery.

Validation: `lcompile.py --all` compiled all five delivery modules successfully.
The theorem signature and the coefficient-ring construction were checked verbatim
against the shared original. All seven packet node dependency lists match their proof
steps, and the new Lean attachments match the delivered declaration signatures.

## No longer needed

Removed the following direct proof imports. Some remain transitively needed by the
realization or Tor-image theorem, so removal from this file does not claim their global
withdrawal:

- `Sheaf.Paper.FiniteDiscreteCondensedRing`.
- `Sheaf.Paper.FiniteDiscreteSchemeRing`.
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`.
- `Sheaf.AlgebraicGeometry.DimensionExtension`.
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedPointCohomologicalDimension`.
- `Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`.
- `Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange`.
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`.

The following modules leave this item's transitive import closure relative to the
original module; this is a local closure audit, not a claim that all other targets cease
to use them. No source declaration or module is withdrawn:

- `Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange`.
- `Sheaf.AlgebraicGeometry.ComparisonReflectsTorsion`.
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedEncoding`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExchangeEncoding`.
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedPointCohomologicalDimension`.
- `Sheaf.SixFunctors.ClassicalDefinition`.

The finite coefficient identification is constructed directly in the original universe,
so no small-ring replacement is needed. The declared realization bundles the constructible
and finite-Tor comparisons and proper direct-image comparison. The geometric-fibre bound
bundles the dimension argument. Tensor connectivity replaces the explicit flat-model and
K-flat argument. Existing fixed-scalar source proofs replace a second proof of ordinary
exchange and site-comparison projection transport.

Removed precisely these obsolete direct `tool_uses` entries from the item's node; their
mathematics may still occur inside retained dependencies:

- `lem-weil-pbc-finite-discrete-condensed-ring-constant`.
- `lem-weil-pbc-finite-discrete-scheme-ring-constant`.
- `det-pe-finite-tor-comparison-noetherian`.
- `lem-fin-finite-type-fibre-dimension-bound`.
- `lem-weil-pbc-proper-base-change`.
- `lem-kun-dimension-extension`.
- `lem-kun-cd-sep-closed-point`.
- `thm-sc-finite-type-torsion-cd`.
- `sk-thm-pe-direct-image-comparison`.
- `lem-pc-bounded-above-flat-kflat-site`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `sk-thm-pe-constructible-comparison`.
- `sk-thm-properbasechange`.

The route retains `det-ctf-finite-proper-tor` and classical torsion proper base change,
as required by the unit. The new node proof dependencies retain the generic normalized
coefficient and mate comparisons needed to prove the two residual assertions.

## Where the brief, the DAG or earlier work was wrong

The old file's imports alone did not identify the internal canonical arrows with their
ordinary fixed-scalar presentations. The existing
`finiteCoefficientDerivedExchangeIdentification` has qcqs hypotheses on all four
corners; the item permits arbitrary `X'` and `Y'`. It therefore cannot directly supply
the required exchange identification. The separate new comparison makes no such
restriction and does not assume the desired invertibility.

The ordinary projection comparison requires a lower bound for
`C tensor^L Lp*D`, not just for `C`. The Tor-connectivity argument supplies this hypothesis
explicitly. No regularity assumption on the finite coefficient ring is used.
`lem-weil-pbc-proper-base-change` expresses stability of properness under base change;
it is not the cohomological base-change theorem. The fixed-scalar source attachment
therefore also records the actual torsion cohomological theorem it uses.

## New nodes

`def-sfb-finite-proper-exchange` records the existing canonical mate construction as a
shared operation. It has no hole and asserts no invertibility. The original item's
exchange name is an abbreviation with the original inferred type.

`def-sfb-finite-coefficient-operation-encoding` records the constructed inverse-isomorphism
scalar restriction followed by the normalized fixed-scalar encoding, and its proved
`IsEquivalence` instance. The forward functor is actual termwise derived scalar
restriction, not arbitrary equivalence data.

`lem-sfb-finite-coefficient-exchange-encoding` records the source-grounded comparison of
canonical unit-square-counit arrows on arbitrary schemes. It is independent of properness
and boundedness. Empty schemes, zero objects and the zero ring use the same exact
adjunction and comparison equations.

`lem-sfb-finite-coefficient-projection-encoding` records the source-grounded comparison
of invertibility of the two canonical projection arrows, using the balanced pure-tensor
comparison, compatibility with derived counits, and reflection by the encoding equivalence. It is independent of any projection-formula theorem.
Zero objects and zero rings use the same balanced tensor universal property.

`lem-sfb-fixed-scalar-etale-origin-proper-exchange` attaches the existing proved source
proper-exchange theorem to the exact fixed-scalar presentation used here. The existing
finite-level node instead attaches an intrinsic continuous-ring module presentation;
this adds no duplicate Lean declaration or hole.

`lem-sfb-fixed-scalar-derived-projection-transport` attaches the existing proved source
transport theorem, with its actual bounded-below domain and flat-pullback hypotheses.
It adds no Lean declaration or hole and records the reusable source result rather than
reproving it from the much larger ringed comparison interface.

Change record: `coord/changes/E8-finiteProperAmbientExchange-elaboration.md`.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
