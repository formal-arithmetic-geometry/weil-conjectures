## What changed

Decomposed `WeilConjectures.WeilChosenDualityExchange.weil_chosen_duality_exchange`
without changing its signature. The existing interfaces moved verbatim to
`Sheaf.Paper.WeilChosenDualityExchangeData`, publicly re-exported at the old path,
so the new proof-step modules can import them without a cycle. The change record is
`coord/changes/D2-weil-chosen-exchange-interface.md`.

The private `ordinary_maps` proof verifies the original ordinary unit, counit and
both Hom bijections on carriers. It expands the actual lifted adjunction and the
Mathlib `homEquiv_unit`/`homEquiv_counit` formulas, eliminates the supplied HEq, and
concludes by reflexivity. This proof compiled before the interface relocation.

The private `exchange_of_natural` construction turns the specified natural components
into tau. It maps the actual chosen comparison through the flipped Hom bifunctor,
whiskers by the ordinary direct-image functor, and composes with tau. Both component
formulas are definitional. The main proof obtains normalized data, proves the ordinary
maps and supplies this Exchange for every choice of structure right adjoints.

The two remaining steps are strictly smaller: normalized geometric/Hom data, and the
three-transpose naturality square for any supplied normalized data and target pair.
Neither restates the existential conjunction of the item or packages it as a hypothesis.
The assembly proves the ordinary-map clause and constructs the final comparison
substitution instead of postponing either one.

## Proved and sorry left

Closed one original textual hole:
`WeilConjectures.WeilChosenDualityExchange.weil_chosen_duality_exchange`
(node `lem-sf-weil-chosen-duality-exchange`). Its proof from the two subclaims is complete and compiled in 15.2 seconds.
The item module has zero remaining sorry. All 18 original public signatures and all
17 relocated interface bodies were compared mechanically and are unchanged. The
interface and both new statement modules compiled, and the final assembled item
compiled cleanly through lcompile.py. The DAG has no new cycle or missing edge.

Added two holes, each the entire proof of a public theorem in its own module:

- `WeilConjectures.WeilChosenDualityExchange.weil_chosen_exchange_construction`
  (`lem-sf-weil-chosen-exchange-construction`), in
  `Sheaf.Paper.WeilChosenExchangeConstruction`.
- `WeilConjectures.WeilChosenDualityExchange.weil_chosen_transpose_naturality`
  (`lem-sf-weil-chosen-transpose-naturality`), in
  `Sheaf.Paper.WeilChosenTransposeNaturality`.

This is a decomposition, not an axiom-free proof of the original mathematical result:
one hole closed, two added, net minus one. The two private helpers have complete bodies.
No data definition has a sorry or selects arbitrary data from an unproved existence theorem.

## No longer needed

All four original public imports are preserved by the re-exported data module:
ConstructibleMateCoherence, CompactSupportProjectionFormula,
CoefVerdierWeilEquivariance and Mathlib.CategoryTheory.Adjunction.Unique.
The following proof-only imports are unnecessary in the assembled item and removed:
Sheaf.Paper.IntegralConstructibleInternalHom,
Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence,
Sheaf.Paper.DerivedAutomorphismHomEvaluation,
Sheaf.Paper.IntegralOperationsPreserveConstructible,
Sheaf.Paper.SfIntegralCompactSupportConstructible,
WeilConjectures.SixFunctors.Etale.Derived.Adjunctions and
WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius.

The construction subclaim still needs the mathematical domain/evaluation/coherence
steps, which its node records. Thus removal of a direct proof import does not claim
that those modules are globally unnecessary. The final assembly does not require
`lem-pod-verdier-composition-mate-normalization`: chosenComparison already constructs
its isomorphism from Mathlib conjugation and right-adjoint uniqueness. No adopted
source declaration, module or proof is removed. No module is withdrawn or claimed
pruned from the whole targets closure. All old direct proof_deps except
`det-sp-unique-right-adjoint` move to the actual construction/naturality steps or
are superseded by the explicit ordinary-map proof. Old tool_uses entries for
lem-pur-integral-operations-preserve-constructible,
lem-sf-integral-compact-support-constructible, fix-prop-adjunctions,
cor-coef-verdier-weil-equivariance,
lem-pod-frobenius-pullback-monoidal-adjunction-coherence,
lem-pod-verdier-composition-mate-normalization,
lem-pod-derived-automorphism-hom-evaluation,
fix-prop-projection-formula and lem-fix-weil-operations are removed from the item;
its two subclaims record the tools needed by their own arguments.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The listed existing tools do not themselves state
Nonempty Data with the three full Hom lifts and normalized constant, compositor and
projection for this supplied W, nor the first-variable naturality square for an arbitrary
normalized Data. In particular common_comparisons_coherent supplies an existential
coherent lift, whereas this theorem quantifies over the supplied W. The construction
step must use the normalization fields to compare that W, rather than replace it.
The original plan's naturality step needs evaluation normalization and projection
normalization to identify its first-variable square on the supplied presentations.

Searches used LeanSearch, Loogle, project/Mathlib rg, and whole-blueprint searches for
chosen duality and transpose naturality. Mathlib supplies generic adjunction naturality
and evaluation tools; no exact normalized sheaf/Frobenius package was found. Existing
PodHomChain target-variable and finite-Tor presentation lemmas do not have these types.

Edge cases for the new subclaims: zero M gives the same canonical transpose square;
empty X introduces no nonempty-object assumption; f=id retains the actual supplied
normalizations; changing a chosen right-adjunction normalization does not affect the
data or transpose-naturality statements. Naturality quantifies over every target pair,
so it does not impose a special choice of dualizing object. Every Data supplies the
closed-adjunction evaluations and carrier maps; no arbitrary closed presentation is
assumed natural without those normalizations. The unit's realized lists are empty;
no unit statement or prescribed unit step is bypassed.

## New nodes

`def-sf-weil-chosen-exchange-data` owns only the existing relocated interfaces and
states no existence theorem. All names, types and definition bodies are unchanged.

`lem-sf-weil-chosen-exchange-construction` is the construction/domain part of original
DAG Steps 1, 4 and 5, including the specified compact-support compositor from Step 3.
Its conclusion omits all exchange laws and choices of structure adjunctions. Its
module/docstring and node give the normalization and permitted-domain argument.

`lem-sf-weil-chosen-transpose-naturality` is original DAG Step 6, a single naturality
square for the exact three transposes, at any supplied target pair. Its docstring
writes the evaluation dinaturality, inverse projection square and three successive
uses of adjunction naturality. It neither constructs Data nor substitutes the chosen
comparison; the latter is proved in the item.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
