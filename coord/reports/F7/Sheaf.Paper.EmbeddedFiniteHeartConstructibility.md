## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteHeartConstructibility`
in `Sheaf.Paper.EmbeddedFiniteHeartConstructibility`, with its statement unchanged.
The only added declarations are proved private helpers: invertibility of the actual
point scalar map, an explicit continuous-ring universe-lift isomorphism, and their
composite with its monoid-homomorphism and invertibility instances.

The proof transports constant models along that coefficient isomorphism, uses the
existing normalized finite-discrete encoding comparison, and compares the resulting
fixed module sheaf with the specified heart realization after forgetting to sets.
The already proved finite-scalar-action transfer gives constructibility in both
directions. The existing intrinsic restriction theorem finishes the argument.

Proof-only imports expose existing private general helpers from
`EmbeddedFiniteHeartRealization`, `FiniteDiscreteEncodingConstructibility`,
`IntegralConstantModelHeartClosure`, and `IntegralModelsGenerators` using `import all`.
The existing public import is retained. Additional proof-only imports supply intrinsic
restriction, its constructibility comparison, and the Noetherian qcqs instances.
The DAG proof now records the actual argument and these dependencies.

The extra cross-unit tools are already proved generic comparison helpers: normalized
finite-discrete encoding, constant-ring realization/restriction, and the generic
coefficient-isomorphism helpers in the integral heart closure module. They supplement
the original encoding route without bypassing an integral-models unit step. The last
module's integral Serre theorem is not used.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteHeartConstructibility`
(node `lem-sfb-embedded-finite-heart-constructibility`), the item's sole original hole.
Added: none. Remaining in this module: none. Split off: zero.
All private helpers are proved. No definition or existing public statement changes.

## No longer needed

No original import was removed. No module is withdrawn.
The original proof dependency `def-weil-proetale-constructible-sheaf` need not be a
separate proof step: its predicate is handled by the existing theorem
`proEtaleModuleRestriction_constructible_iff`; the statement dependency is retained.
The remaining original proof dependencies are used. No finite-field presentation,
monoidal structure, derived comparison, or etale-origin theorem is proved anew.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and unit route are unchanged. The previous report already
identified that Tag 03ET concerns flatness of sheafification; the finite constant-function
isomorphism here is proved directly by local bijectivity, rather than attributed to
that tag. The original public declaration docstring is retained. The DAG's proposed direct
scalar-action identification is unnecessary: the proved finite-action transfer lemma
compares constructibility using an isomorphism of underlying sheaves of sets.
Its finiteness hypotheses hold on both sides. The Type-0 versus scheme-universe
continuous coefficient rings require an explicit ULift postcomposition isomorphism.
The cover universes also differ: ordinaryLocalModel uses a Type-u index whereas
IsFiniteLocallyConstant uses Type-(u+1). Mathlib's smallness theorem for the
quasi-compact precoverage supplies the required subcover, including empty covers.
Positive strata on an empty scheme are already handled by the intrinsic restriction
constructibility theorem. No new nodes or statement/definition repairs are needed.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
