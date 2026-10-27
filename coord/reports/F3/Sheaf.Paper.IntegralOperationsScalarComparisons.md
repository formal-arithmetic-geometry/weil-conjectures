## What changed

Reduced `WeilConjectures.scalarOperationsOrdinary_tower` to explicit chain-level
coherence. The pullback and completed-tensor comparisons descend from their
normalized representative squares using the new, proved
`CategoryTheory.functorSquareTowerDescent`. Its proof uses faithful restriction,
naturality and cancellation of representative isomorphisms. The closed tensor
comparison descends in the same way from its ordinary pure-tensor chain model;
the existing `CategoryTheory.scalarBaseChangeHom_tower` then proves the Hom
component with the required inverse transport in the first variable.

All existing public signatures, definitions, normalization predicates and public
imports of the assigned module are preserved. The new imports are proof imports.
The main node's tower proof step now records the actual descent argument. Two
new, fully proved representative modules isolate the scalar factorization and
chain-square calculations. Two further proved modules apply localization descent
to comparison isomorphisms supplied with their normalization equations; the
assigned file supplies its existing comparisons and normalization proofs.
A further proved module isolates the localized ordinary tensor chain-square
calculation. These proof extractions address the per-file compile limit. Their
private scalar functors and square components are imported only for the proof;
their public equations state exactly the representative tower equations. The pre-existing normalized
pullback existence proof also uses an extracted, proved good-representative chain
comparison with its full component characterization. Its chosen data is determined
by all hom components; its statement and the final normalization are unchanged.
The full pullback localization proof is also extracted, without a hole, to
`NormalizedIntegralScalarPullbackComparison`; the original existence theorem
applies that lemma with exactly the same normalization predicate.

## Proved and sorry left

The original module had one direct hole, `WeilConjectures.scalarOperationsOrdinary_tower`.
It is reduced by a complete proof to strictly lower chain equations. This is a
decomposition, not a claim that its transitive axioms are already closed.

The new formal descent theorem `CategoryTheory.functorSquareTowerDescent` is proved.
`WeilConjectures.integralScalarPullbackGoodComparison` is proved from the existing
chain naturality and quasi-isomorphism declarations; it adds no hole.
`WeilConjectures.normalizedIntegralScalarPullbackComparison` is the completely
proved extraction of the original pullback existence and uniqueness proof.
The representative equations
`WeilConjectures.integralScalarPullbackTowerOnRepresentatives` and
`WeilConjectures.integralScalarTensorTowerOnRepresentatives` are proved from the
chain equations and the exact-derived scalar composition formula.
`WeilConjectures.integralScalarPullbackNormalizedTower` and
`WeilConjectures.integralScalarTensorNormalizedTower` are proved conditional
descent lemmas: their comparison maps and normalization equations are parameters,
which the assigned module instantiates with its existing definitions.
`WeilConjectures.integralScalarOrdinaryTensorTowerOnRepresentatives` is also proved:
it takes the three chain comparisons and their chain tower equation as parameters,
and derives the localized square using scalar factor composition. The assigned
module supplies its existing comparisons and the proved ordinary chain tower.
`WeilConjectures.integralScalarOrdinaryTensorChainTower` is proved by the composite
scalar adjunction, explicit unit-section normalization, pure tensor generation and
the ordinary scalar associator normalization. Its module compiled cleanly in 16.1 s.

The lower statements currently left with `sorry` are:

- `WeilConjectures.integralScalarPullbackChainTower`
  (`lem-pur-integral-scalar-pullback-chain-tower`).
- `WeilConjectures.integralScalarTensorChainTower`
  (`lem-pur-integral-scalar-tensor-chain-tower`).

The delivery adds two named lower holes and closes the original direct hole by
decomposition. Every delivered Lean module has compiled through `lcompile.py`.
The final assembled module compiled in 55.3 seconds; the extracted full pullback
normalization proof compiled in 16.4 seconds. No profiling options, increased
limits, or relaxed transparency settings are left in the packet. The delivery
command performs the required final compilation and preflight checks.

## No longer needed

No existing public import or declaration is removed. No existing module is
withdrawn. The new descent helper needs only the functor/whiskering API; its
statement and proof need no localization import. The ordinary-chain module also
drops an unnecessary public import of the finite/Roos models; its statement needs
only the normalized ordinary tensor chain and scalar-composition modules.

The tower argument uses the existing formal evaluation-transpose Hom lemma rather
than constructing a new Hom comparison. It does not require a new finite-free Hom
inversion argument: the assigned module's already proved inversion theorem and
its dependencies are preserved.

The direct proof dependency `lem-pur-finite-free-completion-exchange-coherence`
(`Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence`) is no longer
needed for this ordinary tower theorem. No global withdrawal is claimed.
`lem-sfb-scalar-hom-tensor-coherence` is no longer invoked as a complete coherence
package by the assigned module; its already proved private tensor-generation
helpers are still used in the new ordinary chain proof. The descent lemma only needs families of square components,
so the new representative modules do not rebuild natural transformations or import their
separate chain naturality lemmas. The representative square equations need no
`IntegralScalarTensorGoodIso` import. These existing comparison and naturality
modules remain used by the assigned module's original normalized comparisons;
no global withdrawal is claimed. The assigned module
now imports `NormalizedIntegralScalarPullbackComparison` in place of the direct
`IntegralScalarPullbackChainProperties` proof import; the latter is still needed
inside the proved extraction. The direct
`FunctorSquareRepresentativeDescent` import is also confined to that extraction.
Its direct import of the tensor representative helper is
also unnecessary because the proved normalized-tower module supplies that proof.

The older three component-clause nodes are not imported or used: their recorded
Lean declarations are absent in the current source, and the new reduction works
below those derived component equalities, on explicit chain maps.

## Where the brief, the DAG or earlier work was wrong

The three existing `...-pullback-clause`, `...-tensor-clause` and `...-hom-clause`
node records point at declarations absent from the current assigned module.
Their records are preserved; they are not treated as usable lemmas or as
authorization to withdraw mathematics.

The latest blueprint moved `def-weil-derived-pullback-tensor-hom` to
`sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/`. The new nodes cite
the current coefficient-coherence proof and the inherited node's scalar tower
step, rather than the stale pathname. The unit's coefficient-compatibility route
and its existing targets are unchanged.

## New nodes

- `lem-pur-functor-square-tower-descent`: a fully proved categorical pasting and
  faithful-restriction lemma. Its conclusion follows formally from the three
  normalization squares and the two representative associator equations.
- `lem-pur-integral-scalar-pullback-chain-tower`: the strict pullback/Roos chain
  equation, before descent and without any completeness assumption.
- `lem-pur-integral-scalar-tensor-chain-tower`: the strict completed-tensor/Roos
  chain equation, before descent for arbitrary complex pairs.
- `lem-pur-integral-scalar-ordinary-tensor-chain-tower`: the ordinary total-tensor
  chain associativity equation, proved by the composite scalar adjunction and
  pure bidegree generators.
- `lem-pur-integral-scalar-pullback-tower-representatives`: the localized
  pullback square equation, proved by chain coherence, scalar-factor naturality
  and exact-derived scalar composition.
- `lem-pur-integral-scalar-tensor-tower-representatives`: the analogous proved
  tensor square equation. Its component family needs no separate naturality
  construction: the categorical descent lemma uses only its normalized equations.

- `lem-pur-integral-scalar-pullback-normalized-tower`: faithful descent of
  normalized pullback squares, proved for arbitrary comparison isomorphisms
  satisfying the existing normalization predicate.
- `lem-pur-integral-scalar-tensor-normalized-tower`: faithful product descent of
  normalized tensor squares, with the full component normalization as hypothesis.

- `lem-pur-integral-scalar-ordinary-tensor-tower-representatives`: the proved
  localized ordinary tensor square calculation, for arbitrary cochain pairs
  and chain comparisons satisfying their given tower equation.

- `lem-pur-integral-scalar-pullback-good-comparison`: the uniquely normalized
  natural isomorphism on good pullback chain representatives, proved from the
  existing chain properties and extracted from the original existence proof.

- `lem-pur-normalized-integral-scalar-pullback-comparison`: the original
  uniquely normalized derived pullback comparison, completely proved by
  representative localization in its own module.

The chain statements include zero complexes, identity coefficient maps and
unbounded complexes. Their associators have the same order `c * j(b)` as the
existing normalized scalar composition. No shared interface is changed, so there
is no interface change record or forced adaptation.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
