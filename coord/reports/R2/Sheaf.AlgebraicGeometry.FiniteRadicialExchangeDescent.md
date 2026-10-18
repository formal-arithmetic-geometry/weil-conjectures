## What changed

Proved `AlgebraicGeometry.Etale.finite_radicial_exchange_descent`, with exactly its original
signature and both conclusions, in `Sheaf.AlgebraicGeometry.FiniteRadicialExchangeDescent`.
No definition or other existing declaration was changed. Added seven proved private helpers:
bounded-constructibility comparison, canonical cover exchange, reflection of finite stalks,
reflection of finite local constancy, actual immersed realizations of locally closed subsets,
reflection of constructibility, and reflection of bounded constructibility.

The boundedness argument works on arbitrary schemes. It constructs image strata using the
vanishing-ideal subscheme and open restriction, compares their pullbacks with the old strata
using immersion independence, and descends local constancy and finite stalks. Exact inverse
image then reflects the same cohomological interval. For the Noetherian exchange conclusion,
reuse the source library's finite-radicial test-property descent theorem after proving its
upstairs test-boundedness hypothesis from the supplied global boundedness and exchange.
The single-complex/pullback comparison transports the coefficient object exactly; the
canonical `derivedBaseChangeMap` remains the map in the conclusion.

Updated the node's proof, proof dependencies and proof origin to this route. Added one node
attaching the already existing source-library test-property theorem; added no Lean module.
Removed unused proof imports. All five original public imports are unchanged.

Validation: the complete proof compiled without errors or warnings through `lcompile.py`,
including after import pruning. The delivery dry run also passed compilation and all
preflight checks (review class CODEX: adds nodes; changes a node file). Edge cases checked in the construction: empty schemes and
zero strata require no chosen point unless a geometric point is given; zero modules and the
zero coefficient ring use the same finite-generation/isomorphism arguments; interval endpoints
are preserved, with min/max used only when translating independently supplied bounds. Neither
S nor S' is assumed Noetherian; only the source test-property predicate quantifies over
Noetherian tests.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.finite_radicial_exchange_descent`
(node `lem-fin-radicial-exchange-descent`).

No `sorry` remains in the delivered Lean file. Added 0 holes and split off 0 new theorems.
The seven private helpers are all proved. This is a proof from existing declarations,
not a claim that the target's transitive axiom closure is already sorry-free.

In particular the proof uses the pre-existing `sorry` in
`AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective`
(`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne`, newly attached node
`lem-fin-radicial-noetherian-test-descent`), and the pre-existing `sorry` in
`CategoryTheory.isIso_mateEquiv_of_isEquivalence_of_fullyFaithful`
(node `lem-weil-mate-iso-along-equivalences`). Neither declaration is changed or newly stated
by this delivery. The source descent predicate gives boundedness on Noetherian tests only;
the parent theorem's separate global boundedness conclusion is proved here.

## No longer needed

Removed these direct proof imports:

- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`

The parent node no longer directly uses these old proof dependencies:

- `thm-weil-pbc-universal-homeomorphism-invariance`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-exact-functor-derived-functor`
- `def-weil-pbc-etale-constructible-sheaf`
- `lemma-weil-pbc-universal-homeomorphism-site-equivalence`
- `lemma-constructible-pullback-constant`
- `lem-weil-pbc-reduction-universal-homeomorphism`
- `lem-trf-finite-radicial-basechange`
- `def-weil-finite-integral-morphism`
- `lem-weil-pbc-finite-type-over-noetherian`
- `def-kun-unbounded-exchange`
- `lem-weil-pbc-cartesian-square-pasting`
- `lem-fin-module-exchange-composite-base-change`

The expanded exact-derived-factorization construction is replaced by the existing derived
inverse-image API. The explicit reduction-stratum comparison is replaced by pullbacks and
immersion independence. The noetherian pullback and canonical-pasting argument is encapsulated
by the existing source test-property descent theorem; those facts remain dependencies of its
new attachment node and are not claimed globally unnecessary. The unused module
`Sheaf.AlgebraicGeometry.ModuleExchangeCompositeBaseChange` is not imported by this proof;
its node remains part of the source descent theorem's mathematical proof plan.

Deleted obsolete parent `tool_uses` approvals (remaining approvals retain their original order):

- `thm-weil-pbc-universal-homeomorphism-invariance`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-exact-functor-derived-functor`
- `def-weil-pbc-etale-constructible-sheaf`
- `lemma-weil-pbc-universal-homeomorphism-site-equivalence`
- `lemma-constructible-pullback-constant`
- `def-weil-finite-integral-morphism`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-reduction-universal-homeomorphism`
- `lem-trf-finite-radicial-basechange`
- `def-kun-unbounded-exchange`
- `lem-weil-pbc-cartesian-square-pasting`

No Lean module is withdrawn: pruning here concerns parent dependencies and direct imports,
not a claim that every removed module is unreachable from all other targets.

## Where the brief, the DAG or earlier work was wrong

The assigned node did not record the source library's existing
`HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective`. Its docstring cites this
same blueprint label, but its actual predicate is different: it only asserts boundedness on
Noetherian tests, so applying it alone cannot supply the assigned theorem's global boundedness
when the base is non-Noetherian. This delivery proves that missing global part independently
and attaches the precise test-only statement as a separate node. No hypothesis or conclusion
of the assigned theorem is changed.

The original node also records `Sheaf.AlgebraicGeometry.ModuleExchangeCompositeBaseChange`,
but that module's source file is absent from this machine's shared checkout. This did not
block the shorter route through the existing source test-property declaration.

The plan's comparison of reduced induced strata is unnecessary: the proved
`IsFiniteLocallyConstantSheaf.upperStar_of_range_subset` works directly on the pullback
stratum with the same underlying image. This avoids both reduction and choosing any
unspecified object from an unproved existence theorem.

A read-only traversal also found the pre-existing DAG cycle
`lem-weil-pbc-derived-exchange-termwise` →
`lem-weil-pbc-derived-exchange-bounded-comparison` →
`lemma-weil-pbc-derived-exchange-replacement` →
`lem-weil-pbc-derived-exchange-termwise`. The identical cycle is reachable from the original
assigned node before this delivery; no new Lean import cycle is introduced. This is reported
for the maintainer rather than changing unrelated nodes.

## New nodes

`lem-fin-radicial-noetherian-test-descent` attaches the existing declaration
`AlgebraicGeometry.Etale.HasConstructibleDirectImageBaseChangeOn.of_isFinite_of_surjective`
in `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne`. Its source is the Noetherian
test/exchange portion of the assigned blueprint proof. It states no global boundedness on Y;
its only conclusion is the boundedness-and-canonical-exchange property on Noetherian tests.
The Lean theorem already exists with `sorry`, so this attachment adds no theorem or hole.
The node supplies the complete proof in words, exact existing Lean attachment and the three
required kinds of Mathlib search. No definition/statement change record is required.

The new node uses an `existing: true` source attachment (branch `slopmaster2`), so its Lean
record has no delivered-file field, as required by the attachment format.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
