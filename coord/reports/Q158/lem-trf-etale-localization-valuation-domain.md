## Worker report

The module `Sheaf.RingTheory.EtaleLocalizationValuationDomain` states
`AlgebraicGeometry.etale_localization_valuation_domain` with proof `sorry`.
It introduces no definition and changes the node only in `lean`.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 0ASJ,
`lemma-etale-extension-valuation-ring`, statement and first proof paragraph
(lines 37479 onward). The node isolates the valuation-domain and inclusion/locality
assertions; it does not request the subsequent weakly-unramified assertion.

Hypothesis and clause correspondence:

- A is a valuation domain: `(A : Type u) [CommRing A] [IsDomain A]
  [ValuationRing A]`. Mathlib's valuation-ring class takes the domain instance
  explicitly; its `TFAE` identifies its divisibility definition with the
  fraction-field condition in def-trf-valuation-ring. Its local-ring instance
  supplies `IsLocalRing.maximalIdeal A` without an extra hypothesis.
- B is a commutative A-algebra: `(B : Type u) [CommRing B] [Algebra A B]`.
  These rings share the ambient universe of the scheme category; `u` is arbitrary.
- The affine spectrum map is etale: `hEtale : Etale (Spec.map
  (CommRingCat.ofHom (algebraMap A B)))`. This uses the actual scheme property
  from def-weil-etale-morphism, without assuming a conversion to ring etaleness.
- q is prime: `(q : Ideal B) [q.IsPrime]`. No maximality of q is imposed.
- Its inverse image is the maximal ideal of A: `hq : Ideal.comap
  (algebraMap A B) q = IsLocalRing.maximalIdeal A`.
- The natural map is injective: `Function.Injective
  (algebraMap A (Localization.AtPrime q))`. This is the canonical algebra map
  through B to its canonical prime localization, not a chosen ring homomorphism.
- The natural map is local in the node's explicit sense: `Ideal.comap
  (algebraMap A (Localization.AtPrime q))
  (IsLocalRing.maximalIdeal (Localization.AtPrime q)) = IsLocalRing.maximalIdeal A`.
  The target maximal ideal is q B_q by Mathlib's
  `IsLocalization.AtPrime.map_eq_maximalIdeal`.
- B_q is a valuation domain: `∃ h : IsDomain (Localization.AtPrime q),
  @ValuationRing (Localization.AtPrime q) _ h`. The dependent proposition
  asserts the domain structure rather than presupposing it. The explicit
  instance argument allows Mathlib's existing valuation-domain notion to be used.
- No henselian, Noetherian, rank or module-finiteness hypothesis occurs.

Statement dependencies used, with declarations and docstrings read:

- def-trf-valuation-ring: `Mathlib.RingTheory.Valuation.ValuationRing`,
  `ValuationRing` (lines 62--64), `ValuationRing.TFAE` (lines 407--416), and
  `ValuationRing.isLocalRing` (line 267). The node is a Mathlib leaf with no
  `lean` record, so its `mathlib_match` is used directly.
- def-weil-etale-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` (affine-local ring-map etaleness, lines 39--46).
- def-weil-pbc-localization-at-prime:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`
  (lines 55--58), its local-ring instance (lines 107--108), and
  `IsLocalization.AtPrime.map_eq_maximalIdeal` (lines 524--526).
  The residue-field and fibre clauses of this dependency are not needed here.

The available proof dependencies are plain imports:
`Sheaf.AlgebraicGeometry.EtaleComparison`
(`AlgebraicGeometry.etale_indEtale_weaklyEtale_comparison`),
`Sheaf.RingTheory.IndEtaleUniverseTransport`
(the recorded ind-etale interface, publicly importing the weak-etale notion), and
`Sheaf.RingTheory.WeaklyEtaleTor`
(`ModuleCat.weaklyEtale_flatResolutionBound`). The two proof-only nodes
lem-trf-flat-localized-field-descent and
lem-trf-weak-dimension-one-valuation-criterion currently have no recorded Lean
module, so there is no module to import for them; neither is needed to type this
statement. All four DAG proof steps are included in the theorem docstring.

Edge cases checked mathematically before writing:

- A may be a field, so its maximal ideal may be zero; no nonzero-ideal or
  positive-rank assumption excludes this case. Etale localization over a field
  gives a field and hence a valuation domain.
- B may be a product or otherwise fail to be a domain. Only B_q is asserted to
  be a domain; the statement does not assume `[IsDomain B]`.
- B cannot be the zero ring when a prime q is supplied. This follows from the
  meaning of prime ideal rather than an additional nontriviality binder.
- The identity algebra with q the maximal ideal recovers the usual local-ring
  localization isomorphism.
- Arbitrary-rank and non-Noetherian valuation domains remain admitted; no
  finite-generation or discreteness class is present.

Searches actually run on 2026-10-24:

- msearch.py leanfinder: "An etale algebra over a valuation domain localized at
  a prime over the maximal ideal is a valuation domain". Eight hits include
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`,
  `ValuationSubring.ofPrimeAlgebra`, `Algebra.IsEtaleAt`, and ring-map etale
  localization-span lemmas. None is this theorem; the DVR result has stronger
  base hypotheses.
- msearch.py loogle: `ValuationRing, Algebra.Etale`. Zero hits.
- msearch.py grep: `etale.*[Vv]aluation|[Vv]aluation.*[Ee]tale`. Zero hits.
- msearch.py leansearch: "An etale algebra over a valuation domain localized at
  a prime above the maximal ideal is a valuation domain". Eight hits about
  etale localizations and the definition of etaleness, not this result.
- rg of both project roots for the item id and etale/valuation combinations:
  no matching declaration. The discrete-valuation stalk theorem in
  `WeilConjectures/AlgebraicGeometry/Sites/DivisorMap.lean` concerns codimension-one
  stalks in a regular scheme. Other hits include valued-curve proofs and
  `Sheaf/RingTheory/ValuationValueGroupTorsion.lean`, which states the distinct
  power-times-unit conclusion for algebraic valued-field extensions.
- rg of `dag/lean_names_upstream.json` for the item id and proposed declaration:
  no match.

No statement correction, new node, dependency repair, or disputed statement.

Validation: scompile.py compiled this file in sandbox mode and at its intended
library module path, with the default 60-second limit. Both checks exited
successfully without diagnostics. Auto-implicit binders are disabled and the
maximum Lean line width is 90.

## Second reading by Q158

A second pass over the unchanged node and the completed Lean file checked the
three conclusions separately. In particular, using a valuation-ring predicate
alone would require a domain instance prematurely; the dependent existential
correctly puts the domain assertion in the conclusion. The localness clause is
the specified contraction equality, not merely preservation of nonunits in one
direction. The hypothesis is on the canonical affine scheme map, and the map in
both conclusions is the canonical composite A to B to B_q. The contraction
hypothesis uses the original algebra map A to B, so the two maps are not confused.
No hypothesis or conclusion was added or removed. No changes were needed in
this pass. This is the dispatcher's single-worker check; the maintainer's
independent review is performed after delivery, as required by the task brief.
