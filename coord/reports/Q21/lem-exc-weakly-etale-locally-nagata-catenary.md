## Worker report

The delivery states `RingHom.isUniversallyCatenary_and_locallyNagata_of_weaklyEtale`
in `Sheaf.RingTheory.LocallyNagataCatenaryOfWeaklyEtale`. Its sole proof is `sorry`.
The docstring includes all nine steps of the reviewed DAG proof, including the explicit
localization maps, polynomial reduction, prime-chain contraction argument, and quotient
argument. No definition, dependency interface, statement correction, or new node is needed.
The existing stage-1 split reviewed by N9 is preserved. That split did not provide a Lean
record; the previous worker's “item unchanged” failure was not completion of stage 2.
This delivery adds the missing Lean record and theorem.

Source read: Greco, *Two theorems on excellent rings* (1976), printed pp. 139 and
146–148: Foreword; Remark 5.2; Theorem 5.3(iii); Proposition 5.4; Lemma 5.5;
Remark 5.7(ii). The Cambridge PDF timed out; its text was read in the online copy
https://scispace.com/pdf/two-theorems-on-excellent-rings-2lc74dyy3w.pdf . The theorem
asserts preservation of both local Nagata properties and universal catenarity; the
Foreword supplies commutativity and Noetherianity. Remark 5.2 supplies the equivalence
of AF with flatness of the map and tensor multiplication. There is no source or node fault.

Every hypothesis and clause is rendered as follows:

- Arbitrary commutative rings `A`, `B`: `{A : Type u} {B : Type v}` with
  `[CommRing A] [CommRing B]`. Universes `u`, `v` are explicitly declared and independent.
- Both rings Noetherian: `[IsNoetherianRing A] [IsNoetherianRing B]`, precisely the
  recorded `IsNoetherianRing`; it means all ideals are finitely generated.
- The specified homomorphism: `(f : A →+* B)`.
- Weak etaleness of that same map: `(hf : f.WeaklyEtale)`. Upstream
  `RingHom.WeaklyEtale` uses `f.toAlgebra` and the recorded `Algebra.WeaklyEtale`;
  it is flatness over `A` plus flatness via tensor multiplication. It imposes no finite
  presentation, injectivity, locality, or faithful flatness condition.
- Every prime localization of `A` is Nagata:
  `(hA : ∀ (p : Ideal A) [p.IsPrime], IsNagataRing (Localization.AtPrime p))`.
  The prime is universally quantified, and the canonical fraction localization is used.
  The hypothesis concerns the localizations, without assuming `IsNagataRing A`.
- Universal catenarity of `A`: `(hcat : IsUniversallyCatenary A)` from the recorded
  excellent-ring definition module.
- First conclusion: `IsUniversallyCatenary B`.
- Second conclusion: `∀ (q : Ideal B) [q.IsPrime],
  IsNagataRing (Localization.AtPrime q)`. It is joined to the first by `∧`.
- The explanatory chain clause is inside the recorded `IsUniversallyCatenary`:
  for each finite type algebra, `IsCatenaryRing` quantifies over comparable primes,
  supplies one finite bound on all finite strict chain lengths in the interval, and
  equates lengths of every pair of saturated chains. `IsPrimeChain` includes prime
  membership, fixed endpoints, and strict consecutive inclusions;
  `IsSaturatedPrimeChain` forbids a prime strictly between consecutive members.
  No local bound or saturated-chain clause is lost. The predicate includes
  Noetherianity, already required independently by the node.

Recorded statement-dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, with `isNoetherianRing_iff_ideal_fg` identifying its ideal condition.
- `def-weil-pbc-ind-etale-algebra`: `Sheaf.RingTheory.IndPrincipalZariski` is publicly
  imported, using its reexported `Algebra.WeaklyEtale`. The ring-map wrapper
  `RingHom.WeaklyEtale` was read in
  `WeilConjectures.RingTheory.ProEtale.WeaklyEtale` at lines 237–246 and reduces exactly
  to that algebra predicate. The Mathlib class was read at
  `Mathlib/RingTheory/Etale/Weakly.lean:34–41`.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`, the
  localization at the prime complement. Declaration and docstring read at lines 55–58.
- `def-weil-pbc-nagata-ring`: `Sheaf.RingTheory.NagataRing`, `IsNagataRing`, namely
  Noetherian plus N-2 for every prime quotient. Full declaration and docstring read.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`,
  `IsUniversallyCatenary`, `IsCatenaryRing`, `IsPrimeChain`, `IsSaturatedPrimeChain`.
  All definitions and docstrings read locally and the current server source confirmed
  with `scompile.py --source Sheaf.RingTheory.ExcellentRing`.

The modules of all recorded, stated proof dependencies are also imported without
`public`: the finite-type, polynomial, dimension and localization Mathlib interfaces;
`Sheaf.RingTheory.JapaneseDomain`, `FiniteOverNagata`,
`LocalizationPrimeResidueFieldIso`, `NagataLocalization`, `PolynomialNagata`,
`WeaklyEtaleField`, and `WeilConjectures.Mathlib.RingTheory.Etale.Weakly`.
Base-change and composition are provided by `Mathlib.RingTheory.Etale.Weakly`.
The proof-only nodes `lem-exc-nagata-weakly-etale-ascent` and
`lem-exc-weakly-etale-local-component-dimension` have no Lean record on the inspected
base, so there is no module to import for them. Their statements are unnecessary to type
this theorem, and their proof roles remain in its full proof docstring and DAG record.

Edge cases checked before writing:

- The zero target ring has no prime ideals. Its local Nagata assertion is vacuous;
  every unital finite type algebra over it is the zero ring and its prime-chain
  conditions are vacuous. No `Nontrivial B` assumption is introduced.
- If the source is the zero ring, a unital map forces the target to be zero as well.
- The identity map recovers precisely the two given source properties.
- General localization maps, including non-faithful ones, are allowed. No hypothesis
  requires surjectivity on spectra.
- Equal endpoint primes allow exactly length zero strict chains. Empty spectra produce
  no endpoint pairs. The recorded definitions handle both cases directly.
- No characteristic, dimension, finite presentation, domain, or local-ring restriction
  is present. Independent `u` and `v` permit different source and target sizes.
  The recorded universally catenary predicate tests algebras in the ring's universe;
  finite type algebras admit polynomial quotient presentations in that universe.

Searches actually run for this delivery:

- `msearch.py leanfinder`, query “Locally Nagata and universally catenary Noetherian
  rings ascend along weakly etale ring maps”: eight hits about etale composition,
  locality, algebra conversion and descent of finite presentations; none states this
  ascent theorem.
- `msearch.py loogle`, query `IsUniversallyCatenary, IsNagataRing,
  Algebra.WeaklyEtale`: zero hits; service says `IsUniversallyCatenary` is unknown.
  This is a Mathlib-name search result, not evidence that the project lacks the notions.
- `msearch.py grep`, query `Catenary|catenary|Nagata|WeaklyEtale`, subdirectory
  `RingTheory`: six hits, namely a bibliographic credit to Nagata and Mathlib's existing
  weakly etale class and universe-lift lemma; no catenarity or Nagata ascent theorem.
- `rg` over the upstream `WeilConjectures` and project `lean/Sheaf` sources for catenarity,
  local Nagata and weak etale combinations found the recorded `ExcellentRing` definitions,
  related excellence statements, and a proof-docstring reference to this item;
  no declaration with this statement. Searching the item's literal ID in upstream
  `WeilConjectures` found no attachment. A further name search for
  `isUniversallyCatenary.*weaklyEtale|locallyNagata.*weaklyEtale|locally_nagata.*weakly`
  in both source trees found no existing theorem.

Validation: `scompile.py Q21 lem-exc-weakly-etale-locally-nagata-catenary`
compiled the single delivered module cleanly (no unexpected warnings). The required
`deliver2.py Q21 lem-exc-weakly-etale-locally-nagata-catenary --no-push` printed
`OK (dry run)`: compilation and preflight pass apart from the independent second
reading, which the second reader supplies. Only the item's `lean` field differs from
the inspected base; its recorded signature matches the module verbatim. No push made.

## Second reading by Q21

I opened the item node, the complete Lean module, every recorded statement dependency,
and Greco's source at Theorem 5.3(iii), Proposition 5.4, Lemma 5.5, and Remark 5.7(ii).
The item has no `statement_change`, and no new definition or dependency module is
needed.

The node-to-Lean comparison is itemized below.

- The source and target objects are arbitrary commutative rings `A` and `B`: Lean
  binds independent universes with `{A : Type u} {B : Type v}` and instances
  `[CommRing A] [CommRing B]`. Verdict: exact.
- The Noetherian hypotheses on both rings are `[IsNoetherianRing A]` and
  `[IsNoetherianRing B]`, the recorded Mathlib predicate. Verdict: exact; no stronger
  finiteness, domain, local, or characteristic assumption is added.
- The specified map is `(f : A →+* B)`. Verdict: exact.
- Weak etaleness is `(hf : f.WeaklyEtale)`. The opened upstream wrapper reduces via
  `f.toAlgebra` to `Algebra.WeaklyEtale`, whose two flatness fields are the weakly
  etale condition used in the node and Greco's Remark 5.2. Verdict: exact; no finite
  presentation, injectivity, faithful flatness, or locality is added.
- The local Nagata hypothesis is
  `(hA : ∀ (p : Ideal A) [p.IsPrime], IsNagataRing (Localization.AtPrime p))`.
  This quantifies every prime and uses the canonical prime-complement localization.
  Verdict: exact; it does not replace local Nagata by global Nagata.
- Universal catenarity is `(hcat : IsUniversallyCatenary A)`, using the recorded
  `Sheaf.RingTheory.ExcellentRing` declaration. Verdict: exact.
- The first conclusion is `IsUniversallyCatenary B`. Verdict: exact.
- The second conclusion is
  `∀ (q : Ideal B) [q.IsPrime], IsNagataRing (Localization.AtPrime q)`, joined
  with the first by `∧`. Verdict: exact; every target prime is included.
- The node's explanatory catenary clause is rendered by the dependency's
  `IsUniversallyCatenary`, `IsCatenaryRing`, `IsPrimeChain`, and
  `IsSaturatedPrimeChain`: finite bounds for all finite chains in every comparable
  prime interval and equal lengths for all saturated chains, with no intermediate
  prime between consecutive terms. Verdict: exact; no clause is dropped or added.

The source check agrees: Greco's Theorem 5.3(iii) assumes an AF map between
commutative Noetherian rings and says that local Nagata and universal catenarity of
the source ascend to the target; Remark 5.2 identifies AF with the weakly etale
flatness formulation used here. The Lean theorem has precisely the source's two
properties and the Foreword's Noetherian assumptions.

Edge cases were checked explicitly. For `B = 0`, the prime-localization conclusion
is vacuous and universal catenarity has no prime intervals; no `[Nontrivial B]` is
present. A unital map from `A = 0` forces `B = 0`. The identity map returns the two
source properties. Empty spectra and equal endpoint primes are covered by the
quantifiers and length-zero chains. No characteristic, dimension, finite
presentation, domain, or local-ring restriction occurs, and the independent `u` and
`v` preserve all universe cases.

I searched Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` with
LeanFinder/Loogle/grep and several alternate name queries (`catenary`, `Nagata`,
`WeaklyEtale`, and their combinations). The searches found only the existing
weakly-etale and defining predicates; no theorem with this ascent statement exists.
The dependency declarations were opened: `IsNoetherianRing`,
`RingHom.WeaklyEtale`, `Localization.AtPrime`, `IsNagataRing`, and the catenarity
predicates all match the node's notions. The three proof-only dependency nodes have
no recorded Lean declarations and are not statement dependencies, so no import or
repair is required.

No mismatch was found. I changed only the item's missing `lean` record, recording the
module and the verbatim theorem signature below; the Lean source itself required no
repair.
