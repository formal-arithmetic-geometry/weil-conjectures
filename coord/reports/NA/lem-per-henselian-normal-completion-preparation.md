## Worker report

The module states `AlgebraicGeometry.henselian_normal_completion_preparation` with
one `sorry`, and defines no new notions. The node statement and its existing
statement/proof dependencies are unchanged. The declaration docstring reproduces
all thirteen proof steps with their named dependencies. No statement correction,
new node, dependency repair, or disputed statement is needed.

Hypothesis and clause correspondence:

- The reduced quasi-excellent Noetherian local ring `(R,m)` is `R : Type u` with
  `CommRing R`, `IsLocalRing R`, `IsNoetherianRing R`, `_root_.IsReduced R`, and
  `hR : IsQuasiExcellent R`; `m` is `IsLocalRing.maximalIdeal R`.
- The ordinary henselization is `H : Type v`, its `CommRing` and
  `HenselianLocalRing` structures, and
  `hH : Algebra.IsHenselizationAtPrime' R (IsLocalRing.maximalIdeal R) H`.
  The algebra structures over R and its maximal-ideal localization, and the
  `IsScalarTower`, express the same canonical R-map: R localized at its maximal
  ideal is R itself. They specify compatibility, rather than another hypothesis
  on the henselization. The recorded predicate requires the henselian structure
  as input. Henselianity is also explicitly present in the conclusion.
- The properties of H are `_root_.IsReduced H`, `IsNoetherianRing H`,
  `IsExcellent H`, `HenselianLocalRing H`, and
  `ringKrullDim H = ringKrullDim R`.
- The finite list of factors is `r : ℕ`, indexed by `ULift.{v} (Fin r)`;
  `B : ULift.{v} (Fin r) → CommRingCat.{v}` provides actual commutative rings,
  `f : ∀ a, H →+* B a` their structural maps, and the existential
  `∀ a, HenselianLocalRing (B a)` their henselian local structures. For each a,
  `IsDomain`, `IsIntegrallyClosed`, `IsNoetherianRing`, and `IsExcellent`
  express every specified property of B_a. In particular normality means
  integral closure in the fraction field, not just reducedness.
- This is the canonical componentwise normalization, rather than a freely
  chosen finite cover: `e : (Spec (.of H)).reducedNormalization ≅ ∐ ...`,
  together with `e.hom ≫ Sigma.desc ... = (Spec (.of H)).fromReducedNormalization`,
  identifies the disjoint union over Spec H with the recorded normalization.
- Its product presentation is an isomorphism `eprod` from the same coproduct
  to `Spec (.of (Π a, B a))`, whose hom is precisely `sigmaSpec B`.
  Thus the displayed product and normalization use the same factors and maps.
- Finiteness as a module is `(RingHom.pi f).Finite`, and finiteness and
  surjectivity of the coproduct map are `IsFinite (Sigma.desc ...)` and
  `Surjective (Sigma.desc ...)`. For the finite index set, finiteness of the
  product module is equivalent to finiteness of each factor module.
- The dense open is `∃ U : (Spec (.of H)).Opens, Dense (U : Set ...) ∧ ...`.
  Its containment of every generic point is
  `∀ p : PrimeSpectrum H, p.asIdeal ∈ minimalPrimes H → p ∈ U`.
  Its isomorphism clause is `IsIso (Sigma.desc ... ∣_ U)`.
- The bound on every factor is `ringKrullDim (B a) ≤ ringKrullDim H`.
  No equidimensionality or equality of component dimensions is assumed.
- The independently quantified `∀ (B : Type w) [CommRing B] [IsLocalRing B]
  [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B], IsExcellent B → ...`
  states the normal-completion assertion for *any* normal excellent Noetherian
  local domain. There is no henselian input on this B. The result lists
  `IsDomain`, `IsIntegrallyClosed`, `IsNoetherianRing`, and `IsLocalRing` on
  `AdicCompletion (IsLocalRing.maximalIdeal B) B`, and
  `Module.FaithfullyFlat B (AdicCompletion ... B)` for its canonical algebra map.
- Every nowhere dense closed Z is quantified as `Z : Set (PrimeSpectrum R)`
  with `IsClosed Z → IsNowhereDense Z → ...`. The three conclusions use
  `IsNowhereDense` of preimages under `PrimeSpectrum.comap`, respectively for
  R→H, R→H→B_a, and R→H→B_a→AdicCompletion (maximalIdeal B_a) B_a.
  These are the canonical composite ring maps. Their continuity makes these
  inverse images closed as well. The assertion ranges over every Z and every a.

Recorded dependency declarations used:

- `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`:
  `Algebra.IsHenselizationAtPrime'` (full local-map universal property, read
  together with `Sheaf.RingTheory.HenselizationAtPrime`).
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, `IsExcellent`, including
  their `IsGRing`, regular-locus and universal-catenarity definitions.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` is the
  recorded scheme notion; for the rings R and H the same reducedness notion is
  its underlying `_root_.IsReduced` predicate, as the affine equivalence states.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded terminology
  includes Mathlib's `HenselianLocalRing`; strict henselianity is not assumed.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`:
  `AlgebraicGeometry.Scheme.reducedNormalization` and `fromReducedNormalization`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion`,
  the compatible quotient sequences with their canonical ring/algebra structures.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` in `WithBot ℕ∞`.
- Mathlib's `IsDomain`, `IsIntegrallyClosed`, `RingHom.Finite`, `IsFinite`,
  `Surjective`, `sigmaSpec`, `IsNowhereDense` and `Module.FaithfullyFlat` provide
  the standard clauses without private redefinitions.

Every proof-dependency module with a recorded declaration or a Mathlib file is
imported (plain imports for proof-only modules). The currently unstated
`lem-per-ratliff-formal-catenarity` and
`lem-per-excellent-normalization-preparation` have no module to import. They
are proof dependencies only; no missing notion is needed to write this statement.

Edge cases checked before writing: local rings are nonzero, so no zero-ring
counterexample to the finite domain decomposition is included. No positivity
restriction on r is added; the normalization isomorphism itself excludes an
empty family for nonempty Spec H. The field / dimension-zero case has one field
factor, trivial maximal-ideal completion, and only the empty nowhere dense
closed subset. For several minimal primes the components may have different
dimensions, and only the required upper bounds are stated. Empty Z is allowed;
a closed subset containing a generic point fails the nowhere-dense premise.
R and H have independent universes u and v, with the recorded henselization
predicate testing rings in `Type (max u v)`; factors lie in H's universe and
use a lifted finite index so coproducts exist at that universe. The independent
completion variable B has its own universe w. Arbitrary characteristic is allowed.

Sources read: Travaux de Gabber, I Corollary 6.3(ii), Proposition 6.2, Theorem 8.1
and the following henselization paragraph; III Proposition 6.2's normalization,
completion and rare-closed-set reductions. These confirm that quasi-excellence
suffices for the henselization to be excellent, without assuming universal
catenarity of R. Also read Stacks `more-algebra.tex`,
`lemma-henselization-reduced` (06DH), `lemma-henselization-dimension` (06LK), and
`lemma-completion-normal-local-ring` (0C23).

Searches for an existing complete statement:

- `msearch.py leanfinder`: `Reduced quasi excellent local ring henselization
  excellent finite normalization normal local completion` returned eight
  results, mainly `HenselianLocalRing`, its TFAE, field henselianity and reduced
  normalization. None states the preparation theorem.
- `msearch.py loogle`: `HenselianLocalRing, IsIntegrallyClosed` returned zero hits.
- `msearch.py grep`: `hensel.*normal|normal.*completion` in `RingTheory`
  returned zero hits.
- `msearch.py leansearch`: `The henselization of a reduced quasi excellent local
  ring is excellent and its normalization has normal completions` returned eight
  henselian-local-ring results, including its TFAE and constructors, with no
  exact statement.
- `rg` over `WeilConjectures` and `Sheaf` for
  `henselian.normal.completion|hensel.*[Nn]ormali|normal.*completion`
  found specialized curve-branch and normalization-localization results,
  including `PuncturedCurveBranches`, `SeparableNormalizationLocalEmbeddings`,
  and `HenselianNormalizationLocalization`, but no full statement. Read the
  related local-embedding and affine-normalization signatures for reuse.
- `grep -rn lem-per-henselian-normal-completion-preparation WeilConjectures`
  found no upstream declaration. A name-clash search for
  `henselian_normal_completion_preparation|henselianNormalCompletionPreparation`
  over the upstream-name index and both library roots returned no hits.

Validation: the full module compiled cleanly through `scompile.py` against the
live published build. Delivery preflight and its compile are run with
`deliver2.py --no-push` before pushing. Only the theorem proof is postponed;
there are no new definitions or unnamed postponed proofs.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
