## Worker report

Group Q159, item `lem-trf-henselization-quasi-finite-ring`, stage 2.

The module `Sheaf.TraceFormula.HenselizationQuasiFiniteRing` states
`Algebra.henselization_quasiFinite_ring` with `sorry` as its only proof.  The node
copy changes only its `lean` record.  No statement correction, disputed statement,
dependency repair, or new node was needed.

Source read: Stacks Project `literature/stacks-project/algebra.tex`, Tag 05WP,
“Lemma quasi-finite-henselization” (lines 43580--43615).  The repository review had
corrected the old 05WR citation to 05WP; 05WR is the strict-henselization lemma.
The formal statement uses independent universes for the source and target rings and
for the two henselization rings.  The canonical algebra structure
`Localization.AtPrime.algebraOfLiesOver p q.asIdeal` is represented by the standard
Mathlib typeclass pair `[Algebra (Localization.AtPrime p)
(Localization.AtPrime q.asIdeal)]` and
`[Localization.AtPrime.IsLiesOverAlgebra p q.asIdeal]`; the latter pins the supplied
structure to the canonical localization map and adds no mathematical assumption.

### Hypotheses and conclusions, clause by clause

- `A : Type u` and `B : Type v` are commutative rings with `[Algebra A B]` and
  `[Algebra.FiniteType A B]`, rendering the finite-type ring map in the node.
- `p : Ideal A` has `[p.IsPrime]`; `q : PrimeSpectrum B` is the target prime and
  `[q.asIdeal.LiesOver p]` is exactly the assertion that its contraction is `p`.
- `hq : Algebra.IsQuasiFiniteAtPrime A B q` is the recorded
  `def-weil-pbc-ring-map-quasi-finite-at-prime` notion at `q`.
- `H` is a commutative ring with an algebra over `Localization.AtPrime p`, a
  `HenselianLocalRing` structure, and
  `hH : Algebra.IsHenselizationAtPrime' A p H`.  This is the ordinary henselization
  `A_p^h`; the primed dependency is the universe-polymorphic recorded interface.
- `K` is a commutative ring with an algebra over
  `Localization.AtPrime q.asIdeal`, a `HenselianLocalRing` structure, and
  `hK : Algebra.IsHenselizationAtPrime' B q.asIdeal K`, representing `B_q^h`.
- The two localization typeclass binders identify the natural `A_p`-algebra on `B_q`
  (from `Localization.AtPrime.algebraOfLiesOver`), so the tensor product below is
  precisely `A_p^h ⊗_{A_p} B_q`.
- The conclusion first supplies a ring hom `h : H →+* K`.  `IsLocalHom h` renders
  locality, and the displayed equality says that `h` is the canonical map over the
  original `A → B` after both localizations.
- `@Module.Finite H K _ _ h.toModule` says this canonical map is finite, with the
  module structure induced by `h`.
- The next existential supplies a prime `n` of
  `TensorProduct (Localization.AtPrime p) H (Localization.AtPrime q.asIdeal)` and a
  ring equivalence `e : K ≃+* Localization.AtPrime n`.
- The first contraction equality says `n` lies over the maximal ideal of the source
  henselization `H`; the second says its contraction to `B_q` is the maximal ideal
  corresponding to `q`.  Thus `n` is the prime selected by the quasi-finite residue
  evaluation, rather than an arbitrary tensor-product prime.
- The final two universal equations make `e` compatible with the two tensor factors:
  on `H` it agrees with `h`, and on `B_q` it agrees with the structural map to `K`.
  These equations express the canonical localization identification in the node.

No extra characteristic, noetherian, domain, nonzero, or finite-residue-field
hypothesis is present.  Prime ideals may be maximal or non-maximal; the statement
also allows arbitrary (independent) universes `u`, `v`, `w`, and `z` and does not
exclude zero rings except where the prime-instance hypotheses themselves rule them
out.

### Recorded dependencies and interfaces used

- `def-weil-pbc-ring-map-quasi-finite-at-prime`: import
  `WeilConjectures.RingTheory.QuasiFiniteAtPrime`, declaration
  `Algebra.IsQuasiFiniteAtPrime`.
- `def-weil-pbc-localization-at-prime`: import
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, declarations
  `Localization.AtPrime`, `Ideal.ResidueField`, and `Ideal.Fiber` (the statement
  uses `Localization.AtPrime`; the canonical `localRingHom`/`algebraOfLiesOver`
  interface is also from this Mathlib file).
- `def-weil-pbc-henselization-at-prime`: import
  `Sheaf.RingTheory.GeneralizedHenselizationAtPrime`, declaration
  `Algebra.IsHenselizationAtPrime'`.
- Stated proof-dependency modules imported for the stage-3 plan are
  `Sheaf.TraceFormula.HenselizationPrimeIndEtale`,
  `Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition`,
  `WeilConjectures.RingTheory.FiniteLocalHenselian`,
  `Sheaf.RingTheory.IndEtaleStability`,
  `Sheaf.RingTheory.MapIntoHenselianColimit`, and
  `Sheaf.RingTheory.QuasiFiniteFourRings`.  The Mathlib leaf
  `lem-weil-pbc-etale-algebra-finite-presentation-localization` is represented by
  `Algebra.Etale.finitePresentation` and the principal-localization etale instance,
  so it has no project module to import.

### Edge cases checked

The formal type keeps `p` and `q` as arbitrary prime ideals, so non-maximal primes
and their localizations are retained.  The two henselization rings are allowed to
have different universes from each other and from `A` and `B`.  The tensor prime is
an existential `n` with an explicit `n.IsPrime` witness; no choice of a prime is
silently made and no empty-index or positive-degree assumption is introduced.  The
identity-map case `A = B`, `p = q`, and the finite-map case were checked against the
same canonical localization interfaces.

### Searches made

- `msearch.py ... leanfinder "ordinary henselization under quasi-finite local ring map"`:
  returned `HenselianLocalRing`, `Algebra.QuasiFiniteAt`, and localization/quasi-finite
  declarations, but no ordinary henselization comparison theorem.
- `msearch.py ... loogle "HenselianLocalRing, IsLocalization, Module.Finite"`:
  zero hits.
- `msearch.py ... grep "henselization.*quasi-finite|quasi-finite.*henselization" RingTheory`:
  zero hits.
- `rg -n "henselization.*quasi-finite|quasi-finite.*henselization|henselization_quasiFinite"`
  over `WeilConjectures/` and the project `lean/Sheaf/`: found only the strict
  henselization analogue, the quotient consumer, and explanatory references; no
  ordinary comparison declaration.
- The dependency declarations and full docstrings were read in
  `Sheaf/RingTheory/GeneralizedHenselizationAtPrime.lean`,
  `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`, and
  `WeilConjectures/RingTheory/QuasiFiniteAtPrime.lean` (the latter through its
  recorded upstream module path).

## Second reading by Q159

I reread the DAG statement, Tag 05WP, the generalized henselization dependency, and
the complete Lean signature.  The finite-type, lying-over, and quasi-finite hypotheses
are all present.  The two henselization structures use the universe-polymorphic
interface, and the canonical localized algebra structure is pinned by
`IsLiesOverAlgebra`.  The conclusion contains the canonical local map, its finite
module property, the prime selected by both maximal-ideal contractions, and the two
factor-compatibility equations for the localization equivalence.  No hypothesis or
clause of the node was dropped, and no extra ring-theoretic assumption was added.
The initial local elaboration issue was only an ambiguous `algebraMap` target and was
resolved by explicit source and target types; there is no statement correction.
