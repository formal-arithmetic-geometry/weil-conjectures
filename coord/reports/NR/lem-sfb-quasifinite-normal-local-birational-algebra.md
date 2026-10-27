## Worker report

The module `Sheaf.RingTheory.QuasiFiniteNormalLocalBirationalAlgebra` states
`Localization.bijective_localRingHom_of_isQuasiFiniteAtPrime_of_isIntegrallyClosed`.
Its only proof is `by sorry`. No new notion, dependency repair, or statement correction
is necessary. All writes are in the assigned sandbox; compilation uses scompile.py.

Clause-by-clause rendering:

- The commutative integral domains A and C are `A : Type u`, `C : Type v`,
  `[CommRing A] [IsDomain A] [CommRing C] [IsDomain C]`.
- Their inclusion is `algebraMap A C` from `[Algebra A C]`. Injectivity follows
  from the injective fraction-field embeddings and the scalar-tower equality:
  equality of images in C implies equality in K and hence in A. No additional
  injectivity hypothesis is needed.
- The common fraction field is `K : Type w`, `[Field K]`, `[Algebra A K]`,
  `[Algebra C K]`, `[IsFractionRing A K]`, `[IsFractionRing C K]`.
  `[IsScalarTower A C K]` says the inclusion commutes with these embeddings;
  therefore its extension to the common fraction field is the identity.
  Each of the three carrier universes is explicitly and independently bound.
- Finite type is `[Algebra.FiniteType A C]`. This is exactly the finite-type
  notion in the dependency: `RingHom.FiniteType` is defined by this class for
  the induced algebra, and `RingHom.finiteType_algebraMap` explicitly states
  the equivalence for `algebraMap A C`. Both declarations were read in
  `Mathlib.RingTheory.FiniteType`; no private replacement is introduced.
- The prime ideal q is bundled as `(q : PrimeSpectrum C)`; its underlying ideal
  and primeness are `q.asIdeal` and `q.isPrime`. Its contraction p is the
  canonical term `(q.comap (algebraMap A C)).asIdeal`, rather than another
  arbitrary prime plus an equality assumption.
- Quasi-finiteness at this prime is precisely
  `(hq : Algebra.IsQuasiFiniteAtPrime A C q)`, using the dependency's recorded
  open-singleton-in-the-fibre definition. No global quasi-finiteness is assumed.
- Integral closedness of A_p is
  `[IsIntegrallyClosed (Localization.AtPrime (q.comap (algebraMap A C)).asIdeal)]`.
  A_p is a domain automatically because A is a domain and p is prime.
  The intrinsic fraction-field formulation is equivalent to integral closedness
  in the specified K: K remains the fraction field after localization at p,
  and `isIntegrallyClosed_iff` identifies the intrinsic and chosen-field forms.
  An algebra structure of A_p on K is thus derivable, not an added hypothesis.
- The conclusion is `Function.Bijective` of
  `Localization.localRingHom (q.comap (algebraMap A C)).asIdeal q.asIdeal
  (algebraMap A C) rfl`. Its source is the stipulated A_p and its target is C_q.
  This is the canonical induced local ring homomorphism (its definition and
  `localRingHom_to_map` were read), so bijectivity asserts that this specified
  map is an isomorphism. It does not merely posit some unrelated ring equivalence.
- Both localizations are Mathlib's `Localization.AtPrime`, defined as localization
  at the indicated ideal's `primeCompl`, exactly the complements in the node.

Dependency declarations and imports:

- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType`, its underlying `Algebra.FiniteType`, and the bridge
  `RingHom.finiteType_algebraMap`.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`:
  `WeilConjectures.RingTheory.QuasiFiniteAtPrime`, `Algebra.IsQuasiFiniteAtPrime`.
- `def-weil-pbc-normal-ring`:
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`;
  domain normality uses the already available domain instance.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`;
  this module also supplies the actual `Localization.localRingHom`.
- The common-fraction-field data use `IsFractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing`.
- The additional proof dependencies are plain imports:
  `WeilConjectures.RingTheory.QuasiFiniteAtFiniteSubalgebraAway`
  (`Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime`),
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`
  (`Algebra.IsIntegral.of_finite`), and
  `Mathlib.GroupTheory.MonoidLocalization.Away` (`Localization.Away`).
  Their recorded signatures and relevant source were read. Statement dependencies
  are public imports. The docstring reproduces all five proof steps, including
  the denominator arguments in the node.

Source checked: `literature/stacks-project/varieties.tex`,
`lemma-modification-normal-iso-over-codimension-1`, Tag 0BFP, especially proof (4):
normality identifies the finite intermediate birational algebra with the base
local ring, and localization gives equality of the local rings. The node's
pointwise finite-subalgebra proof supplies this without a Noetherian assumption.

Edge cases checked before writing: q = (0) gives the common fraction field on
both sides; A a field forces the finite-type birational C to be the same field;
A = C gives the identity map on the localization. Zero rings are excluded by the
explicit integral-domain assumptions, exactly as in the node. There is no
assumption that A itself is normal, Noetherian, or local; normality is required
only for A_p. There is no restriction on characteristic or on the dimensions.
Compatibility of embeddings is essential: omitting the scalar tower would allow
the two chosen embeddings into K to describe a different fraction-field map.

Searches on 2026-10-24:

- `msearch.py ... leanfinder`: query "A finite type inclusion of domains with a
  common fraction field quasi finite at a prime induces an isomorphism on local
  rings if the base local ring is integrally closed". Eight hits, including
  `Algebra.QuasiFinite.of_isIntegral_of_finiteType`, `Algebra.QuasiFiniteAt`,
  `Algebra.ZariskisMainProperty.of_isIntegral`, and locality of integral closure.
  None identifies the specified two local rings.
- `msearch.py ... loogle`: `Algebra.QuasiFiniteAt, IsIntegrallyClosed`.
  Zero hits.
- `msearch.py ... leansearch`: query "A birational finite type map of integral
  domains that is quasi finite at q induces an isomorphism of local rings if the
  base localization is integrally closed". Eight hits: Zariski main property,
  quasi-finite permanence, and finite residue fields. No exact match.
- `msearch.py ... grep`:
  `QuasiFiniteAt.*[Ii]ntegrallyClosed|[Ii]ntegrallyClosed.*QuasiFinite|[Bb]irational`
  in `RingTheory`. Two hits, both in `ZariskisMainTheorem.lean`, concerning the
  private strongly-transcendental lemma. Its full signature and docstring were
  read; it does not assert this node.
- `rg` in `lean/WeilConjectures/RingTheory`, `lean/Sheaf/RingTheory`, and
  `dag/lean_names_upstream.json` for birational terminology, quasi-finite-at-prime
  declarations, and the proposed declaration name found no existing statement
  of the result. `rg` for the exact node id in `lean/WeilConjectures` and
  `lean/Sheaf` found no matches. The generic-localization and dimension-one local
  overring modules concern different hypotheses and conclusions.
  `FiniteNormalCoverFamily.lean` was also inspected: its private principal-open
  integrally-closedness lemma does not assert the present quasi-finite local result.

Validation: scompile.py NR lem-sfb-quasifinite-normal-local-birational-algebra
compiled both sandbox and final module forms successfully (1.1 seconds each).
`set_option autoImplicit false` checks that every variable is explicitly bound.
No diagnostic commands remain, no definitions contain sorry, and no node fault
or disputed statement was found.

## Second reading by NR

A separate in-thread reading reopened the node and the final module and checked
all clauses above. The assignment prohibits starting another agent, so this is
an additional reading by the same worker, not an independent worker review;
the maintainer's independent review remains required.

The domain instances match both integral-domain hypotheses. The two fraction-ring
instances and scalar tower jointly express the compatible common fraction field,
and imply injectivity of the algebra map. Algebra.FiniteType is the algebra-map
specialization of the recorded RingHom.FiniteType. The bundled q supplies precisely
a prime ideal, its comap supplies precisely p, and hq uses the exact recorded
pointwise quasi-finite definition. Normality concerns A_p alone. The conclusion
is bijectivity of the canonical localRingHom between the required prime-complement
localizations. No hypothesis or conclusion was added or omitted, and no code
change was needed after this reading. The node copy changes only its lean field.
