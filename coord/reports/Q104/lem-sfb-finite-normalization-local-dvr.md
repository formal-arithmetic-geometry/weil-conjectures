## Worker report

The delivery states `integralClosure.finite_normalization_local_dvr` in
`Sheaf.RingTheory.FiniteNormalizationLocalDvr`. Its sole theorem has proof `sorry`;
there are no new definitions, additional nodes, dependency repairs, or statement
corrections. Only the item's `lean` record changes.

I read the complete item, all seven statement-dependency statements and their
recorded declarations, all seven proof-dependency statements and available
interfaces, and Stacks `algebra.tex`, Tags 00PH (`lemma-exists-dvr`, especially
lines 29330–29337) and 09IG (`lemma-integral-closure-Dedekind`, lines 29754–29774).
The source gives arbitrary finite field extensions without requiring separability
or normality of the base. No `Module.Finite D C` is asserted: normalization is
Noetherian here, but need not be finite as a D-module.

Hypotheses, one by one:

- `D : Type u`, `[CommRing D]`, `[IsNoetherianRing D]` give the commutative
  Noetherian base; `[IsDomain D]` includes nontriviality and absence of zero divisors.
- `[IsLocalRing D]` supplies the unique maximal ideal, written everywhere as
  `IsLocalRing.maximalIdeal D`. `hm` is exactly its required nonzero condition.
- `hdim : ringKrullDim D = 1` gives dimension exactly one, not merely at most one.
- `K : Type v`, `L : Type w`, `[Field K]`, `[Field L]`, and `[Algebra K L]`
  give the fields and inclusion K into L. A field algebra map is injective.
- `[Algebra D K]` and `[IsFractionRing D K]` give the inclusion of D into its
  given fraction field K; the latter includes injectivity and fraction
  representations with nonzero denominators.
- `[Algebra D L]` and `[IsScalarTower D K L]` identify the given map D into L
  with the composite D into K into L. This is compatibility of the stated
  inclusions, not an extra mathematical assumption.
- `[FiniteDimensional K L]` is `[L:K] < infinity`. There is no separability class.
- `C : Subalgebra D L`, `hC : C = integralClosure D L` represent the specified
  integral closure with its actual inclusion into L. C is not an arbitrary
  overring and no substitute closure is defined. Using this equality rather than
  repeating `integralClosure D L` makes the prescribed maps readable.
- `u`, `v`, `w` are independently declared universes; none are identified.

Conclusions, clause by clause:

- `IsNoetherianRing C ∧ IsDomain C ∧ IsIntegrallyClosed C ∧ ringKrullDim C = 1`
  is precisely the Noetherian normal dimension-one domain assertion. The
  `IsDomain` conjunct is explicit even though it is already inherited from C's
  inclusion in the field L.
- `IsFractionRing C L` uses the existing subalgebra inclusion, so L is the
  fraction field of this particular embedded C.
- The existential `q : PrimeSpectrum C` gives a prime ideal `q.asIdeal` with
  `q.asIdeal.comap (algebraMap D C) = IsLocalRing.maximalIdeal D`. This is
  exactly lying over the maximal ideal, and does not assume a chosen branch.
- The following universal quantifier ranges over every `q : PrimeSpectrum C`
  satisfying that same contraction identity. It concludes both
  `q.asIdeal ≠ ⊥` and `q.asIdeal.IsMaximal`.
- For every such q, `e : Localization.AtPrime q.asIdeal →ₐ[C] L` is the map
  of the actual prime localization into the specified field. It is required
  to be injective and to send every `IsLocalization.mk' ... c s` to
  `(c : L) / ((s : C) : L)`, for `s : q.asIdeal.primeCompl`. This is the
  canonical map, completely characterized on every fraction, not an arbitrary
  embedding or an unspecified choice of a nonempty type. Also, its C-algebra
  homomorphism type already requires it to extend the given inclusion C into L.
  The denominator is nonzero since zero belongs to every prime ideal.
- The biconditional `x ∈ e.range ↔ ∃ c s : C, s ∉ q.asIdeal ∧
  x = (c : L) / (s : L)` specifies the exact image subring requested by the node.
  There is no unspecified localization image or enlarged valuation overring.
- `∀ d : D, algebraMap D L d ∈ e.range` says that image contains the given D.
- `IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)` records the DVR
  structure on the abstract localization as well. Its fraction field is L for
  the very same map e, expressed by
  `@IsFractionRing (Localization.AtPrime q.asIdeal) _ L _ e.toRingHom.toAlgebra`.
  The underscores infer only the already fixed ring structures; the algebra
  structure is explicitly the one induced by e.
- On the abstract localization, the next three equalities are, respectively,
  `m_A = q.map (algebraMap C A)`,
  `m_A.comap (algebraMap C A) = q`, and
  `m_A.comap ((algebraMap C A).comp (algebraMap D C)) = m_D`.
- The existential `h : IsDiscreteValuationRing e.range` records the requested
  DVR structure on the embedded image itself. `IsFractionRing e.range L` uses
  the actual subtype inclusion of this subalgebra into L. The final three
  equalities give its maximal ideal as q extended to the image, and its
  contractions to C and to D as q and m_D. Here
  `@IsLocalRing.maximalIdeal e.range _ h.toIsLocalRing` makes the local-ring
  structure explicit. Thus both realizations of A have all ideal identities;
  injectivity identifies the localization with its image, so the additional
  displayed realization adds no mathematical strength.

Statement dependencies used, with the declarations read:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (196–197), whose ideals are the submodules of R over itself.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim` (26–31), dimension of the prime spectrum ordered by inclusion.
- `def-weil-field`: `Mathlib.Algebra.Field.Defs`, `Field` (169–180).
- `def-weil-pbc-integral-closure`: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure` (215–222); also read `IsIntegral` in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs` (50–54).
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed` (69–74); the node's recorded domain form is the explicit
  conjunction `IsDomain C ∧ IsIntegrallyClosed C` used here.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime` (55–58),
  the local-ring instance and `Localization.AtPrime.map_eq_maximalIdeal`
  (209–215). The unused residue-field and fibre-ring clauses of that general
  dependency are not needed by this item.
- `def-sc-discrete-valuation-ring`: `Mathlib.RingTheory.DiscreteValuationRing.Basic`,
  `IsDiscreteValuationRing` (56–60), a nonfield local PID with `[IsDomain]`.
  This retains the nonfield condition, rather than allowing field valuations.

Proof-dependency imports are plain imports as required for the future proof:
`WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`
(`AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`);
`Mathlib.RingTheory.Localization.Integral`
(`integralClosure.isFractionRing_of_finite_extension`);
`Mathlib.RingTheory.Spectrum.Prime.Topology`
(`RingHom.IsIntegral.comap_surjective`);
`Mathlib.RingTheory.DedekindDomain.Dvr`
(`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`);
and `Mathlib.RingTheory.Localization.LocalizationLocalization`
(`IsFractionRing.isFractionRing_of_isLocalization`). The normal-localization
lemma `isIntegrallyClosed_of_isLocalization` is in the public normal-ring
module already imported. The last two proof dependencies use the already-public
prime-localization module, including `Localization.AtPrime.under_maximalIdeal`.
The theorem docstring gives all four steps and the precise dependency nodes.

Searches actually run on 2026-10-24:

- `msearch.py ... leanfinder "The integral closure of a one dimensional
  Noetherian local domain in a finite field extension has DVR localizations over
  the maximal ideal, canonically embedded in the extension as fractions"`:
  8 hits, including `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`
  and `IsDiscreteValuationRing.TFAE`. They start with a Dedekind ring or an
  already-local DVR criterion; none states the entire node.
- `msearch.py ... loogle "integralClosure, IsDiscreteValuationRing"`: 0 hits.
- `msearch.py ... grep "integralClosure|isDiscreteValuationRing|IsFractionRing"
  RingTheory/DedekindDomain`: 25 hits, mostly fraction-field facts and the
  Dedekind normalization file. Reading that file (45–93, with the subsequent
  hypotheses) confirms its normalization API assumes a Dedekind base and uses
  separability for its Noetherian conclusion; these assumptions cannot be
  inserted here. The general upstream normalization theorem supplies that step.
- `msearch.py ... leansearch "The integral closure of a dimension one Noetherian
  local domain in a finite extension of its fraction field has discrete valuation
  localizations dominating the base"`: 8 hits. The integral-closure normality
  theorem covers only one clause, and the Dedekind candidates do not state the
  complete construction with the given inclusions and ideal contractions.
- `rg -n 'finite.normalization|finiteNormalization|normalization.*Dvr|lem-sfb-finite-normalization-local-dvr'
  lean/WeilConjectures lean/Sheaf dag/lean_names_upstream.json`, and the required
  `grep -rn 'lem-sfb-finite-normalization-local-dvr' lean/WeilConjectures`:
  no existing declaration for this node (the id search is empty). Further
  `rg` for `integralClosure.*local|local.*integralClosure|normalization.*local`
  in the RingTheory directories found specialization results, semilocal
  normalization, and local compositum diagrams. Those impose different
  hypotheses or omit this node's map/image/contraction assertions.
- Mathlib source searches for `mapToFractionRing`, `IsFractionRing`, localization
  lifts, and prime-localization contractions identified the standard canonical
  map and its range facts in `Localization/AsSubring.lean`. I read that complete
  file. The statement uses the standard `AlgHom`, localization, fraction formula
  and algebra-hom range; it defines no second map or subring notion.
- `rg -n 'finite_normalization_local_dvr'` in both project roots and Mathlib
  returned no declaration-name collision.

Edge cases checked before writing:

- The zero ring is excluded exactly by the node's domain/nonzero assumptions;
  the field case is excluded by both dimension one and the explicitly stated
  nonzero maximal ideal. No extra exclusion is introduced.
- The identity finite extension L = K is allowed, including the nonnormal base
  `k[t^2,t^3]_(t^2,t^3)`. Its normalization has the expected DVR localization;
  there is no assumption that D itself is normal or a DVR.
- Purely inseparable `F_p[t]_(t)` with L obtained by adjoining `t^(1/p)` is
  allowed. No separability or characteristic restriction occurs in the type.
- Ramified extensions, and extensions with more than one prime over m_D, are
  allowed: the existential obtains a prime and the universal assertion covers
  every prime above m_D, without uniqueness or henselianity.
- If the numerator is zero or the denominator is one, the image formula still
  has its usual meaning. A zero denominator cannot occur outside q.
- The map D into the image is the given inclusion into L: the C-algebra
  homomorphism condition and `IsScalarTower D K L` ensure compatibility. Both
  contraction composites use `algebraMap D C`, not an unrelated D-algebra action.
- Independently sized D, K and L are retained. Although the imported upstream
  proof lemma has some universes equal in its interface, that does not restrict
  this statement; a future proof can transport the rings to compatible sizes.

Validation: the initial module compiled successfully by `scompile.py` against
both the sandbox and its library module name on the server, with no errors or
warnings. After removing one unused import, the required delivery dry run and
final delivery compile the final file again. The node signature is extracted
verbatim from the final module. No `STATEMENT-DISPUTED` or node fault was found.

## Second reading by Q104

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
