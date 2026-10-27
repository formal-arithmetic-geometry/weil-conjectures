## Worker report

The module `Sheaf.RingTheory.NagataNormalizationDVRBranches` states
`nagata_normalization_dvr_branches`, with `sorry` as its entire proof. It introduces
no definitions, new DAG nodes, dependency replacements, or statement corrections.
The existing node changes only in `lean`.

Source read: Stacks `literature/stacks-project/varieties.tex`,
`lemma-pre-delta-invariant` (Tag 0C3S) and
`lemma-normalization-same-after-completion` (Tag 0C3V), together with the node's
seven-step algebra proof. The first source gives finite normalization of a reduced
one-dimensional local Nagata ring; the second uses its normal local branches.
This item spells out their component normalization and DVR input, with no
completion assertion. Its proof is carried step by step in the theorem docstring.

Hypothesis and clause correspondence:

- The ring A is `(A : Type u) [CommRing A]`. Locality and reducedness are
  `[IsLocalRing A] [IsReduced A]`; the maximal ideal is the canonical
  `IsLocalRing.maximalIdeal A`. Nagata is `(hA : IsNagataRing A)`, and dimension
  exactly one is `(hdim : ringKrullDim A = 1)`. No separately assumed
  Noetherianity, domain hypothesis on A, completeness, or residue characteristic
  restriction is added.
- The total ring of fractions is `FractionRing A`, Mathlib's localization at
  `nonZeroDivisors A`, valid for a reduced ring with several components as well
  as a domain. The normalization B is exactly
  `integralClosure A (FractionRing A)`.
- The finite enumeration of all distinct minimal primes is
  `t : ℕ` and `p : Fin t ≃ {p : PrimeSpectrum A // p.asIdeal ∈ minimalPrimes A}`.
  The equivalence gives both completeness and absence of repetitions.
- The domain quotient D_i is literally `A ⧸ (p i).val.asIdeal`, and K_i is
  literally `Localization.AtPrime (p i).val.asIdeal`. The conclusion lists
  `IsDomain`, `IsNoetherianRing`, `IsLocalRing`, `IsNagataRing`, and
  `ringKrullDim ... = 1` for each quotient.
- `f i : D_i →+* K_i` satisfies
  `(f i).comp (Ideal.Quotient.mk ...) = algebraMap A K_i`, specifying the
  canonical quotient-induced homomorphism. The quotient map is surjective, so
  this equation uniquely determines f_i. The conclusion `IsField K_i` and
  `@IsFractionRing D_i _ K_i _ (f i).toAlgebra` identify K_i as its fraction
  field via this very map, rather than through an unspecified embedding.
- `E i` is a subalgebra of K_i over D_i using `(f i).toAlgebra`, with the
  explicit equality to `@integralClosure D_i K_i _ _ (f i).toAlgebra`.
  This existential naming merely binds that exact subalgebra; it is not a new
  normalization definition or an arbitrary choice of a normal ring.
- Each E_i has `Module.Finite D_i (E i)`, `IsDomain (E i)`,
  `IsNoetherianRing (E i)`, `IsIntegrallyClosed (E i)`, and
  `ringKrullDim (E i) = 1`. These spell out exactly the node's dimension-one
  Dedekind definition; Mathlib's dimension-at-most-one convention is not used
  to omit the dimension-one assertion.
- `eQ : FractionRing A ≃ₐ[A] (∀ i, K_i)` is the canonical product decomposition:
  its A-algebra compatibility forces each coordinate to extend the localization
  map from A, hence determines it on total fractions. The restricted ring
  equivalence is `eB : B ≃+* (∀ i, E i)`, with the coordinate equation
  `(eB b i : K_i) = eQ b.val i`. This requires the actual restriction of eQ,
  not just an abstract ring isomorphism. `Module.Finite A B` is also explicit.
- A branch is `q : PrimeSpectrum B` with
  `q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A`.
  `∃! z : Σ i : Fin t, PrimeSpectrum (E i), ...` states the unique factor and
  unique prime in that factor. Its first conjunct says q is the inverse image
  of this prime under the projection `(Pi.evalRingHom ... z.1).comp eB.toRingHom`.
- The component prime has `z.2.asIdeal.IsMaximal` and `z.2.asIdeal ≠ ⊥`.
  Its contraction along `algebraMap D_i E_i` equals
  `(IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p_i)`, precisely m/p_i.
- The localization equivalence is
  `e : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime z.2.asIdeal`.
  Its displayed ring-hom equation says it extends the same product projection
  on B. This is the canonical fraction localization isomorphism: agreement on
  B fixes the extension on localized fractions.
- Finally `∃ hq : IsDomain (Localization.AtPrime q.asIdeal),
  @IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) _ hq` states both
  the domain structure and Mathlib's DVR property for every B_q in question.
  The explicit proof argument is necessary because the possibly reducible B
  itself is not assumed to be a domain.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.NagataRing`: `IsNagataRing`, the conjunction of
  Noetherianity and N-2 for every prime quotient. Its recorded dependency
  module `WeilConjectures.RingTheory.JapaneseDomain`, declarations `IsN2` and
  `IsN1`, was also read; these declarations are at the root namespace.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` in `WithBot ℕ∞`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`;
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`: `IsIntegral`;
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  the integral-closedness condition in `FractionRing`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing` and
  `IsFractionRing`. I also read `Ideal.ResidueField` and its fraction-ring
  instance in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, but retained
  the node's actual prime localizations instead of replacing them by residue
  fields.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`;
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
  All seven statement-dependency notions use the recorded declarations.
- Proof dependencies are imported from
  `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`
  (`minimalPrimes.finite_of_isNoetherianRing`),
  `Mathlib.RingTheory.Noetherian.Basic`
  (`isNoetherianRing_of_surjective`, `IsNoetherianRing.of_finite`),
  `WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions`
  (`reduced_noetherian_total_ring_fractions`),
  `Mathlib.RingTheory.Localization.Integral`
  (`integralClosure.isFractionRing_of_finite_extension`),
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`
  (`integralClosure.isIntegrallyClosedOfFiniteExtension`),
  `WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp`
  (`ringKrullDim_eq_of_isIntegral`),
  `Mathlib.RingTheory.Ideal.GoingUp`
  (`Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'`), and
  `Mathlib.RingTheory.DedekindDomain.Dvr`
  (`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`).
  `IsN2`/`IsN1` and integral-closure definitions are already publicly imported
  through the statement dependencies. No proof import is omitted for a cycle.

Edge cases checked: a DVR gives one component; the local nodal ring can have
several minimal primes and a reducible total fraction ring; an irreducible
singularity can have several maximal ideals in its single normalization factor.
The sigma of component primes handles both distinctions. Fields and the zero ring
are excluded by dimension exactly one, not by an added hypothesis. No positive
t assertion is required: the full enumeration and hypotheses already prevent an
empty minimal-prime set. The arbitrary universe u is retained, and every index,
ring variable, and proof binder is explicit. The DVR predicate excludes fields
via its nonzero-maximal-ideal condition. No node fault or disputed statement was
found.

Searches for an existing full statement:

- `msearch.py ... leanfinder` with query "Integral closure of reduced Nagata
  local ring finite product Dedekind normalization discrete valuation branches"
  returned eight hits including `IsDedekindDomainDvr`,
  `IsDedekindDomain.isDedekindDomainDvr`,
  `IsIntegralClosure.isDedekindDomain`, and
  `integralClosure.isDedekindDomain`. These require an already Dedekind domain
  or describe its DVR localizations; none gives the reduced Nagata product and
  its canonical branch assertions.
- `msearch.py ... loogle "IsDedekindDomain, integralClosure"` returned
  `integralClosure.isDedekindDomain` and
  `integralClosure.isDedekindDomain_fractionRing`. Their full signatures require
  an already Dedekind base and a finite separable field extension; neither
  states this result for a reduced Nagata curve ring.
- `msearch.py ... grep` with pattern
  `(Nagata|IsNagata).*([Nn]ormal|[Dd]edekind)|([Nn]ormal|[Dd]edekind).*(Nagata|IsNagata)`
  returned one historical attribution in `NoetherNormalization.lean`, no match.
- `rg` on the project's `lean/WeilConjectures` and `lean/Sheaf` found
  `IsNagataRing.finite_integralClosure_quotient` and the private
  `finite_reduced_nagata_normalization` in
  `WeilConjectures/RingTheory/IsN1OfIsAnalyticallyUnramified.lean`.
  The former only gives component finiteness; the latter only gives total
  finiteness. Neither is the full decomposition/branch theorem. Complete-DVR
  finite normalization also has different hypotheses and conclusion.
- Searching the item id in `lean/WeilConjectures` returned no attachment.
  Searching `nagata_normalization_dvr_branches` in Mathlib, both project roots,
  and `dag/lean_names_upstream.json` returned no name collision.

Validation: the initial module compiled in both sandbox and library module modes
through `scompile.py`, with no errors or warnings (35.3 s and 33.2 s). The final
file adds explicit public imports of the recorded Noetherian, module-finiteness,
and integral-closure definition modules; final compilation is repeated by the
prescribed delivery preflight. All Lean lines have at most 100 characters.

## Second reading by Q70

On a separate pass I reread the full node statement beside the Lean signature.
The ring hypotheses, exact dimension, exhaustive distinct indexing, both actual
quotient/localization carriers, finite component normalizations, dimension-one
Dedekind clauses, canonical ambient and restricted product equivalences, total
module finiteness, unique factor and nonzero maximal prime over m/p_i, commuting
localization equivalence, and final DVR clause are all present. In particular,
I checked that `IsDomain A` is not assumed, that E_i is not assumed local, and
that uniqueness applies to the pair of component index and prime rather than
only to a prime after selecting a component. I checked the parenthesization:
B_q is a DVR for every q over m, outside the unique-component existential.
The equations for f, eQ/eB, and e ensure canonical maps rather than arbitrary
isomorphisms. No mismatch requiring a statement change was found. This is the
author's second pass; the maintainer supplies the independent review described
in the assignment.
