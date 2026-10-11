## Worker report

The module `Sheaf.RingTheory.DimOneResidueFieldsFinite` states
`Ideal.dim_one_residue_fields_finite`, with its only proof `sorry`.
It renders all three conclusions of the node. No definitions or dependency modules
were added, and no node statement was corrected.

Source checked: [Stacks Tag 031F](https://stacks.math.columbia.edu/tag/031F),
Lemma 10.119.10, statement and proof. The local literature checkout does not contain
`literature/stacks-project/algebra.tex`, so the tag was opened on the Stacks website.
The node agrees with the source.

Hypotheses and clauses:

- Integral domains R and S: `[CommRing R] [IsDomain R]` and
  `[CommRing S] [IsDomain S]`; the map is `(φ : R →+* S)` and
  `(hφ : Function.Injective φ)`.
- Fraction fields K of R and L of S: `[Field K] [Algebra R K]
  [IsFractionRing R K]` and `[Field L] [Algebra S L] [IsFractionRing S L]`.
  The independent universes `uR uS uK uL` impose no size identification.
- The induced field extension K into L: `[Algebra K L]` together with
  `hcompat : ∀ r : R, algebraMap K L (algebraMap R K r) = algebraMap S L (φ r)`.
  This equation specifies that the chosen field map extends φ, rather than introducing
  an unrelated action. A field homomorphism is injective; the extension of φ to fractions
  exists uniquely for an injection of domains. Thus this is the data of the induced
  extension in the node, not an additional mathematical restriction.
- Finite degree: `[FiniteDimensional K L]`, i.e. `Module.Finite K L`, not a bound
  on `Module.finrank` (which would admit infinite-dimensional spaces by its zero convention).
- Noetherian local base: `[IsNoetherianRing R] [IsLocalRing R]`; the maximal ideal
  throughout is `IsLocalRing.maximalIdeal R`.
- Dimension exactly one: `hdim : ringKrullDim R = 1`.
- Clause (1): for every `n : PrimeSpectrum S`, contraction
  `n.asIdeal.comap φ = IsLocalRing.maximalIdeal R` implies `n.asIdeal.IsMaximal`.
  PrimeSpectrum bundles exactly an ideal and its primality proof, so every prime is covered.
- Clause (2): `Set.Finite {n : PrimeSpectrum S | n.asIdeal.comap φ =
  IsLocalRing.maximalIdeal R}`. Bundling the primality proof introduces no extra elements.
- Clause (3): for each n and contraction equality hn, the local algebra instance is
  `(Ideal.ResidueField.map (IsLocalRing.maximalIdeal R) n.asIdeal φ hn.symm).toAlgebra`.
  The conclusion is `FiniteDimensional (IsLocalRing.maximalIdeal R).ResidueField
  n.asIdeal.ResidueField` with exactly this induced map. Mathlib's residue field is
  the local-ring residue field of `Localization.AtPrime`, as specified by the dependency.
  At the maximal ideal of the local ring R it is canonically isomorphic to R/m.
  No arbitrary residue-field algebra structure is assumed.

Dependency declarations read and used:

- `def-pc-field-extension`: its mathlib_match is `Algebra`, in
  `Mathlib.Algebra.Algebra.Defs`; also `RingHom.toAlgebra` in that module. The field
  extension is expressed by Algebra and the residue map by RingHom.toAlgebra.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`. Its definition and ideal-finiteness equivalence
  were read; it means exactly the stated Noetherian condition.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic`, the supremum of strict prime chains.
- `def-weil-pbc-localization-at-prime`: the mathlib_match supplies
  `Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic` and
  `Ideal.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`.
  The latter is used, with `Ideal.ResidueField.map` from the same module. Both full
  signatures and docstrings were read. Its other clause `Ideal.Fiber` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber` was read but is not needed in the signature.
- Supporting Mathlib notions: `IsFractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing` and `FiniteDimensional` from
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.

Edge cases checked before writing: R or S cannot be zero by IsDomain. A field R has
Krull dimension zero and is excluded by the node's dimension-one hypothesis.
S may itself be the fraction field of R: then there are no primes above m, the finite
set is empty, and the universal conclusions are vacuous. Likewise the closed fibre
may be zero. No surjectivity onto Spec R, nonempty fibre, finite generation of S,
integrality of S over R, or Noetherian condition on S is imposed. Degree one is
allowed, as are arbitrary characteristics and infinite residue fields: the last
clause requires finite dimension, not finite cardinality. All binders and universes
are explicit; `autoImplicit` is disabled.

Searches for an existing statement (all msearch calls used group K1 and this item's id):

- LeanFinder: “Over a one-dimensional Noetherian local domain a domain with finite
  fraction field extension has finitely many primes above the maximal ideal and finite
  residue field extensions”. Eight hits, including
  `Algebra.instFiniteResidueFieldOfQuasiFiniteAt`,
  `Algebra.QuasiFinite.instFiniteResidueField`, and
  `IsLocalRing.ResidueField.finite_of_module_finite`. They require quasi-finiteness
  or module-finiteness, so none says this node's statement.
- Loogle: `Ideal.ResidueField, Module.Finite`. Twelve hits, including the same
  quasi-finite instances and the base-ring finiteness of a maximal-prime residue
  field; none proves the three clauses under the fraction-field hypotheses.
- Mathlib grep via msearch: `residueField.*[Ff]inite|[Ff]inite.*[Rr]esidueField`
  in RingTheory. Twenty-five hits on quasi-finite and unramified maps or residue
  fields of maximal ideals, with no matching theorem.
- LeanSearch: “one dimensional Noetherian local domain finite fraction field extension
  primes over maximal ideal finite residue field extensions”. Service unavailable:
  Internal Server Error, recorded by msearch; no mathematical verdict inferred.
- Direct rg in both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the
  repository's `lean/Sheaf`: item id and
  `residue.*[Ff]inite|[Ff]inite.*[Rr]esidue|primesOver`. Hits concern padic integers,
  finite-type schemes and number-field ramification, not this node. The item-id
  search gives no declaration. A separate declaration-name search for
  `dim_one_residue_fields_finite` in the source and project gives no collision.

The theorem docstring includes each of the node's four proof steps and the named
support nodes. No statement dispute or dependency fault was found. The server
single-file compile passed cleanly in 1.4 seconds (exit 0).

## Second reading by K1

Independently read the node copy, all four statement dependency nodes, the full
Lean module, and the Stacks algebra.tex source at
`lemma-finite-extension-residue-fields-dimension-1` (Tag 031F). The local Stacks
checkout is absent; I read the upstream raw TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex and
https://stacks.math.columbia.edu/tag/031F. The enclosing Around Krull-Akizuki
section introduces no standing hypotheses. The source has exactly the domains,
induced fraction-field injection, Noetherian local dimension-one base, finite
field degree, and three conclusions of this node. No correction is needed.

Object, hypothesis, and conclusion checklist (each verdict: exact):

1. Domains R and S: `(R : Type uR) (S : Type uS)`, `[CommRing R]
   `[IsDomain R] [CommRing S] [IsDomain S]`. The domain classes exclude the
   zero ring precisely as the node does.
2. Injective ring map: `(φ : R →+* S) (hφ : Function.Injective φ)`.
   There is no assumed algebra structure on S over R imposing a different map.
3. Fraction fields K and L: `(K : Type uK) (L : Type uL) [Field K] [Field L]`,
   `[Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]`.
   Read `IsFractionRing` in Localization/FractionRing.lean: localization at
   the non-zero-divisors. For domains this is exactly the fraction field.
4. The induced extension K into L: `[Algebra K L]` and
   `hcompat : ∀ r : R, algebraMap K L (algebraMap R K r) =
   algebraMap S L (φ r)`. Read Algebra and RingHom.toAlgebra in
   Algebra/Algebra/Defs.lean against def-pc-field-extension. The compatibility
   forces the field map to extend φ. Existence and uniqueness follow from
   localization; this presents the node's induced map without an extra
   restriction. Field maps are injective automatically.
5. Finite degree: `[FiniteDimensional K L]`. Read its abbreviation in
   LinearAlgebra/FiniteDimensional/Defs.lean: Module.Finite, exactly finite
   vector-space dimension, including inseparable extensions.
6. Noetherian local R and its maximal ideal m: `[IsNoetherianRing R]
   `[IsLocalRing R]`, `IsLocalRing.maximalIdeal R`. Read the dependency's
   Noetherian signature and `isNoetherianRing_iff_ideal_fg`; there is no
   Noetherian, integral, finite-type, or module-finite assumption on S.
7. Dimension one: `(hdim : ringKrullDim R = 1)`. Read the recorded
   `ringKrullDim` definition in KrullDimension/Basic.lean against its node:
   the strict prime-chain dimension, with 1 in WithBot ℕ∞.
8. Conclusion (1): `∀ n : PrimeSpectrum S, n.asIdeal.comap φ =
   IsLocalRing.maximalIdeal R → n.asIdeal.IsMaximal`. Bundling primality
   neither omits primes nor duplicates them by distinct proof witnesses.
9. Conclusion (2): `Set.Finite {n : PrimeSpectrum S |
   n.asIdeal.comap φ = IsLocalRing.maximalIdeal R}`. This is precisely the
   set quantified in (1), with no nonemptiness condition.
10. Conclusion (3): for every such `n` and contraction proof `hn`, the local
    `letI` is `(Ideal.ResidueField.map (IsLocalRing.maximalIdeal R)
    n.asIdeal φ hn.symm).toAlgebra`, and the conclusion is
    `FiniteDimensional (IsLocalRing.maximalIdeal R).ResidueField
    n.asIdeal.ResidueField`. Read ResidueField/Ideal.lean: the residue field
    is the residue of Localization.AtPrime, and map has the equality argument
    `I = J.comap f`, explaining `hn.symm`. Its map_algebraMap lemma confirms
    the canonical map extends φ. Its bijective_algebraMap_quotient_residueField
    identifies the base field with R/m since m is maximal. Hence this is the
    specified extension, not finiteness for a freely chosen scalar action.

All dependency records are usable as stated; the localization dependency's
three Mathlib declarations describe its three clauses, and the item uses its
residue-field clause. No new definition nodes or dependency modules exist in
this delivery, and none is missing. No private copies or hollow definitions
occur. The theorem is the only declaration and its proof is solely sorry.
Its docstring carries the source, blueprint id, and all four proof steps:
nonzero x and finite length, passage to the closed fibre, finite maximal primes,
and finite residue fields. Imports supply notions in the signature. Explicit
universes and autoImplicit=false leave no undeclared parameters. The node's
lean.statement is verbatim the signature before :=.

Edge cases: S may be K with R included, producing an empty fibre; both universal
claims are then vacuous and Set.Finite admits the empty set. R a field is
excluded by dimension exactly one, and zero rings are excluded by the domain
hypotheses. The fraction extension cannot have degree zero, because fields are
nontrivial; degree one is included. No bound on characteristic, residue-field
cardinality, or separability occurs. Four independent universes accommodate
arbitrary sizes. Scheme and index-set edge cases are not additional inputs.

Independent searches, with different phrases from the first reading:

- LeanFinder through msearch: "Krull Akizuki theorem closed fiber finite
  dimensional finite fraction extension local domain". Eight hits. Opened
  Ideal.finrank_quotient_map in NumberTheory/RamificationInertia/Basic.lean:
  it assumes a Dedekind base and Module.Finite R S and states a rank equality,
  not the present three conclusions. Quasi-finite residue-field and fibre
  finiteness hits require quasi-finiteness, not a hypothesis here.
- Loogle through msearch: `IsFractionRing, Module.Finite`. Twelve hits on
  lattices, integral closure, discriminants, and norms. None is this statement;
  integral-closure finiteness additionally requires integral closedness and
  separability, and concerns another ring.
- LeanSearch through msearch: "Krull Akizuki finite closed fiber over one
  dimensional local domain". Internal Server Error, unavailable; no verdict
  inferred from the unavailable service.
- Direct rg in Mathlib/RingTheory, WeilConjectures, and lean/Sheaf for
  `akizuki|finite.*primesOver|primesOver.*finite`, the item id, and the proposed
  declaration name. Mathlib candidates are quasi-finite or integral Dedekind
  results. Opened the project's krullAkizukiNoetherian: its conclusion is only
  Noetherianity of an intermediate ring, not finite primes and residue fields.
  Project citations of this node are not declarations of it. No matching
  existing declaration or name collision was found.

No mathematical or convention mismatch found; no Lean or node changes made.
Added only this independent second-reading report. The independent server
single-file compile passed with exit 0 in 1.4 seconds and no warnings. An initial
compile invocation used a repository-relative filename and failed before
compilation; using the sandbox's absolute filename resolved it.
