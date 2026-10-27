## Worker report

The module `Sheaf.FieldTheory.RationalParameterBinomialIrreducible` states
`Polynomial.irreducible_X_pow_sub_C_of_algebraicIndependent`, with `sorry` as its
entire proof. No definition, additional theorem, new node, dependency repair, or
statement correction is needed. The accepted stage-1 split is preserved verbatim.
The previous worker's stale-assignment report concerned stage 1: the current node
has a passing split and no Lean record, and the current queue names stage 2.
The stage-handoff paragraph of coord/brief-stage2.md explicitly permits this work.

Hypothesis and clause correspondence:

- Fields `F ⊆ E`: `(F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]`.
  The algebra map from a field is injective. Independent universes `u v` cover
  all field sizes; no extra scalar structure is assumed.
- `r ≥ 1`: `(r : ℕ) (hr : 0 < r)`. This is exactly positive finite length.
- `t₁, ..., tᵣ ∈ E`: `(t : Fin r → E)`. Index zero is the first parameter;
  its index is explicitly `(⟨0, hr⟩ : Fin r)`.
- Algebraic independence in the evaluation sense: `(ht : AlgebraicIndependent F t)`.
  This Mathlib definition is injectivity of `MvPolynomial.aeval t`; over fields
  it is equivalent to the zero-evaluation condition in the node, by
  `algebraicIndependent_iff` immediately after the definition.
- The smallest subfield `K = F(t₁, ..., tᵣ)` is written directly as
  `IntermediateField.adjoin F (Set.range t)`. Its definition is the subfield
  closure of `Set.range (algebraMap F E) ∪ Set.range t`, exactly the stipulated
  smallest subfield. There is no arbitrary choice of a field or a map.
- Every integer `m ≥ 1`: `(m : ℕ) (hm : 0 < m)`. Positive integers are exactly
  positive naturals, and natural powers are the polynomial powers meant here.
- `X^m - t₁ ∈ K[X]`: the displayed term uses
  `(X : Polynomial (IntermediateField.adjoin F (Set.range t))) ^ m - C ...`.
  The constant is the subtype element `t ⟨0, hr⟩` with membership supplied by
  `IntermediateField.subset_adjoin F (Set.range t) (Set.mem_range_self ...)`.
  This is a named, proved Mathlib membership fact, with no postponed construction.
- Irreducibility is `Irreducible` of exactly that polynomial. This is the standard
  nonunit/factorization predicate; in this nontrivial polynomial ring it also
  excludes zero (zero factors as zero times zero). Thus it gives the node's
  nonzero, nonunit, and unit-factor clauses.
- No characteristic, separability, primality, or coprimality hypothesis occurs.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`,
  `Mathlib.Algebra.Algebra.Defs`, with fields `Field F` and `Field E`.
- `def-weil-pbc-transcendence-basis`: its Mathlib match is
  `IsTranscendenceBasis` in `Mathlib.RingTheory.AlgebraicIndependent.Defs`.
  The item's statement uses only the algebraic independence and generated-field
  notions explicitly included in that dependency's statement. Use
  `AlgebraicIndependent` in the same module, rather than imposing maximality or
  algebraicity of `E` over the generated field. `IntermediateField.adjoin` in
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs` is the generated field
  explicitly described by that dependency's statement and match. Both definitions
  and the membership lemma `IntermediateField.subset_adjoin` were read.
- `def-weil-polynomial-ring`: `Polynomial`,
  `Mathlib.Algebra.Polynomial.Basic`; its structure and docstring were read.
- The stated proof dependency
  `lem-trf-monic-polynomial-fraction-field-irreducibility` is a Mathlib leaf matched
  to `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`,
  `Mathlib.RingTheory.Polynomial.GaussLemma`. Its complete signature and docstring
  were read and its module is imported privately for the proof plan. The other
  proof dependency is the algebraic independence definition already imported.

The declaration docstring records all four accepted proof steps: denominator
clearing to show the first parameter transcendental over the remaining-parameter
field; the fraction-field presentation; irreducibility by degree one in the first
parameter after regrouping the two polynomial variables; monic Gauss transfer.
It uses the reviewed direct degree argument, not the dropped Eisenstein node.

Edge cases checked before writing:

- `r = 1` is admitted: the remaining-parameter field is `F`, and `K = F(t₁)`.
- `m = 1` gives a nonconstant linear polynomial, hence irreducible over `K`.
- In characteristic `p`, including `p ∣ m`, the same degree-one-in-parameter
  argument applies. For example `X² - t` over `F₂(t)` is irreducible though
  inseparable; no separability claim is present.
- `r = 0` and `m = 0` are exactly the excluded cases in the node, and the
  positive-index proof `hr` is necessary to name the first parameter.
- Algebraic independence forces each parameter nonzero and transcendental;
  no hidden nonzero-parameter hypothesis is added.
- A family independent over `F` inside a larger field `E` need not be a
  transcendence basis of `E/F`. The signature correctly does not assert that.

Searches for an existing statement (all made through the prescribed wrapper or
read-only source searches):

- LeanFinder, query "For algebraically independent t1,...,tr over F, the polynomial
  X^m-t1 over F(t1,...,tr) is irreducible for every positive m": eight hits, including
  `MvPolynomial.irreducible_toPolynomialAdjoinImageCompl`,
  `X_pow_mul_sub_C_irreducible`, `irreducible_X_pow_sub_C_of_root_adjoin_eq_top`,
  and prime/prime-power Kummer criteria. None states this result.
- Loogle, query `AlgebraicIndependent, Irreducible`: one hit,
  `MvPolynomial.irreducible_toPolynomialAdjoinImageCompl`. Its full source signature
  was read: it assumes an already irreducible multivariate polynomial and concludes
  irreducibility over an adjoined subalgebra of the other parameters. It is not
  this binomial statement over the field generated by all parameters.
- LeanSearch, query "The polynomial X^m minus the first of algebraically independent
  parameters is irreducible over their generated rational function field": eight
  hits, with the same general criteria, `Polynomial.irreducible_X`, and unrelated
  power-series/multivariate results. No exact match.
- Mathlib grep via msearch, query
  `X_pow.*irreducible|irreducible.*X_pow|irreducible.*adjoin`, subdirectory
  `FieldTheory`: twenty hits in Perfect, KummerPolynomial, KummerExtension,
  SeparablyGenerated, and IntermediateField/Adjoin/Basic. The source signature of
  `X_pow_mul_sub_C_irreducible` was read; it needs inductive irreducibility
  hypotheses rather than algebraic independence. The prime-exponent criteria
  do not cover arbitrary positive `m` without a further argument.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `rational.parameter.binomial|irreducible.*(parameter|transcendental)|X_pow.*sub_C.*irreducible`
  found Kummer applications and geometric irreducibility results, but no matching
  theorem. Searching the exact node id found only a proof-plan reference in
  `Sheaf.FieldTheory.AlgClosedFinitelyGeneratedFinite`, not a declaration.
- Searching the proposed declaration name and `irreducible_X_pow_sub_C_adjoin`
  in Mathlib, both library roots, and `dag/lean_names_upstream.json` found no hit.

No statement is disputed, and no node fault was found.

Validation uses only scompile.py and deliver2.py; no local/global library build
or direct mutation of the shared repository is performed.

Current retry validation (2026-10-23): reread the current accepted node and every
statement dependency, including the full Mathlib signatures and docstrings. Repeated
LeanFinder, Loogle, LeanSearch, Mathlib grep and both project-root searches; no exact
existing theorem was found. The source module compiled through scompile.py in both
sandbox and library contexts (1.0 seconds each), with no errors or unexpected warnings.
Verified that the node copy differs from the live node only in `lean`, and its
recorded signature is verbatim from the module. No stage-1 split was reopened.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
