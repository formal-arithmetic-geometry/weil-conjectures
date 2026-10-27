## Worker report

The module `Sheaf.RingTheory.NormalizedPolynomialPrimeLift` states
`Algebra.normalizedPolynomialPrimeLift`. Its proof is `sorry`; no mathematical
theorem is proved. Three auxiliary definitions in the same owning module construct
the canonical maps used in this statement. They have concrete data and use only
existing Mathlib proofs for the kernel's primality and the invertible denominator.
There are no new DAG nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- A commutative ring and an arbitrary nonnegative number of variables are
  `(R : Type u) [CommRing R] (n : ℕ)`. Both source and target polynomial rings
  use `MvPolynomial (Fin n)`, with distinct roles despite having the same type.
- The prime `q'` is `q : PrimeSpectrum (MvPolynomial (Fin n) R)`. The notation
  `p = q' ∩ R` is rendered by `p : PrimeSpectrum R` and
  `hp : p.asIdeal = q.asIdeal.under R`. Thus `p` is fixed by contraction;
  it is not an additional freely chosen prime satisfying an extra restriction.
- The field `k` is exactly `p.asIdeal.ResidueField`. The helper
  `polynomialFibrePrime R n p q hp` constructs `Q` as the kernel of
  `MvPolynomial.eval₂Hom`, using the canonical `Ideal.ResidueField.map` on
  coefficients and the images of the target variables in `q.asIdeal.ResidueField`.
  Under `MvPolynomial.algebraTensorAlgEquiv`, this is precisely the kernel of
  the tensor evaluation map in the node. Its bundled primality follows from
  Mathlib's `RingHom.ker_isPrime` for maps to fields.
- The integer character and bound of the transcendence degree are
  `∃ r : ℕ, Algebra.trdeg k Q.asIdeal.ResidueField = (r : Cardinal) ∧ r ≤ n`.
  This records finiteness as well as the value; it does not truncate an infinite
  cardinal with `Cardinal.toNat`.
- `∃ (f : R) (hf : f ∉ p.asIdeal)` is exactly the required denominator outside
  the base prime. `Localization.Away f` is the prescribed ring `R_f`.
- `ψ : MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
  MvPolynomial (Fin n) (Localization.Away f)` is the required base-algebra map.
  `ψ.toRingHom.FiniteType` gives precisely finite type of its target over its source.
- `polynomialAwayResidueMap R p f hf` is `Localization.awayLift` of the canonical
  residue map, with invertibility supplied by `hf` and
  `Ideal.algebraMap_residueField_eq_zero`. It introduces no arbitrary map.
- `polynomialMapResidueReduction R n p f hf ψ` is the scalar extension `ψ̄`:
  `MvPolynomial.aeval` sends each variable to the coefficientwise reduction of
  its image under `ψ`. This is the scalar extension under the canonical polynomial
  tensor identifications, by evaluation's uniqueness. Its `.toRingHom.Finite`
  means that the target is a finitely generated module for this very map.
- The first ideal equality is `Ideal.comap ψ̄.toRingHom Q.asIdeal = I`, where
  `I = Ideal.span (Set.range (fun i : Fin n ↦ if r ≤ i.val then X i else 0))`.
  Zero-based indices `i.val ≥ r` are exactly the node's variables `x_{r+1},…,x_n`;
  the zero generators for earlier indices do not change the span.
- The extension `q_D = q'D` is
  `q.asIdeal.map (MvPolynomial.map (algebraMap R (Localization.Away f)))`.
  Its contraction along `ψ.toRingHom` is precisely `P`.
- The next equality identifies `P` with
  `p.asIdeal.map (MvPolynomial.C.comp (algebraMap R (Localization.Away f))) ⊔
  Ideal.span (…)`. The first summand is the ideal generated in `C` by `pR_f`,
  and the second is the specified last-coordinate ideal. Their supremum is
  the ideal generated jointly by these generators.
- Finally `Ideal.comap (MvPolynomial.map (polynomialAwayResidueMap …)) I = P`
  says that `I` is the fibre prime corresponding to `P`. The fibre-prime
  correspondence is contraction along this canonical coefficient map under the
  polynomial tensor identification. Primality of `I` already follows from the
  first contraction equality, since `Q` is prime; primality of `P` follows by
  this last contraction. These equalities retain the actual correspondence.

Dependency declarations read and used:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval`, `MvPolynomial.eval₂Hom`,
  and `MvPolynomial.map` provide the given polynomial ring and universal property.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`,
  `Ideal.ResidueField.map`. These give the node's affine residue fields. The
  recorded scheme version `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` in `Mathlib.AlgebraicGeometry.ResidueField` were
  also read: the ideal version is the same local-ring residue construction at
  the specified affine points, already recorded by the localization dependency.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `Mathlib.RingTheory.Localization.Away.Basic`: `Localization.awayLift`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`;
  `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, `RingHom.Finite`.
  The latter is definitionally `Module.Finite` for the map's algebra structure.
- Proof imports: `WeilConjectures.RingTheory.FibrePrimesResidueFields`
  (`PrimeSpectrum.fibre_primes_residue_fields`),
  `WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`
  (`IsLocalization.prime_localRing_residueField_iso`),
  `Mathlib.RingTheory.TensorProduct.MvPolynomial`
  (`MvPolynomial.algebraTensorAlgEquiv`),
  `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`
  (`Algebra.IsAlgebraic.trdeg_le_cardinalMk`), and
  `Sheaf.TraceFormula.RefinedNoetherNormalizationPrime`
  (`Algebra.refinedNoetherNormalizationPrime`). All recorded signatures and
  docstrings were read. The theorem's docstring carries all six DAG proof steps.

Sources checked: Stacks `algebra.tex`, Tag 051P, statement and induction proof;
Tag 0520, statement and entire proof, especially the fibre prime, coordinate
normalization, and common-denominator lifting. The current blueprint ancestor
`lem-trf-local-term-locality` was read for context.

Edge cases checked mathematically before drafting: `n = 0` has no variables,
`r = 0`, empty coordinate ideal, and the identity map with `f = 1`; for general
`n`, `r = 0` selects every coordinate and `r = n` selects none. Empty products
of coefficient denominators are `1`. The residue map need not be surjective;
the statement uses contraction, so it does not incorrectly assume surjectivity
of `R_f → κ(p)`. Zero rings have no input prime and hence no instance of the
premises. Zero divisors, finite residue fields, and arbitrary characteristics
are all allowed. All universe and object variables are explicit, and no
Noetherian, domain, or characteristic hypothesis is added.

Searches for an existing statement (all through the prescribed `msearch.py`):

- LeanFinder: “Lift a finite polynomial map over a residue field to a principal
  localization and compute its contracted coordinate prime”. Eight hits,
  including `Ideal.ResidueField.lift`, `.liftₐ`, and univariate residue-field
  comparisons; none asserts this lift and normalized contracted prime.
- Loogle: `"MvPolynomial", "FiniteType"`. Four hits about finite-type
  polynomial algebras and presentations; none gives the normalization or lift.
- Mathlib grep, `RingTheory`: `refined.*[Nn]ormal|[Ll]ift.*[Nn]ormal|[Nn]ormal.*[Pp]rime`.
  Twenty-five unrelated normalization/factorization hits; no match.
- LeanSearch: “Lift refined Noether normalization from a residue field to a
  principal localization of the base ring”. Eight hits including ordinary
  `exists_integral_inj_algHom_of_fg` and localization integer normalization;
  none is the prescribed full polynomial endomorphism with computed prime.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, normalized polynomial/prime combinations, and the four
  proposed declaration names found no existing exact statement or name clash.
  The existing refined Noether normalization theorem is imported as an
  ingredient, rather than duplicated.

Validation: the prescribed `scompile.py` compiled both the sandbox module and
its library-path version cleanly. The initial underspecified `algebraMap` in
the fibre evaluation was repaired by giving its polynomial domain explicitly.
There are no warnings apart from any expected `sorry` notification.

No statement dispute or node fault was found.

## Second reading by Q76

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
