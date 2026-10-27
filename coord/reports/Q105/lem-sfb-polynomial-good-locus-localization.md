## Worker report

The module `Sheaf.RingTheory.PolynomialGoodLocusLocalization` states
`MvPolynomial.polynomialModuleGoodLocus_localization`, with its entire proof `sorry`.
No definition is copied or introduced, and the natural-language statement is unchanged.
The definition node `def-sfb-polynomial-module-good-locus` already gives exactly the
item's inline definition, as the stage-1 review notes. I added this landed node to
`stmt_deps`, as authorized by brief-stage2 section 5, and imported its module publicly.

Hypothesis and clause correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`.
- A nonnegative number of variables: `(n : ℕ)`; the polynomial algebra is
  `MvPolynomial (Fin n) R`, including `n = 0`.
- An arbitrary P-module M: `(M : Type v) [AddCommGroup M]`
  `[Module (MvPolynomial (Fin n) R) M]`. The independent universes u and v impose
  no restriction on the size of the module. There is no finite-generation hypothesis.
- An arbitrary localizer: `(h : R)`, without regularity or nonvanishing.
- R_h: `Localization.Away h`, with `algebraMap R (Localization.Away h)`.
- M_h with its specified polynomial action: the fraction type
  `LocalizedModule ((Submonoid.powers h).map (C (σ := Fin n))) M`, equipped with
  the existing `localizedPolynomialModule R n M h`. Its fractions are m/C(h)^a,
  canonically identified with m/h^a in the underlying R-module localization. Their
  equality relations agree, and X_i sends m/h^a to (X_i m)/h^a. This is the exact
  existing definition used in def-sfb-polynomial-module-good-locus, not a chosen action.
- G_R(M): `polynomialModuleGoodLocus R n M`. The definition is the set of primes
  for which some f outside the prime witnesses BOTH `Module.Free (Localization.Away f)`
  and `Module.FinitePresentation (MvPolynomial (Fin n) (Localization.Away f))` on
  the canonically localized module. Its base action is restriction along constants.
  This is precisely the union of D(f) in the item; freeness allows empty and infinite bases.
- G_(R_h)(M_h): the fully explicit application `@polynomialModuleGoodLocus` at
  `Localization.Away h`, the fraction type above, and `localizedPolynomialModule R n M h`.
  Writing the module instance explicitly prevents any arbitrary scalar action.
- The identification Spec(R_h) with D(h) by inverse images of primes:
  `PrimeSpectrum.comap (algebraMap R (Localization.Away h))`. The equality uses its
  set image `''`, so both sides are subsets of Spec(R), exactly as in the node.
- The asserted right hand side: `(PrimeSpectrum.basicOpen h : Set (PrimeSpectrum R)) ∩
  polynomialModuleGoodLocus R n M`. By the definition of `basicOpen`, D(h) means
  h not in the prime ideal. The result is equality, not only one inclusion.
- No reducedness, finiteness, or nonzero-ring assumption occurs in the signature.

Sources read: `literature/stacks-project/algebra.tex`, equations
`equation-flat-and-finitely-presented`, `equation-good-locus`, and Tag 051X,
`lemma-generic-flatness-locus-localize` with both proof paragraphs. The polynomial
algebra is automatically free and finitely presented over the base, so the two
remaining goodness conditions are exactly the definition used here. All five
accepted DAG proof steps are included in the theorem's docstring.

Dependency declarations read and used:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval`, with its variable formula.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  its underlying space is `PrimeSpectrum R`. `PrimeSpectrum.comap` implements
  contraction, and `PrimeSpectrum.basicOpen` gives the principal open.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`, defined by existence
  of a basis of arbitrary index type (equivalently a subset of the module).
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`,
  defined by finite generators and a finitely generated relation kernel.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away`,
  `LocalizedModule.mkLinearMap`, and `IsLocalizedModule.lift`.
- `Sheaf.RingTheory.PolynomialModuleGoodLocus`:
  `MvPolynomial.localizedPolynomialModule`, `MvPolynomial.localizedPolynomialBaseModule`,
  `MvPolynomial.polynomialModuleGoodLocus`. All three definitions were read in full.
- For the proof plan: `Mathlib.RingTheory.Localization.Defs`, `IsLocalization.lift`
  and `IsLocalization.ringHom_ext`; `Mathlib.RingTheory.Localization.BaseChange`,
  `IsLocalizedModule.isBaseChange`; `Mathlib.LinearAlgebra.TensorProduct.Basis`,
  `Module.Basis.baseChange` and `Module.Basis.baseChange_apply` (plain proof import);
  `Mathlib.Algebra.Module.FinitePresentation`,
  `instFinitePresentationLocalizationLocalizedModule`.
  Other proof modules are already public transitive imports of the good-locus module.
  The polynomial coefficient localization is Mathlib's `MvPolynomial.isLocalization`
  in `Mathlib.RingTheory.MvPolynomial.Localization`, read with its docstring.

Edge cases checked before writing: for R = 0 the spectra are empty; for h = 0
or h nilpotent both Spec(R_h) and D(h) are empty; a unit h gives the original
locus under the canonical identification. For n = 0 the polynomial ring is R.
For M = 0 freeness has an empty basis and finite presentation holds, giving the
whole spectrum and the expected D(h) after contraction. Infinite-rank free
modules are allowed; no finite rank over R is inserted. Zero divisors in h
cause no problem because the localization equivalence relation includes a
further annihilating power, and the proof uses universal properties, not cancellation.

Searches actually run through msearch.py (Q105/item, 2026-10-24):

- LeanFinder: "The union of principal opens where a polynomial module is free over
  the base and finitely presented over the polynomial algebra commutes with localization".
  Eight hits included `Module.freeLocus_localization`, `Module.isOpen_freeLocus`,
  `Module.basicOpen_subset_freeLocus_iff`, and
  `Module.FinitePresentation.exists_free_localizedModule_powers`. No exact match:
  prime-stalk freeness is different from freeness on a whole principal chart with
  simultaneous finite presentation over the polynomial algebra.
- Loogle: `IsLocalizedModule, Module.FinitePresentation`. Twelve hits concerned
  finite presentations, lifted maps, and eventually free localizations, not this locus.
- LeanSearch: "Polynomial module good locus localization free finitely presented".
  Eight hits included localization preservation of finite presentation, localized
  freeness and `Module.freeLocus`; none states the desired equality.
- Mathlib grep: `polynomialModuleGoodLocus|goodLocus|freeLocus_localization` in
  RingTheory. Two hits, both on `Module.freeLocus_localization`, a different locus.
- Project/source rg: `polynomialModuleGoodLocus|goodLocus|good_locus|` plus the
  item id in `lean/WeilConjectures` and `lean/Sheaf`. Found the exact good-locus
  definition and its generic-freeness consumer, but no localization theorem.
  Also checked the proposed theorem name and good-locus name in
  `dag/lean_names_upstream.json` and `lean/WeilConjectures`, with no match.

Validation: scompile.py compiled both its sandbox view and the library-named
module cleanly (1.4 s and 1.3 s). There are no statement disputes, corrections,
new nodes, dependency repairs, or additional postponed theorems.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
