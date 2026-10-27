## Worker report

The module `Sheaf.RingTheory.PointedEtalePolynomialSolutionGlobalization` states
`AlgebraicGeometry.Scheme.pointedEtalePolynomialSolutionGlobalization`, with one
postponed theorem proof (`sorry`) and no new definitions. The DAG statement is
unchanged. No dependency repair or new node is necessary.

Source read: `literature/stacks-project/smoothing.tex`, Tag 0CAR,
`lemma-approximation-property-variant`, lines 3347–3384, especially its final
paragraph. The global Noetherian and G-ring assumptions are used to obtain the
local solution in the preceding approximation step. This item starts with that
étale algebra and its solution already supplied; its globalization uses no such
assumption. The two recorded upstream proof dependencies were read in full,
including their signatures and proof docstrings.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Commutative ring A | `A : CommRingCat.{u}` |
| Prime p in A | `p : PrimeSpectrum A`, whose ideal is `p.asIdeal` |
| R = A_p | The actual ring `Localization.AtPrime p.asIdeal` throughout |
| Commutative R-algebra E | `E : CommRingCat.{u}` and the structural ring map `α : Localization.AtPrime p.asIdeal →+* E`; specifying a commutative algebra by its structure map is equivalent to supplying its Algebra instance |
| Spec E → Spec R étale | `hα : Etale (Spec.map (CommRingCat.ofHom α))`, using the recorded scheme-morphism definition directly |
| Prime q of E contracting to pR | `q : PrimeSpectrum E` and `hq : IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) = q.asIdeal.comap α`; `Localization.AtPrime.map_eq_maximalIdeal` identifies this maximal ideal with pR |
| n,m ≥ 0 | `n m : ℕ`, with `Fin n` and `Fin m` indexing the two finite families |
| Polynomials over A | `f : Fin m → MvPolynomial (Fin n) A` |
| Tuple in E solving the equations through A → R → E | `c : Fin n → E` and `hc : ∀ k, MvPolynomial.eval₂ (α.comp (algebraMap A (Localization.AtPrime p.asIdeal))) c (f k) = 0` |
| An étale commutative A-algebra A' | Existential `A' : CommRingCat.{u}`, its structure map `a : A →+* A'`, and `Etale (Spec.map (CommRingCat.ofHom a))` |
| An A-algebra map j : A' → E | Existential `j : A' →+* E` and `j.comp a = α.comp (algebraMap A (Localization.AtPrime p.asIdeal))` |
| A tuple b solving the same equations | `b : Fin n → A'` and `∀ k, MvPolynomial.eval₂ a b (f k) = 0` |
| j(b_i) = c_i | `∀ i, j (b i) = c i` |
| p' = j⁻¹(q) | `p' : PrimeSpectrum A'` and `hpq : p'.asIdeal = q.asIdeal.comap j` |
| p' contracts to p in A | `hp' : p.asIdeal = p'.asIdeal.comap a` |
| The induced local homomorphism is an isomorphism | Existential ring equivalence `θ : Localization.AtPrime p'.asIdeal ≃+* Localization.AtPrime q.asIdeal`, with `θ.toRingHom = Localization.localRingHom p'.asIdeal q.asIdeal j hpq` |
| This is an R-algebra isomorphism | `θ.toRingHom.comp (Localization.localRingHom p.asIdeal p'.asIdeal a hp') = (algebraMap E (Localization.AtPrime q.asIdeal)).comp α`; these are exactly the canonical R-structure maps, so the equality states R-linearity of the ring isomorphism without choosing any additional algebra structures |
| θ(b_i/1) = c_i/1 | The displayed equality on `algebraMap A' (Localization.AtPrime p'.asIdeal) (b i)` and `algebraMap E (Localization.AtPrime q.asIdeal) (c i)` |
| Induced residue-field isomorphism | Mathlib's actual `IsLocalRing.ResidueField.mapEquiv θ`, with source definitionally `p'.asIdeal.ResidueField` and target `q.asIdeal.ResidueField` |
| Compatibility with the structural maps from κ(p) | The final equality of ring-homomorphism composites from `p.asIdeal.ResidueField`; the left map is `Ideal.ResidueField.map p.asIdeal p'.asIdeal a hp'`, and the right is `Ideal.ResidueField.map p.asIdeal q.asIdeal (α.comp (algebraMap A (Localization.AtPrime p.asIdeal))) ...` |

The equality proof supplied to the last residue-field map is built entirely from
existing terms: `Localization.AtPrime.under_maximalIdeal` contracts the maximal
ideal of A_p to p, `congrArg (Ideal.comap ...) hq` uses the supplied pointing,
and `Ideal.comap_comap` composes the contractions. It postpones no new theorem.
The residue-field isomorphism is induced from θ by the quotient construction,
not an independently selected field isomorphism. The ring-equivalence presentation
plus its R-commutation equality says exactly “R-algebra isomorphism”: the source
R-action is the canonical localization lift, and the target action is the given
R → E followed by localization. The inverse is R-linear automatically because θ
is bijective.

Statement dependencies used:

- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, and `Ideal.ResidueField` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` (read both definitions and
  the canonical local-ring and residue-field maps there).
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (full class signature read).
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`; evaluation is its existing `eval₂` in
  `Mathlib.Algebra.MvPolynomial.Eval`, the underlying evaluation of the recorded
  `MvPolynomial.aeval`. The `aeval` and `algHom_ext` signatures were also read.

All recorded proof-dependency modules are imported privately, including
`WeilConjectures.RingTheory.PrimeLocalizationEtaleAlgebraModel`
(`AlgebraicGeometry.Scheme.primeLocalization_etale_algebra_model`) and
`WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`
(`IsLocalization.prime_localRing_residueField_iso`), together with the Mathlib
localization, localization-away and étale-algebra modules named by the other
proof dependencies. The theorem docstring gives all six DAG proof steps, their
node names, the finite fraction and annihilator constructions, and the pointing
and residue compatibility argument.

Edge cases checked before writing and on rereading:

- `n = 0`: the empty tuple and constant-polynomial equations are retained;
  constants killed in E can be killed by the finite second localization.
- `m = 0`: the equation hypothesis and conclusion are empty; the arbitrary finite
  tuple must still lift, using the product of its denominators.
- `n = m = 0`: both products in the proof are 1; the pointed local-ring and
  residue-field conclusions remain in force.
- Zero divisors and nilpotents are allowed; the proof uses annihilator criteria,
  never cancellation.
- A a field is allowed: p is its zero prime, with no nonzero-prime restriction.
- A or E the zero ring supplies no prime p or q respectively, so there is no
  missing exceptional case or hidden Nontrivial assumption.
- All rings can be placed in an arbitrary common universe `u`; localization and
  the finitely presented descended algebra stay in that universe. No independent
  small test-object universe makes a hypothesis vacuous.

Searches actually run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`
for this group and item:

1. `leanfinder`: “Finite polynomial solutions in an etale algebra over a prime
   localization descend to an etale algebra preserving the pointed local ring”.
   Eight hits: `Algebra.exists_etale_of_isEtaleAt`, local étaleness tests,
   localization stability, and standard-étale notions; no exact theorem.
2. `loogle`: `Algebra.Etale, Localization.AtPrime`. Four hits about lifting
   coprime monic factorizations or splitting quasifinite fibres; none is this
   arbitrary finite-system globalization.
3. `grep`: `etale.*(descen|model)|exists.*etale|polynomial.*spread`, subdirectory
   `RingTheory`. Twenty-five hits about an étale locus, unramified structure,
   finite-type subalgebra descent, faithfully-flat descent and polynomial
   factorization; no exact statement. Read `Etale/Locus.lean:103`,
   `Smooth/NoetherianDescent.lean:294` and
   `Polynomial/UniversalFactorizationRing.lean:694` to check their differences.
4. `leansearch`: “Polynomial solutions in etale algebras over prime localizations
   descend to global etale algebras with isomorphic pointed local rings”. Eight
   hits on localization stability, local étaleness, and finite-type subalgebra
   descent, none giving the specified tuple and canonical pointed-ring map.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for pointed étale or
   polynomial globalization phrases, plus the exact item id: only other pointed
   étale topics, no declaration of this statement. Separate `rg` for
   `primeLocalization.*polynomial|pointedEtalePolynomial|pointed_etale_polynomial|polynomialSolutionGlobalization`
   in both trees and `dag/lean_names_upstream.json` found no name collision.
6. `rg` and direct reads of Mathlib localization and residue-field sources found
   `Localization.localRingHom`, `Localization.AtPrime.algebraOfLiesOver`,
   `Ideal.ResidueField.map` and `IsLocalRing.ResidueField.mapEquiv`; the latter
   existing maps suffice, so no new notion is introduced.

No statement dispute or node fault was found. The only changed node field is
`lean`, whose signature is extracted verbatim from the module. Compilation via
`scompile.py Q20 lem-trf-pointed-etale-polynomial-solution-globalization <file>`
passed for both sandbox and final library module names (3.7 s and 1.7 s), with
no errors or unexpected warnings.

## Second reading by Q20

The dispatcher brief prohibits starting other agents. This is a separate second
pass by the same worker, not a claim of an independent agent review; the
maintainer's independent delivery review remains applicable. I reopened the
node, the generated signature and the source paragraph and checked every row
above. In particular: the input contraction is to the maximal ideal of A_p;
the composite A → A' → E is fixed; the solution lives in the global A'; the
contracted prime and its contraction to A are stated; θ is required to be the
canonical `Localization.localRingHom`, not merely some abstract isomorphism;
its R-linearity and its action on the tuple are explicit; the residue-field
isomorphism is the one induced by θ; and its κ(p)-commutation uses the original
map A → A_p → E. No added Noetherian, henselian, finite residue-extension,
nonempty-index, or injectivity hypothesis occurs. Both empty-index cases were
checked. No mismatch or correction was found on this pass.
