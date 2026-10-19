## Worker report

The module `Sheaf.FieldTheory.ResidueFactorRootSelection` states
`Polynomial.exists_index_eval₂_eq_zero_and_ne_zero`. Its sole proof is `sorry`, as required
for stage 2. No definitions, auxiliary theorems, dependency repairs or new nodes are needed.
Only the item's `lean` field changes.

The source was read in `literature/stacks-project/algebra.tex`, lines 40070–40126,
Tag 00UF, `lemma-standard-etale-finite-flat-Zariski`, final residue-field paragraph.
The node isolates precisely that paragraph's choice of a root of the irreducible residue
factor that avoids the image of the localization polynomial.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field `k`: `{k : Type u} [Field k]`.
- Polynomials `f,g ∈ k[t]`: `(f g : k[X])`.
- Monic `f`, meaning leading coefficient one: `(hf : f.Monic)`, with
  `Polynomial.Monic` defined as `leadingCoeff f = 1`.
- A field extension `L/k`: `{L : Type v} [Field L] [Algebra k L]`.
  The coefficient map and all evaluations use that same `algebraMap k L`.
  The algebra encoding is exactly the recorded field-extension declaration; every ring
  homomorphism of fields induces it by `RingHom.toAlgebra`.
- A finite indexed family of elements of `L`: `{I : Type w} [Fintype I] (α : I → L)`.
  No nonemptiness, distinctness, algebraic closure, separability, or degree bound is added.
  All three universes are explicitly bound and independent.
- The prescribed coefficient-image factorization:
  `(hfactor : f.map (algebraMap k L) = ∏ i : I, (X - C (α i)))`.
  Each `X - C (α i)` is a polynomial over `L`; multiplicities in the family are retained.
- An irreducible `f₁ ∈ k[t]`: `(f₁ : k[X]) (hf₁ : Irreducible f₁)`.
  Mathlib's `Irreducible` records nonunit and a unit factor in every factorization;
  nonzero follows in this nontrivial polynomial ring by `Irreducible.ne_zero`.
  Thus there is no omitted nonzero hypothesis and no extra monicity assumption on `f₁`.
- Divisibility over the original field: `(hdiv : f₁ ∣ f)` and
  `(hnotdiv : ¬ f₁ ∣ g)`, both in `k[X]`, rather than in `L[X]`.
- An index in the given family: `∃ i : I`.
- Vanishing of `f₁` at that index: `f₁.eval₂ (algebraMap k L) (α i) = 0`.
- Nonvanishing of `g` at the same index:
  `g.eval₂ (algebraMap k L) (α i) ≠ 0`, joined by conjunction inside the same existential.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`;
  `Polynomial.leadingCoeff` and `Polynomial.Monic`,
  `Mathlib.Algebra.Polynomial.Degree.Defs`.
- `def-pc-field-extension`: `Algebra`, `algebraMap`, `RingHom.toAlgebra`,
  `Mathlib.Algebra.Algebra.Defs`; the injectivity remark is `RingHom.injective`,
  `Mathlib.RingTheory.SimpleRing.Basic`.
- `def-weil-polynomial-root`: `Polynomial.eval₂`,
  `Mathlib.Algebra.Polynomial.Eval.Defs`; coefficient extension is `Polynomial.map`
  in that module. This uses the recorded declarations directly, without private copies.
- Proof dependency `lem-pur-polynomial-field-pid`: `Polynomial.instEuclideanDomain`,
  `Mathlib.Algebra.Polynomial.FieldDivision`, and
  `EuclideanDomain.to_principal_ideal_domain`, `Mathlib.RingTheory.PrincipalIdealDomain`;
  the inferred integral-domain instance was read in
  `Mathlib.Algebra.EuclideanDomain.Basic`.
- Proof dependency `lem-weil-coefficientwise-extension-injective`:
  `Polynomial.map_injective`, `Mathlib.Algebra.Polynomial.Eval.Coeff`, and
  `Polynomial.mapRingHom`, `Mathlib.Algebra.Polynomial.Eval.Defs`.
- Proof dependency `lem-trf-divisor-of-split-polynomial`: `Polynomial.Splits.of_dvd`,
  `Mathlib.Algebra.Polynomial.Splits`. The definition `Polynomial.Splits`,
  `splits_iff_exists_multiset` and `Splits.exists_eval_eq_zero` were also read.
  Its module is imported privately for the stated proof plan.

The theorem docstring carries all five proof steps of the node: nonconstancy and
injectivity, the original-field PID Bezout identity, divisor splitting after coefficient
extension, selection from the prescribed product, and evaluation of Bezout for avoidance.
Statement dependencies are public imports; modules used only for the proof are ordinary
imports. All proof dependencies already resolve to Mathlib, so no project declaration is
missing and there is no import cycle.

Edge cases checked mathematically before writing:

- Empty `I`: the product is one. Injectivity gives `f = 1`, whose irreducible divisor
  cannot exist. The hypotheses are therefore inconsistent, as required; this case is
  included, not excluded by a `Nonempty I` binder.
- `f = 0` is excluded by monicity in a field; a constant monic `f` is one and has no
  irreducible divisor. `f₁ = 0` and unit or constant nonzero `f₁` are excluded by
  irreducibility over a field.
- `g = 0` is excluded by `¬ f₁ ∣ g`; a nonzero constant `g` is permitted and its
  evaluation stays nonzero. Repeated factors, inseparable factors and positive
  characteristic remain permitted.
- `L = k` and the identity algebra structure are included. No assumption that `f₁`
  remains irreducible over `L` is present; the Bezout identity is formed over `k`.
- Finite index types of arbitrary universe are included with `[Fintype I]`; this is
  finite enumeration data for precisely the finite family, not a size restriction.

Searches performed with the prescribed wrapper:

- `leanfinder`: “An irreducible divisor of a polynomial with a specified finite linear
  factorization over a field extension has a root in that family where a polynomial it
  does not divide is nonzero”. Eight hits, including
  `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`,
  `AdjoinRoot.mul_div_root_cancel`, irreducible-factor existence and
  `Irreducible.exists_dvd_monic_irreducible_of_isIntegral`; none states this combination.
- `loogle`: `Polynomial.Splits, Irreducible`. Seven hits, including degree-one
  results for irreducible split polynomials, a finrank divisibility lemma, and Galois
  transitivity; none selects an index of the prescribed factor list with avoidance.
- `grep`: `exists.*eval.*ne_zero|irreducible.*eval|eval.*irreducible`, subdirectory
  `Algebra/Polynomial`. Four hits: `eval₂`, `smeval`,
  `exists_eval_ne_zero_of_natDegree_lt_card` and
  `Irreducible.aeval_ne_zero_of_natDegree_ne_one`; none is the statement.
- `leansearch`: “An irreducible factor of a split polynomial has a root from the
  prescribed list of linear factors avoiding a polynomial not divisible by that factor”.
  Eight hits on split-polynomial root existence, a root choice, degree-one irreducibles
  and `Polynomial.factor`; none includes both required clauses or the prescribed index.
- Direct `rg` of the same evaluation/irreducibility patterns in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared `lean/Sheaf`
  found unrelated reduced norm, Hopf ideal, etale primitive-element and p-independence
  declarations. No full match. Direct search for the node id in upstream source and
  `dag/lean_names_upstream.json` found no binding.
- Direct name search for `exists_index_eval₂_eq_zero_and_ne_zero` in Mathlib, upstream,
  shared project source and the upstream-name index found no declaration.

No statement fault or disputed case was found. No statement correction is made.

## Second reading by N8

This is the worker's own second pass, not a claim of an independent review; the dispatcher
brief assigns the independent delivery review to the maintainer and forbids sub-agents.
With the node and module reopened, I checked all binders and clauses listed above. The
factorization is in `L[X]`, the divisibility hypotheses stay in `k[X]`, and both evaluations
use exactly the algebra map used in the factorization. The conclusion returns an index,
not just an arbitrary root, and its two properties share that index. The empty case is
retained and the factor is not assumed irreducible over the extension. The Mathlib
`Irreducible` convention supplies the node's nonzero condition as a consequence. No
mismatch was found and no signature change was needed on this second pass.

Validation: the complete delivered file is checked using `scompile.py` at the default
per-file limit. The prescribed `deliver2.py --no-push` dry run and final delivery provide
server preflight and compilation validation.
