## Worker report

The delivery states `Algebra.exists_monic_prime_coordinate_chart` in
`Sheaf.TraceFormula.MonicPrimeCoordinateChart`. It has one postponed theorem and
no definitions, instances, auxiliary lemmas, or proofs. The node is unchanged
except for its `lean` record.

Source read: `literature/stacks-project/algebra.tex`, Tag 051P,
`lemma-refined-Noether-normalization`, especially its nonzero-prime induction
paragraph (lines 28074–28124), and Tag 051N, `lemma-helper-polynomial`
(lines 27963–27994). These give exactly the triangular change, monic polynomial,
finite substitution, and contraction used here. The declaration docstring supplies
all six proof steps from the node, including the finite-generation induction and
both directions of the constant-coefficient ideal-membership criterion.

Hypotheses and clauses, in statement order:

- The field is `(k : Type u) [Field k]`, with its universe declared explicitly.
  The positive number of variables is `n = m + 1`, where `(m : ℕ)` is unrestricted;
  `A` is `MvPolynomial (Fin (m + 1)) k`. This parametrizes every `n ≥ 1`.
- The nonzero prime is `(q : Ideal A) [q.IsPrime] (hq : q ≠ ⊥)`.
  The fixed nonzero element is `(g : A) (hg : g ≠ 0) (hgq : g ∈ q)`.
  No nonconstancy hypothesis is added: it follows from primality/properness.
- The exponent family is `e : Fin m → ℕ`, with `∀ i, 0 < e i`. The scalar is
  `a : k` with `a ≠ 0`, and the degree is `d : ℕ` with `0 < d`.
- `sigma : A ≃ₐ[k] A` is the algebra automorphism. For each `i : Fin m`, the
  equation for `sigma (MvPolynomial.X i.castSucc)` is precisely the given addition
  of the final variable to the power `e i`. A separate equation fixes
  `MvPolynomial.X (Fin.last m)`.
- The corresponding equations for `sigma.symm` subtract the same powers and fix
  the final variable. The `AlgEquiv` structure includes both inverse laws.
- The normalized polynomial is the witness `f : A` with the equality
  `f = MvPolynomial.C a⁻¹ * sigma g`.
- Monicity and degree in the FINAL variable use the witness
  `F : Polynomial (MvPolynomial (Fin m) k)`, with `F.Monic`, `F.natDegree = d`,
  and `Polynomial.aevalTower (MvPolynomial.rename Fin.castSucc)
  (MvPolynomial.X (Fin.last m)) F = f`. Thus `F` is the expression of `f` in
  `B[x_n]`, where `B = k[x_1,...,x_m]`, with the ordinary inclusion of `B`.
  This polynomial presentation is uniquely determined by `f`; it imposes no
  restriction or extra choice on the original data. In particular this is not
  a claim about the total degree of `f`.
- `qStar : Ideal A` is fixed by `qStar = Ideal.map sigma.toRingHom q`, the ideal
  image under the automorphism. `qStar.IsPrime` and `f ∈ qStar` are both stated.
- `C = B[y_n]` is `Polynomial (MvPolynomial (Fin m) k)`. The witness
  `psi : C →ₐ[k] A` satisfies the defining equality
  `psi = Polynomial.aevalTower (MvPolynomial.rename Fin.castSucc) f`.
  By the defining formulas `aevalTower_C` and `aevalTower_X`, this sends the first
  `m` variables to the corresponding variables of `A` and the last variable to
  `f`. It is the canonical substitution, not an unconstrained map.
- `psi.toRingHom.Finite` is finite generation of `A` as a `C`-module for the
  scalar action given by this exact map. In Mathlib this is definitionally
  `Module.Finite C A` for `psi.toRingHom.toAlgebra.toModule`.
- The specifically required generators are also stated: for EVERY `h : A`,
  there exists `c : Fin d → C` such that
  `h = ∑ j : Fin d, psi (c j) * MvPolynomial.X (Fin.last m) ^ (j : ℕ)`.
  This says exactly that `1,x_n,...,x_n^(d-1)` generate for the scalar action
  of `psi`, rather than merely asserting some finite generating family exists.
- The ideal `p : Ideal B` is fixed by
  `p = Ideal.comap (MvPolynomial.rename Fin.castSucc).toRingHom qStar`.
  This inclusion is exactly `psi|_B` by the defining equation for `psi`.
  The conclusion includes `p.IsPrime`.
- The contracted ideal equality is
  `Ideal.comap psi.toRingHom qStar = Ideal.map Polynomial.C p ⊔
  Ideal.span {Polynomial.X}`. Here `Ideal.map Polynomial.C p` is `pC`,
  `Ideal.span {Polynomial.X}` is `(y_n)`, and `⊔` is ideal sum.
- The explicit final clause quantifies over EVERY `H : C` and states
  `psi H ∈ qStar ↔ Polynomial.eval 0 H ∈ p`. This evaluates only the final
  source variable at zero and leaves all variables of `B` unchanged.

Dependency interfaces read and used:

- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` (line 82) and `MvPolynomial.algHom_ext` (line 436);
  `Mathlib.Algebra.MvPolynomial.Eval`, `MvPolynomial.aeval` (line 593).
  The polynomial objects in the statement are these exact Mathlib types.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite` (line 120), and its ring-map encoding `RingHom.Finite`
  (lines 168–172 of the same module). There is no private module-finiteness notion.
- The stated proof dependency `lem-trf-polynomial-shear-leading-coefficient` is
  imported WITHOUT `public` from
  `Sheaf.TraceFormula.PolynomialShearLeadingCoefficient`, declaration
  `Algebra.exists_polynomial_shear_leading_coefficient`. Its full signature and
  docstring were read: its `Fin (m+1)` last-variable convention is used here.
- Additional existing Mathlib operations: `MvPolynomial.rename`,
  `Polynomial.aevalTower`, `Polynomial.Monic`, `Polynomial.natDegree`,
  `Ideal.map`, `Ideal.comap`, and `Polynomial.eval`. In particular the source
  and coefficient inclusions are Mathlib constructions, with no new notion.

Edge cases checked before writing:

- `n = 1`, represented by `m = 0`: the exponent family and shear equations
  over `Fin m` are empty; the final-variable and inverse equations force the
  identity. `B = MvPolynomial (Fin 0) k` is canonically `k`, its contracted
  prime is zero, and the contracted ideal in `B[y_n]` is `(y_n)`. A nonzero
  `g` in the prime has positive degree. No extra nonempty-index assumption occurs.
- `d = 1`: `Fin d` has just exponent zero, so the displayed spanning equation
  requires generation by `1`, exactly as the linear monic relation implies.
- Over `k = F_2`, with two variables, `q = (x_1)` and `g = x_1`, the shear
  `x_1 ↦ x_1+x_2` has `e = 1`, `f = x_1+x_2`, and `d = 1`. The transported
  prime is `(x_1+x_2)` and the source contraction is `(y_2)`. Subtraction is
  interpreted correctly in characteristic two. No infinitude or characteristic
  hypothesis is present.
- Higher-degree `g`, including powers of an element of `q`, is allowed; `d`
  and the spanning family are not forced to be minimal. A unit `g` would
  contradict `hgq` and properness, rather than requiring a separate hypothesis.
- The bottom ideal is explicitly excluded and the top ideal is excluded by
  `q.IsPrime`. There is no empty-scheme or independent universe restriction.

Searches actually made:

- `msearch.py` leanfinder: "A triangular polynomial automorphism makes a
  polynomial in a nonzero prime monic in the last variable and substitution of
  that monic polynomial defines a finite ring map with contracted prime
  p[T]+(T)". Eight hits, including `MvPolynomial.finite_universalFactorizationMap`,
  `NoetherNormalization.T1`, and `Polynomial.exists_image_comap_of_monic`.
  These supply different normalization maps or spectra results, not this full chart.
- `msearch.py` loogle: `MvPolynomial, Ideal.comap`. One hit,
  `MvPolynomial.mem_ideal_of_coeff_mem_ideal`; not the chart theorem.
- `msearch.py` grep: `monic.*comap|comap.*monic|T_leadingcoeff_isUnit`, restricted
  to `RingTheory`. Twelve hits, including private ordinary-normalization helpers,
  monic polynomial spectra, `Ideal/MonicSpan`, and `IsAdjoinRoot`; none is exact.
- `msearch.py` leansearch: "A monic polynomial in a nonzero polynomial prime
  defines a finite substitution map whose contracted ideal is p[T] plus T".
  Eight hits, including `Polynomial.modByMonicHom`,
  `Ideal.isPrime_map_C_of_isPrime`, and `NoetherNormalization.T1`; none states
  the prescribed automorphism, finite chart, spanning family, and contraction.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `monic_prime_coordinate|monicPrimeCoordinate|monic.*prime.*chart|prime.*coordinate|051P|triangular.*automorphism`
  found the parent refined-normalization theorem, the existing shear theorem,
  and unrelated coordinate constructions, with no exact match.
- `grep -rn lem-trf-monic-prime-coordinate-chart lean/WeilConjectures` found none.
  Searching the proposed declaration name in Mathlib, both project source trees,
  and `dag/lean_names_upstream.json` found none.

No statement correction, new nodes, dependency repairs, or statement dispute.

## Validation

The prescribed `scompile.py` was invoked against the published live build.
`deliver2.py --no-push` then reported `OK (dry run): commit 08225ff474c passes
the preflight and compiles; nothing pushed`. Its compile gate rejects errors and
all warnings except the expected postponed-proof warning. The only three staged
files were this report, the item node, and its module.

## Second reading by Q26

No independent worker reading is claimed: this assignment requires direct worker
delivery and the maintainer supplies the independent review. On rereading the
node and the signature, every displayed substitution and its inverse, scalar
normalization, last-variable monicity, named spanning family, primality assertion,
ideal equality, and universally quantified membership criterion is present.
The polynomial witness `F` records last-variable degree without changing the
source ring `A` or mistaking it for total degree. The equalities fixing `psi`,
`qStar`, and `p` prevent substitution of arbitrary maps or ideals. No mismatch
or change to the node's statement was needed.
