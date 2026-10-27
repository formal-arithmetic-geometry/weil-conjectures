## Worker report

Delivered module: `Sheaf.RingTheory.FormalConormalQuotientData`.
Main statement: `RingTheory.FormalConormal.quotientData`.
The theorem has `sorry` as its entire proof; all nine construction helpers have real data.
Only the assigned node's `lean` field changes. No new nodes, dependency repairs,
statement corrections, or disputed statements are needed.

The source was read in `literature/stacks-project/algebra.tex`: the conormal
construction in Tag 00RU (`lemma-differential-seq`), the canonical differential map
in Tag 00RO (`equation-functorial-omega` and its universal property), the Noetherian
power-series lemma 0306, and the finite-module completion theorem 00MA (3).
The continuous extension is the node's explicit auxiliary argument, not a claim
that Tag 00RU itself already discusses continuous differentials.

The module names intermediate constructions of this very node, using existing
Mathlib operations. These are helpers belonging to the quotient construction,
not new independent mathematical notions. Their full names are listed in
`lean.declarations` and each has its source and blueprint docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Field F, arbitrary nonnegative n and s | `(F : Type u) [Field F] (n : ℕ)`, `{s : ℕ}` in the section; every variable and universe is explicitly bound |
| D = F[[t_1,...,t_n]] | `MvPowerSeries (Fin n) F`, the recorded Mathlib definition |
| Variable ideal n | `variablesIdeal F n = Ideal.span (Set.range MvPowerSeries.X)` |
| A list of s relations with I contained in n | `f : Fin s → MvPowerSeries (Fin n) F`; `relationIdeal f = Ideal.span (Set.range f)`; `hf : ∀ j, f j ∈ variablesIdeal F n`, equivalent to the stated ideal containment |
| R = D/I | `Ring f`, definitionally `MvPowerSeries (Fin n) F ⧸ relationIdeal f` |
| m = nR | `maximalIdeal f`, the ideal image under `Ideal.Quotient.mk (relationIdeal f)`; the helper's name introduces no additional maximality assumption |
| M and its canonical derivation | `Differentials F n = KaehlerDifferential.Continuous F D (variablesIdeal F n)` and the dependency's `KaehlerDifferential.continuousD` |
| T = M tensor_D R, with its R action | `TensorModule f = Ring f ⊗[D] Differentials F n`; the tensor order follows the dependency record's explicit convention via `TensorProduct.comm` |
| L spanned by d(f_j) tensor 1 | `relations f = Submodule.span (Ring f) (Set.range fun j ↦ 1 ⊗ₜ[D] continuousD ... (f j))` |
| N = T/L and q | `QuotientModule f = TensorModule f ⧸ relations f`; `q = (relations f).mkQ` |
| Positive r, R_r and C_r | `r : ℕ` represents the exponent `r + 1`; `Truncation f r = Ring f ⧸ maximalIdeal f ^ (r + 1)` and `KaehlerDifferential F (Truncation f r)` |
| Projection p_r | `m.val r`, the coordinate of the existing compatible-family definition `Continuous` |
| Induced differential map u_r | The existential family `u` of D-linear maps, characterized for every `h : D` by `u r (D F _ (h mod n^(r+1))) = D F _ (h mod I mod m^(r+1))` |
| N finite over D | First conjunct `Module.Finite D (QuotientModule f)` |
| Specified elements generate N over R | Second conjunct: their `Submodule.span (Ring f)` is `⊤` |
| Canonical iota is an R-module isomorphism | Third conjunct `Function.Bijective (AdicCompletion.of (maximalIdeal f) (QuotientModule f))`; `of` is already R-linear, so this is exactly that it is a module isomorphism |
| n^r N = m^r N after restricting scalars | Fourth conjunct equates the positive power submodule over D to `.restrictScalars D` of the power submodule over R |
| Well-defined F-derivation delta | `∃ δ : Derivation F (Ring f) (QuotientModule f)`, with its value on every quotient representative specified by the displayed tensor/quotient formula |
| Well-defined R-linear phi_r | `φ : ∀ r, QuotientModule f →ₗ[Ring f] KaehlerDifferential F (Truncation f r)`, and the formula on every `q(a ⊗ m)` is `a • u r (m.val r)` |
| phi_r delta(x) = d(x mod m^r) | The next conjunct for every `r : ℕ` and `x : Ring f` |
| tau_r phi_(r+1) = phi_r | Final conjunct for every r and every z, using the dependency's canonical `KaehlerDifferential.adicTransition F (Ring f) (maximalIdeal f) r` |

The existential `u` does not replace a canonical map with an arbitrary map:
its values on all differentials of representatives are specified. These
representatives generate the truncated differential module over D, so this
characterization determines exactly the induced differential map. The existence
assertion includes the well-definedness of this canonical map. Similarly delta
and phi are fixed on all quotient representatives and all pure tensors.

Mathlib's `AdicCompletion` uses exponents starting at zero; the exponent-zero
module quotient is the zero module, whose unique coordinate adds no condition.
Deleting it gives exactly the positive-index inverse limit of the node.
`AdicCompletion.of` sends z to the family of its residue classes, so the third
conjunct asserts bijectivity of the specified map, not an unspecified isomorphism.
The equality of the power submodules is indexed positively as in the node.

Dependency declarations read and used:

- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, its algebra structure,
  and `MvPowerSeries.X`.
- `Sheaf.RingTheory.ContinuousKaehlerDifferential`:
  `KaehlerDifferential.Continuous`, `continuousSubmodule`, `continuousD`,
  and `adicTransition`; their full definitions and docstrings were read.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct`, its left-module
  structure, and the `LinearMap.baseChange` convention described in the node record.
  Only the actual tensor product is needed in this statement.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`,
  `linearMapEquivDerivation`; the signature and docstring of `map` were also read.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- Proof imports: `Sheaf.SixFunctors.TraceFormula.FormalPowerSeriesContinuousFree`
  (`RingTheory.formalPowerSeriesContinuousDifferentials_free`),
  `Mathlib.RingTheory.MvPowerSeries.Equiv` (`MvPowerSeries.isNoetherianRing`),
  `Mathlib.RingTheory.AdicCompletion.Completeness`
  (`MvPowerSeries.instIsAdicCompleteSpanRangeXOfFinite`), and
  `WeilConjectures.RingTheory.FiniteModuleComplete`
  (`finite_module_complete_over_complete_noetherian`).

Edge cases checked mathematically before writing:

- n = 0: the power-series ring is F, its variable ideal is zero, and hf forces
  every relation to be zero. The continuous differential module, T and N are zero;
  the empty set generates N. No nonempty or positive-dimension binder excludes it.
- s = 0: the relation ideal and relation span are zero. No relation generator is
  required and the formulas still state the unreduced construction.
- Zero or redundant relations: `Ideal.span` and `Submodule.span` handle them
  without independence or nonvanishing assumptions.
- First positive exponent: r = 0 in Lean means exponent 1; its differential module
  may be zero, and all maps and compatibility still have the specified types.
- Arbitrary characteristic: there is no characteristic-zero or separability binder.
- All objects are constructed from F in universe u; no smaller test-object universe
  or extraneous equality between independent universes is imposed.

Searches made with the prescribed `msearch.py Q43 <item>` wrapper:

- LeanFinder: “A quotient of continuous differentials of formal power series by
  relation differentials is finite complete and has a descended derivation and
  compatible truncation maps”. Eight hits, including `BDeRham`,
  `KaehlerDifferential.derivationQuotKerTotal` and univariate derivative/truncation
  results; none is this continuous quotient construction.
- Loogle: `KaehlerDifferential, AdicCompletion`. Zero hits.
- Mathlib grep under `RingTheory`:
  `continuous.*[Dd]ifferential|formalConormal|conormalQuotient`. Zero hits.
- LeanSearch: “finite complete quotient of continuous differentials of formal
  power series with descended quotient derivation”. Eight hits concerning formal
  univariate derivatives, analytic series, and `derivationQuotKerSq`; no match.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  `formalConormal|conormalQuotient|lem-trf-formal-conormal-quotient-data`.
  The only hits were private `conormalQuotientEquiv` helpers in unrelated symmetric
  conormal presentation modules; neither states this node.
- Required `grep -rn` for the item's id in `lean/WeilConjectures`: no hits.
- Additional Mathlib search for existing variable-ideal definitions found only
  evaluation/substitution ideals and topological bases, not this construction.

Validation: the prescribed `scompile.py` compiles the delivered file both in its
sandbox mode and at its actual library module name. After adding the tensor
notation scope, the first complete version compiled cleanly in 13.7 and 12.7 seconds.
The final positive-exponent version is checked again below by compile and delivery
preflight. No other compile method or global build was used.

## Second reading by Q43

This is an explicit self-audit; the dispatcher brief forbids starting another
agent and assigns independent review to the maintainer. I reopened the node and
Lean file and matched each hypothesis and conclusion in the table above.

The reading checked that the actual compatible-family differential module is
used, rather than a free model; the tensor order agrees with the dependency
record; no arbitrary isomorphism substitutes for the canonical completion map;
and u, delta and phi are all determined by their displayed representative
formulas. The first written power-submodule equality included exponent zero;
I restricted it to `r + 1` to follow the node's positive indexing literally.
The exponent-zero completion coordinate is harmless because it is uniquely zero.
The final compatibility uses `adicTransition`, not an unspecified transition.
No hypothesis, generator clause, descent formula, scalar restriction, or
compatibility clause is missing. No change to the natural-language node was needed.
