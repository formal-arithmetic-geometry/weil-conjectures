## Worker report

The module `Sheaf.FieldTheory.DenseSubfieldAlgebraicRootApproximation` states
`Polynomial.exists_algebraic_root_approximation_of_denseRange`, with its proof `sorry`.
It introduces no definitions, axioms or helper theorems. The node is unchanged except for
its `lean` record. There are no new nodes, dependency repairs or statement corrections.

The source was read in the project's `WeilConjectures/NumberTheory/Padics/Extension.lean`,
lines 110–126, and Mathlib's `Analysis/Normed/Field/Approximation.lean`, lines 114–138.
The first bullet of L19, Proposition 1.1.9 on p. 3, supplies the countability motivation;
it does not itself claim this quantitative theorem. The current blueprint's paragraph (3)
of `sk-thm-sf-ctf-stability-direct-images.proof.md` was also read: the arithmetic lemma is
an intermediate input in the inherited DAG route, not that unit's own statement.

Hypothesis and clause correspondence:

- The fields `D ⊆ K ⊆ L` are `(D : Type u) (K : Type v) (L : Type w)`, `[Field D]`,
  `[NormedField K]`, `[NormedField L]`, `[Algebra D K]`, and `[NormedAlgebra K L]`.
  Field algebra maps are injective. The three universes are independent.
- The listed norm axioms and norm-induced distance are exactly `NormedField`.
  `NormedAlgebra K L` expresses the extending norm: `norm_algebraMap'` gives
  `‖algebraMap K L z‖ = ‖z‖`. Conversely, an extending multiplicative field norm
  gives its `norm_smul_le` by the algebra action formula. This adds no norm condition.
- Algebraic closedness is `[IsAlgClosed L]`, rather than an algebraic-closure or
  algebraic-extension assumption on `L/K`.
- Density is `hd : DenseRange (algebraMap D K)`. By `Metric.denseRange_iff` and
  `dist_eq_norm`, this is exactly the stated positive-radius approximation condition.
  The domain `D` needs no topology or norm.
- The monic polynomial is `(f : Polynomial K) (hf : f.Monic)`. Its positive degree is
  `(n : ℕ) (hn : 1 ≤ n) (hdegree : f.natDegree = n)`. Monic polynomials over fields
  are nonzero, so natural degree equals the node's degree here.
- The given root is `(x : L) (hx : f.eval₂ (algebraMap K L) x = 0)`.
  The radius is `(r : ℝ) (hr : 0 < r)`.
- The node's `M = max {‖x‖,1}` and `epsilon = (r/M)^n/(n+1)` are expanded as
  `max ‖x‖ 1` and `(r / max ‖x‖ 1) ^ n / (n + 1 : ℝ)` everywhere. They are
  fixed expressions, not extra arbitrary parameters or hidden local lets.
- The existential witnesses are `∃ (g : Polynomial D) (b : L)`.
  The first two conjuncts are `g.Monic ∧ g.natDegree = n`.
- The node's `h` is the canonical coefficientwise image `g.map (algebraMap D K)`.
  Its monicity and degree are the next two conjuncts. Splitting over `L` is
  `((g.map (algebraMap D K)).map (algebraMap K L)).Splits`. For this monic
  degree-n polynomial over a field, `Splits.eq_prod_roots_of_monic` and
  `Splits.natDegree_eq_card_roots` identify this with a product of n linear factors.
- All coefficient inequalities are quantified by `∀ i : ℕ` with
  `‖(g.map (algebraMap D K)).coeff i - f.coeff i‖ < (r / max ‖x‖ 1)^n/(n+1)`.
  This includes the leading coefficient and every coefficient above the degree.
- `h(b)=0` is the first `eval₂` conjunct; `g(b)=0` is the next conjunct using
  `((algebraMap K L).comp (algebraMap D K))`. Both evaluations use exactly the
  coefficient maps prescribed by the node, without an unrelated `Algebra D L` instance.
- The strict distance bound is `‖x - b‖ <` the expanded expression
  `((n+1)*epsilon) ^ (n : ℝ)⁻¹ * max ‖x‖ 1`. The following equality sets that
  same bound equal to `r`. Thus the entire displayed chained inequality/equality is kept.
- The last conjunct is `@IsAlgebraic D L _ _` with
  `((algebraMap K L).comp (algebraMap D K)).toAlgebra`, precisely algebraicity over
  `D` for the composite inclusion. There is no completeness, separability,
  characteristic-zero, nontrivial-norm or norm-on-D assumption.

Dependency declarations, with signatures and surrounding docstrings read:

- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  as explicitly listed in this mathlib leaf's `mathlib_match`.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`.
- `def-weil-polynomial-root`: `Polynomial.eval₂`, `Mathlib.Algebra.Polynomial.Eval.Defs`.
- `def-weil-algebraic-element`: `IsAlgebraic`, `Mathlib.RingTheory.Algebraic.Defs`.
- Proof leaf `lem-sfb-monic-dense-approximation`:
  `Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt`,
  `Mathlib.Analysis.Normed.Field.Approximation`.
- Proof leaf `lem-sfb-roots-coefficient-proximity`:
  `Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt`, in the same module.
- Proof leaf `lem-weil-alg-closed-linear-factorization`:
  `Polynomial.Splits.eq_prod_roots`, `Mathlib.Algebra.Polynomial.Splits`, available
  publicly through `Mathlib.FieldTheory.IsAlgClosed.Basic` (and used by the statement's
  splitting predicate). No extra proof import of that already-public module is necessary.

The additional public imports give the normed algebra structure and real powers in the
statement. The approximation module is a plain proof import. In module mode its private
real-power imports do not expose the `HPow ℝ ℝ` instance: the initial compile diagnosed
that omission, and `public import Mathlib.Analysis.SpecialFunctions.Pow.Real` repaired it.
The final standalone sandbox and library module compiles both passed without warnings.

Edge cases checked before writing: `n=1` gives the ordinary first-root bound, and `n=0`
is explicitly excluded by the node. A root at `x=0` has `M=1`, so no division by zero
occurs. For `D=K`, taking `g=f` and `b=x` satisfies the coefficient and distance bounds.
In a trivial norm the small-radius case forces equality as expected; no nontrivial-norm
hypothesis is present. Positive characteristic and inseparable polynomials are allowed:
no separability is needed for splitting with multiplicities. The zero polynomial is
excluded by monicity. Coefficients beyond degree n are both zero and satisfy the strict
bound because epsilon is positive. All three field universes remain arbitrary.

Searches for an existing full statement (2026-10-24):

- `msearch.py leanfinder "dense subfield algebraic root approximation"`: eight hits,
  including Liouville, primitive-element, root-existence and algebraic-closure results;
  none supplies the tolerance, same-degree polynomial and all the requested clauses.
- `msearch.py loogle "Polynomial.Monic, DenseRange"`: the single result is
  `Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt`,
  which is only the coefficient-approximation proof leaf.
- `msearch.py leansearch "Approximate a root over a normed field by algebraic elements
  over a dense subfield"`: eight hits, including `isAlgebraic_of_mem_rootSet` and
  `IsAlgClosed.exists_root`; no full match.
- `msearch.py grep "exists_aroots_norm_sub_lt|exists_monic_and_natDegree|of_denseRange"`
  in `Analysis/Normed/Field`: nine hits in `Approximation.lean` and `Dense.lean`.
  The first contains the two separate proof inputs. `IsAlgClosed.of_denseRange` assumes
  an algebraically closed dense base and concerns closedness of a different field.
- A preliminary wrapper grep for `dense.*subfield|algebraic.*root.*approx` with
  subdirectory `WeilConjectures` returned zero hits. Direct `rg` of `lean/WeilConjectures`
  and `lean/Sheaf` for dense-subfield/algebraic-root variants found the p-adic special
  case in `Extension.lean` and `RationalAlgebraicGenerator.lean`, not the general theorem.
  The item-id search of `lean/WeilConjectures` returned no occurrence.
- `rg` for the proposed full declaration name in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` returned no occurrence.

No statement dispute or node fault was found. The five natural-language proof steps are
preserved in the theorem docstring, including tolerance positivity, coefficient
approximation, monicity/degree and splitting, nearby-root estimate, and composite
evaluation/algebraicity. Only the intended theorem is postponed.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
