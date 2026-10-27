## Worker report

The module `Sheaf.RingTheory.MonoidCompletionCoefficientEmbedding` states
`AddMonoidAlgebra.monoidCompletion_coefficientEmbedding`, with one `sorry` and
no definitions. The node is unchanged outside `lean`; no dependency repairs,
new nodes, or statement corrections are needed.

Source read: ILO, Travaux de Gabber, Exposé VI §1.6(i)–(ii), printed p. 70,
PDF p. 76. This gives the completed monoid models in equal and mixed
characteristic, not this general algebra lemma. The node explicitly identifies
its coefficient argument as agent-written auxiliary algebra. I also read the
current blueprint's `lem-trf-local-term-locality.proof.md`, which explains the
ancestry via contracting correspondences; it does not assert this algebra lemma.
The eight-step proof docstring follows the item's eight recorded proof steps.

Hypotheses and introduced objects, clause by clause:

- `r : ℕ` includes every nonnegative integer, including zero.
- `Q : AddSubmonoid (Fin r →₀ ℕ)` is the specified additive submonoid of
  exponent vectors. Since `Fin r` is finite, finitely supported functions here
  are canonically all vectors in `ℕ^r`, with the same addition and degree.
- `L : Type u`, `[CommRing L]`, and `a : Ideal L` impose exactly the coefficient
  ring and ideal hypotheses, without local, domain, Noetherian, finite generation,
  nontriviality, or finiteness assumptions.
- `AddMonoidAlgebra L Q` is the finite monomial-sum ring `B=L[Q]` with its
  existing multiplication. `MvPowerSeries (Fin r) L` is the specified `A`.
- `J` and `hJ` name exactly `aB + (z^q | q ≠ 0)` using `Ideal.map`, ideal
  supremum, and `Ideal.span` of nonzero monomials. `q ≠ 0` in the subtype
  is equivalent to its underlying vector being nonzero.
- `I` and `hI` name exactly `aA + (X_1,...,X_r)` using the same ideal operations
  and `Set.range MvPowerSeries.X`. These equalities specify the ideals, rather
  than allowing arbitrary ideals with stronger filtration properties.
- `j` and `hj` specify the canonical monomial algebra map. The equation for
  every `single q c` determines its values on every finite sum by additivity.
  Thus it is exactly the displayed map, not an unspecified embedding. Such a
  map exists for every input: the monoid map sends `q` to `monomial q.1 1`
  and extends by `AddMonoidAlgebra.lift`. The monomial multiplication formula
  verifies the monoid law without any additional hypothesis.
- `hcomplete : Function.Bijective (AdicCompletion.of a L)` is literally the
  required bijectivity of the canonical coefficient-completion map.
- `hmap : J ≤ Ideal.comap j.toRingHom I` is precisely `j(J) ⊆ I`.
- `hcofinal` says for each `n : ℕ` that there is `N : ℕ` with `n ≤ N` and
  `Ideal.comap j.toRingHom (I ^ N) ≤ J ^ n`, including the case `n=0`.
- `AdicCompletion J (AddMonoidAlgebra L Q)` is `T`; `AdicCompletion.of J _`
  is `η`; `AdicCompletion.evalₐ J n` is projection to `B/J^n`.
- The explicit topology `⨅ n, TopologicalSpace.induced
  (AdicCompletion.evalₐ J n) ⊥` is the initial topology for all projections
  to discrete quotients (`⊥` is discrete in the topology lattice). The kernels
  form a descending family by compatibility, so finite intersections reduce
  to a kernel at the maximum index. Hence its basic zero-neighborhoods are
  exactly the stated `P_n`, not the powers of an extended ideal. The target
  topology is explicitly `I.adicTopology`, with basis `I^n`.

Conclusions, clause by clause:

- `∃ ι : T →ₐ[L] A` supplies an actual `L`-algebra homomorphism.
- The first conjunct is `Continuous` with both topologies supplied explicitly.
- The second conjunct, `∀ b, ι (AdicCompletion.of J _ b) = j b`, is `ιη=j`.
- The third conjunct quantifies every `L`-algebra map `g`, assumes only its
  continuity and its extension equation, and concludes `g=ι`. Uniqueness is
  not restricted to maps satisfying the additional coefficient conclusions.
- `Function.Injective ι` is the asserted injectivity.
- For every `x` and `f : ℕ → B`, the premise
  `∀ n, Ideal.Quotient.mk (J ^ n) (f n) = AdicCompletion.evalₐ J n x`
  means exactly that each `f n` is a representative of its nth coordinate.
- For every `e` and every candidate `c : L`, the displayed equivalence says
  that all differences `c - MvPowerSeries.coeff e (j (f n))` belong to `a^k`
  for `1 ≤ k` and `k + e.degree ≤ n` if and only if
  `c = MvPowerSeries.coeff e (ι x)`. This expresses both the congruences and
  their characterization of a unique coefficient. Since it quantifies every
  representative family and refers to the same `ι x`, it also states
  independence from all choices of representatives.
- `∀ n, ι x - j (f n) ∈ I ^ n` is the approximation at every level,
  without restricting to positive `n`.
- `Filter.Tendsto (fun n ↦ AdicCompletion.of J _ (f n)) Filter.atTop
  (@nhds _ <the initial topology> x)` states `η(f_n) → x` in the exact
  specified topology.
- The next conjunct `∀ n x, AdicCompletion.evalₐ J n x = 0 → ι x ∈ I ^ n`
  is exactly `ι(P_n) ⊆ I^n`.
- `∀ x e, e ∉ Q → MvPowerSeries.coeff e (ι x) = 0` is support containment.
- `(⨅ n : ℕ, I ^ n) = ⊥` is `⋂_n I^n=0` as an equality of ideals.

Dependency declarations used and sources inspected:

- `def-weil-pbc-multivariate-power-series`: recorded module
  `Mathlib.RingTheory.MvPowerSeries.Basic`, declaration `MvPowerSeries`.
  Read its definition and docstring at lines 84–87, the coefficient and monomial
  maps at lines 128–138, their multiplication formula at line 319, and the
  algebra structure at line 777. No private power-series definition is introduced.
- `def-weil-pbc-adic-completion`: recorded module
  `Mathlib.RingTheory.AdicCompletion.Basic`, declaration `AdicCompletion`.
  Read the compatible-sequence definition and docstring at lines 166–174, and
  `AdicCompletion.of` at lines 363–367. The public import of
  `Mathlib.RingTheory.AdicCompletion.Algebra` supplies this dependency and the
  ring/algebra structures at lines 97–114, projection `evalₐ` at lines 128–137,
  and the canonical-map/projection formula at lines 153–157.
- Proof dependency `lem-weil-pbc-power-series-combined-ideal-coefficients`:
  `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`, theorem
  `power_series_mem_combined_ideal_pow_iff`; read its full signature and proof
  docstring. Imported without `public`, as required for a proof dependency.
- Supporting existing APIs: `AddMonoidAlgebra` and its algebra structure,
  `single`, and `lift` in `Mathlib.Algebra.MonoidAlgebra.Basic`; and
  `Ideal.adicTopology`, with `hasBasis_nhds_zero_adic`, in
  `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology` at lines 86–107.

Edge cases checked before writing:

- `r=0`: the only exponent is zero, `Q` is the zero monoid, the variable ideal
  and nonzero-monomial ideal vanish, and the result reduces to completion of
  `L` along `a`. No positive-rank assumption occurs.
- `Q={0}` at arbitrary rank: only constant coefficients can occur. The
  cofinality hypothesis remains exactly the given one.
- `n=0`: `J^0=B`, `I^0=A`, and `B/J^0` is the zero ring. Kernel and
  approximation conclusions are automatic, but are still included.
- `a=⊥`: bijectivity and coefficient congruences become ordinary equality.
  `a=⊤`: the bijectivity hypothesis forces a subsingleton coefficient ring;
  the result still includes that case. No `Nontrivial L` is imposed.
- There is no requirement that `Q` be finitely generated or saturated. The
  topology on `T` is not silently replaced by extended-ideal powers.
- Coefficient universe `u` is arbitrary; exponent vectors lie in `Type 0`,
  as they should for finitely many natural-valued coordinates. Every binder
  and universe is explicit; there are no file-local definitions or notation.

Searches performed (all msearch invocations use group Q53 and this item):

- LeanFinder: "Over an adically complete coefficient ring coefficient limits
  define a unique continuous injective algebra map from a cofinally filtered
  monoid algebra completion into multivariate power series". Returned
  `MvPowerSeries.aeval_unique`, `PowerSeries.aeval_unique`,
  `MvPowerSeries.eval₂_unique`, `IsAdicComplete.liftAlgHom`, and evaluation
  constructions. None states this result for an arbitrary monoid subalgebra.
- Loogle: `AdicCompletion, MvPowerSeries`. Returned the ten declarations for
  `MvPowerSeries.toAdicCompletion`, `toAdicCompletionInv`, and
  `toAdicCompletionAlgEquiv`, with their coefficient formulas. The inspected
  equivalence in `MvPowerSeries/Equiv.lean:344` is for the variables ideal
  of the full polynomial ring, not this combined ideal or submonoid.
- LeanSearch: "Completion of a monoid subalgebra embeds into formal power
  series by coefficient limits". Returned polynomial-to-series maps,
  `MvPolynomial.toMvPowerSeries_isDenseInducing`, and `AdicCompletion.subalgebra`;
  no exact statement.
- msearch grep: `liftAlgHom|adicTopology|coeff.*[Cc]ompletion`, in `RingTheory`.
  Returned localization and general adic-completion lifts. These are supporting
  APIs, not the theorem with the cofinal filtration and coefficient conclusions.
- Direct `rg` of Mathlib's adic-completion, multivariate-series, monoid-algebra,
  and adic-topology files located the definitions and signatures listed above.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `monoid.*([Ee]mbed|[Cc]ompletion)|monomial.*[Aa]lgHom|MonoidCompletion|monoidCompletion|coefficientEmbedding`
  found `monoidCompletion_coefficients`, formal-monoid dimension, and related
  local-model modules. Read `MonoidCompletionCoefficients.lean`: its theorem
  assumes a Noetherian local coefficient ring and finite generation of the
  monoid; it is not the present coefficient embedding. There is no exact match.
- `grep -rn` for the item id in `lean/WeilConjectures` found no declaration.
  Name collision search in `dag/lean_names_upstream.json`,
  `lean/WeilConjectures`, and `lean/Sheaf` found no declaration named
  `monoidCompletion_coefficientEmbedding` before creating this module.

Validation: prescribed `scompile.py` compiled both the sandbox and canonical
library module cleanly (2.0 s and 1.8 s), with no errors or warnings.

## Second reading by Q53

A separate pass by the same dispatched worker, with the node and final Lean
signature open; no independent agent was started, as the dispatch brief forbids it.
I checked `hJ` and `hI` against the two generator formulas and checked `hj` on
all monomials with arbitrary coefficient, ensuring it fixes the entire map.
`hcomplete`, `hmap`, and `hcofinal` retain exactly the three assumptions in the
node. I checked the discrete initial topology against the coordinate kernels,
and the target adic topology against `I^n`, specifically avoiding a finite
 generation assumption. The uniqueness quantifier ranges over every continuous
extension, and the representative quantifier ranges over every compatible
representative family. The coefficient equivalence includes both the stated
residues and uniqueness of their value, with precisely `k ≥ 1` and
`n ≥ k + |e|`. Approximation, kernel-image containment, support containment,
convergence, and separation are separate explicit conjuncts. The zero-rank,
zero-level, and zero-ring cases remain included. No mismatch was found, and
no statement or dependency change was made during this second pass.
