## Worker report

The module `Sheaf.Paper.EvenTensorPositivity` states
`AlgebraicGeometry.WeilSheaf.isReal_tensorPower_and_even_nonneg`, with one `sorry` proof.
It introduces no definitions and changes only the item's `lean` record. The source is the
current main-20261015 blueprint, sec-purity-real-sheaves/sk-p-real-rankin,
lem-rp-even-tensor-positivity.md and its proof; its two clauses agree with the node.

Hypothesis and clause correspondence:

- The global coefficient convention is `{l : ℕ} [Fact l.Prime]`, with a finite field
  `{k₀ : Type u} [Field k₀] [Finite k₀]` and `[Fact (ringChar k₀ ≠ l)]`.
  Thus the coefficient prime differs from the finite field's characteristic. The chosen
  algebraic closure of the coefficient field is the existing `PadicAlgCl l`.
- The scheme over the finite field is `{X : Scheme.{u}}` with
  `[X.Over (Spec (CommRingCat.of k₀))]`. Its structure morphism has `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` instances. The last two together mean finite
  type, as fixed by def-weil-pbc-scheme-conventions. No smoothness, curve, connectedness,
  normality, nonemptiness, or irreducibility hypothesis occurs.
- The chosen coefficient isomorphism is `(ι : PadicAlgCl l ≃+* ℂ)`; `ι.toRingHom` is used
  to apply it to coefficients. It carries no continuity assumption.
- The sheaf is `(G : WeilSheaf k₀ l X)`, the existing constructible pro-etale Weil sheaf,
  with `(hG : G.IsLisse)` and `(hreal : G.IsReal ι.toRingHom)`.
- Every closed point is `(x : X.finitePoints)`. These are exactly closed points for a
  scheme of finite type over a finite field: finite residue fields give closed points
  (`Scheme.isClosed_singleton_of_mem_finitePoints`), and a closed point's residue field is
  finite over the finite base (`Scheme.Hom.finite_residueField_of_isClosed`).
- Every positive tensor exponent is `(k : ℕ) (hk : 1 ≤ k)`. The actual sheaf tensor power is
  `Nat.iterate (fun H => G.tensorObj H hG) (k - 1) G`. At k=1 it is G, at k=2 it is
  G.tensorObj G hG, and each further iteration tensors once with G. The fixed first
  argument is lisse, so every iteration is defined without assuming any extra property
  of the previously constructed tensor power. `tensorObj` is tensor over the continuous
  coefficient sheaf, with its canonical Weil structure. This directly uses the existing
  tensor operation and adds no new notion or auxiliary data.
- Clause (i) is the first conjunct:
  `((Nat.iterate ... (k - 1) G).stalk x).IsReal ι.toRingHom`.
  `FrobeniusModule.IsReal` means that conjugation fixes every coefficient of the mapped
  local polynomial, equivalently all its coefficients are real. `localPolynomial` is
  `frobeniusEnd.charpolyRev`, hence det(1-tF_x), not det(t-F_x).
- Clause (ii) is guarded by `Even k`. Its first conjunct quantifies over every `n : ℕ`
  and states `0 ≤ PowerSeries.coeff n` of the inverse of the mapped local polynomial
  embedded in complex formal power series. With `open scoped ComplexOrder`, this means
  that the coefficient has imaginary part zero and nonnegative real part; it does not
  merely bound the real part of an arbitrary complex coefficient. The polynomial has
  constant coefficient 1, so its formal inverse is exactly the specified reciprocal
  local factor. Mapping the polynomial first and then inverting gives the same series
  as coefficientwise mapping its inverse, by uniqueness of the inverse. There is no
  substitution t ↦ t^(degree x) in this statement.
- The second conjunct under `Even k` is `PowerSeries.constantCoeff (...) = 1`, precisely
  the constant-term clause. It is also included among the nonnegative coefficients at n=0.

Dependency declarations read and used:

- def-wf-iota-real: recorded module `WeilConjectures.WeilSheaf.Stalk`, recorded name
  `AlgebraicGeometry.WeilSheaf.IsRealizable`; its definition refers to
  `AlgebraicGeometry.WeilSheaf.IsReal` in the same module. The latter is the reality
  hypothesis used here. `WeilSheaf.stalk`, in that module, constructs the canonical
  geometric stalk and its local geometric Frobenius.
- `WeilConjectures.WeilSheaf.Category`: `AlgebraicGeometry.WeilSheaf` and
  `AlgebraicGeometry.WeilSheaf.IsLisse`, imported through Stalk/Tensor. The former is the
  existing constructible sheaf category and the latter says its underlying adic sheaf
  is locally finite free.
- def-real-weil-representation-operations: the recorded live module
  `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra`, declarations
  `AlgebraicGeometry.WeilGroup.detLine` and `semisimplification`, was read through
  `scompile.py --source` because it is absent in the older local checkout. Its operations
  docstring explicitly lists `Representation.tprod` as the ordinary tensor action.
  The sheaf-level tensor used in the signature is
  `AlgebraicGeometry.WeilSheaf.tensorObj` from `WeilConjectures.WeilSheaf.Tensor`;
  its docstring and full definition were read locally and confirmed with `--source`.
- def-weil-pbc-scheme-conventions is a convention record, with no own declaration;
  the Mathlib properties used here are `AlgebraicGeometry.IsSeparated`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and `AlgebraicGeometry.QuasiCompact`.
- def-wf-weil-category: `Sheaf.Paper.PbcWeilCategory`, `WeilConjectures.WeilDQbar` and
  `WeilConjectures.WeilD`, were read and the recorded module is imported. This item is
  about lisse Weil sheaves, whose sheaf/stalk/reality interfaces are already in the
  recorded def-wf-iota-real module; its conclusion does not use derived morphisms or
  assert an identification of derived-category models.
- Proof imports: p-linear-spectra uses `LinearMap.charpoly_roots_tensorProduct` from
  `WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic`; p-linear-triangular uses
  `Module.End.exists_le_map_le_finrank_eq_succ` from
  `WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable` (over an algebraically
  closed field); lem-weil-exp-trace-determinant uses `LinearMap.inv_charpolyRev_eq_exp`
  from `WeilConjectures.ZetaLinearAlgebra.DetTrace`; def-weil-power-series-exponential
  uses Mathlib `PowerSeries.exp` from `Mathlib.RingTheory.PowerSeries.Exp`. These were
  read with their context and docstrings; the proof is supplied step by step in the
  theorem's docstring.
- Iteration uses the existing Mathlib `Nat.iterate`; complex nonnegativity uses
  `Complex.partialOrder` and `Complex.nonneg_iff` from `Mathlib.Analysis.Complex.Order`.

Edge cases checked before the statement was written:

- An empty scheme has no x; the assertion is vacuous and has no Nonempty hypothesis.
- A zero stalk has local polynomial 1; its inverse is 1, so all coefficients are
  nonnegative and the constant term is 1.
- At k=1 the iterate has zero repetitions and gives G. Positivity is correctly
  conditional: a rank-one real Frobenius eigenvalue -1 gives inverse 1/(1+t), with a
  negative linear coefficient. At k=2 that eigenvalue becomes 1, giving 1/(1-t).
- For a conjugate pair i,-i and k=2, the tensor eigenvalues are -1,1,1,-1; the inverse
  factor is (1-t²)^(-2), whose coefficients are nonnegative. The original eigenvalues
  need not individually be real or positive.
- A nontrivial Jordan block changes neither the eigenvalue-multiset reasoning nor the
  trace formula; no semisimplicity hypothesis was introduced.
- k=0 is excluded exactly by the node's k≥1. Natural subtraction is only used under
  this hypothesis. At n=0 the claimed inverse coefficient is 1.
- The scheme universe u is explicit and arbitrary; no accidental equality with the
  coefficient or stalk universe is imposed.

Searches for an existing statement:

- `msearch.py ... leanfinder` query: "Even tensor powers of a real Weil sheaf have real
  characteristic polynomials and nonnegative inverse local factor coefficients".
  Eight hits: DirichletCharacter.zetaMul_nonneg, DirichletCharacter.Even.gammaFactor_def,
  ZMod.LFunction_apply_zero_of_even, ZMod.LFunction_neg_two_mul_nat_add_one,
  ValueDistribution.characteristic_even, WeakFEPair.hε, spectralValueTerms_nonneg,
  DirichletCharacter.Even.LFunction_neg_two_mul_nat. None states this result.
- `msearch.py ... loogle 'PowerSeries, Matrix.charpoly'`: zero hits.
- `msearch.py ... grep 'HasNonnegCoeffs|tensorPower.*IsReal|IsReal.*tensorPower'`:
  zero hits in Mathlib.
- `msearch.py ... leansearch` query: "Even tensor powers of a real Weil sheaf have
  nonnegative inverse characteristic polynomial coefficients". Eight hits, including
  Even.pow_nonneg, Even.zpow_nonneg, exteriorPower.toTensorPower_apply_ιMulti and
  Matrix.IsHermitian.roots_charpoly_eq_eigenvalues₀; none gives the sheaf statement.
- `rg` in upstream WeilConjectures for tensor powers, positivity, reality and charpolyRev,
  and the required search for the node id, found
  `WeilGroup.IsReal.hasNonnegCoeffs_eulerFactor_tprod_self` in RealSheaves/Rankin.lean.
  Its full signature and docstring were read: it only treats tensor squares of Weil
  representations on curves and substitutes t^(degree x). It does not supply this
  node's arbitrary separated finite-type scheme, all k≥1, and both explicit clauses.
- `rg` in shared lean/Sheaf for tensor powers, tensor positivity and the candidate
  declaration name found no equivalent theorem or sheaf tensor-power definition.
  Existing derived-tensor statements use a different level of objects and do not
  duplicate the expression of ordinary positive tensor powers used here.

Validation: `scompile.py Q06 lem-rp-even-tensor-positivity` compiled the sandbox and
library-path forms of the delivered file cleanly (15.9 s and 8.2 s). No warning or error.
There is no statement dispute, statement correction, new node, or dependency repair.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
