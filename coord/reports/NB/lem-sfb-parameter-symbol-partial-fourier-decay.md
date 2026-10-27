## Worker report

The module `Sheaf.Analysis.ParameterSymbolPartialFourierDecay` states
`EuclideanSpace.parameterSymbol_partialFourier_decay`, with its proof `sorry`.
Two concrete helper definitions expand this node's own notation:
`parameterSymbolDeriv` and `parameterSymbolPartialFourier`. No theorem is proved.
No node statement, hypothesis, proof plan, or dependency list is changed.

Hypothesis and clause correspondence:

- The fields are Mathlib's `ℝ` and `ℂ`; `EuclideanSpace` supplies the Euclidean norm,
  real inner product and canonical Lebesgue `volume`. The dependency `def-weil-field`
  is a Mathlib node with match `Field`; its class and docstring were read in
  `Mathlib/Algebra/Field/Defs.lean:180`. No project field declaration needs importing.
- `d m p q : ℕ`, `hd : 1 ≤ d`, `hm : 1 ≤ m`, and `r : ℤ` render exactly the dimensions,
  nonnegative ranks, and signed order. Matrices are continuous complex-linear maps
  `EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q)`, with operator norm,
  the same matrix convention used by the landed compact-symbol frequency kernel.
- The domain of `b` is the right-associated product of the three real Euclidean blocks
  `(x,z,ξ)`. `ContDiff ℝ ∞ b` is joint real smoothness.
- `Lx`, `Lz`, `hLx`, `hLz` introduce the two fixed compact support sets. The implication
  with `x ∉ Lx ∨ z ∉ Lz` imposes precisely vanishing outside their product, for every ξ.
- `C α γ β : NNReal` records the input bounds; the last premise quantifies over all
  α, γ, β, x, z, ξ and uses `parameterSymbolDeriv` and the integer power
  `r - (∑ j, β j : ℕ)`. Taking C nonnegative loses no case: the original inequality
  has a nonnegative left side and strictly positive frequency weight, so every
  admissible real C is already nonnegative. There is no compact ξ-support assumption.
- `parameterSymbolDeriv α γ β` differentiates in ξ, then z, then x, by repeated real
  `fderiv` evaluated on `EuclideanSpace.single j 1`. The coordinate list is explicit.
  For smooth b these commute and give exactly the node's multi-indices.
- `parameterSymbolPartialFourier` is the literal Bochner integral with
  `(2 * (Real.pi : ℂ)) ^ (-(m : ℤ))` and
  `Complex.exp (-Complex.I * (inner ℝ z η : ℂ))`. It has neither a hidden 2π in the
  phase nor a reflected frequency. The first conclusion asserts `Integrable` for
  its matrix-valued integrand at every x, η, ξ, hence absolute convergence.
- The next two conclusions give joint `ContDiff` of B and its vanishing for x outside Lx.
- The derivative equality quantifies over all α, δ, β and x, η, ξ. Its integrand
  multiplies the phase by `∏ j, (-Complex.I * (z j : ℂ)) ^ (δ j)` and by
  `parameterSymbolDeriv α 0 β b`, so only x and ξ differentiate b.
- The last conclusion is the rapid-decay estimate for every natural L (equivalently
  integer L ≥ 0). All frequency weights use real integer powers, allowing negative r.
  The finite set `Γ α δ β L` varies only the z derivative γ, retaining α and β.
- Crucially `∃ Γ K` comes before `∀ b C`. Thus Γ and the finite prefactor K depend
  only on fixed dimensions, order, support sets and indices, and work simultaneously
  for every symbol and input bound array. The explicit value
  `(K α δ β L : ℝ) * ∑ γ ∈ Γ α δ β L, (C α γ β : ℝ)` is a finite nonnegative real
  choice of C'. This renders both the existence of C' and its finite-seminorm control,
  including the stated uniformity for arbitrary families with common bounds.

Dependencies and source reading:

The only statement dependency is the Mathlib `Field` class, used via ℝ and ℂ.
Proof dependencies are imported privately through their recorded Mathlib modules:
`Continuous.integrable_of_hasCompactSupport` and `ContinuousOn.integrableOn_compact`
(`MeasureTheory.Function.LocallyIntegrable`);
`MeasureTheory.Integrable.mono'`, `norm_integral_le_of_norm_le`, `integral_add`,
`integral_smul`, and `integral_congr_ae` (`Integral.Bochner.Basic`, transitively imported);
`integral_smul_const` (`Integral.Bochner.ContinuousLinearMap`);
`StronglyMeasurable.integral_prod_right` (`Integral.Prod`);
`hasFDerivAt_integral_of_dominated_of_fderiv_le` (`Analysis.Calculus.ParametricIntegral`);
and `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`
(`Analysis.Calculus.LineDeriv.IntegrationByParts`). The corresponding node statements,
records, signatures and relevant source docstrings were read. The proof docstring
retains all six DAG proof steps, including the repeated Laplacian, the finite Leibniz
expansion, and the final weight comparison.

Demailly's course was read online at
https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf:
§2 Fourier differentiation identities (p.3), §3 (3.11) (p.9), and the estimates after
(3.15) (p.11). It supplies the method and not this full parameter statement, exactly
as the node says; the extension remains identified as the DAG's agent-written argument.

Edge cases checked before writing: p=0 and q=0 give the zero map space; empty Lx or Lz
forces b=0 and permits K=0; α=δ=β=0 makes the derivative helper the identity; L=0 has
weight one in η and permits the undifferentiated estimate; r may be negative because
1+‖ξ‖ is positive; d and m are independent and can both be 1; η=0 and ξ=0 cause no
singularity. Zero ranks and empty supports are not excluded by any binder or instance.
No statement dispute or source-based correction is needed.

Searches actually run (full service receipts are in sandbox searches.jsonl):

- LeanFinder: "Uniform partial Fourier decay for compact spatial symbol families with
  external parameters and mixed derivatives"; eight hits headed by
  `Real.pow_mul_norm_iteratedFDeriv_fourier_le` and the VectorFourier estimates.
  These do not give the whole three-parameter theorem or its common-support control.
- Loogle: `"fourierIntegral"`; twelve hits including `VectorFourier.fourierIntegral`,
  its norm bound, and `Real.vector_fourierIntegral_eq_integral_exp_smul`.
  These give the integral but not the theorem.
- Mathlib grep via msearch: `partialFourier|symbolMultiIndexDeriv|multiIndexPartialDeriv`
  in `Analysis/`; zero hits.
- LeanSearch: "Smooth compactly supported parameter family Fourier transform uniform
  rapid decay mixed derivatives"; eight hits including `SchwartzMap.fourierTransformCLM`,
  `HasCompactSupport.toSchwartzMap`, and the Fourier derivative estimates. No exact match.
- Local rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for partial Fourier, mixed symbol derivatives and the proposed names. The landed
  `CompactSymbolFrequencyKernel.lean` has two equal-dimensional blocks, no external
  parameter and no η-derivative estimate. Its `symbolMultiIndexDeriv` is consequently
  inapplicable to this three-block domain with independent d and m. The scalar
  `multiIndexPartialDeriv` in `L2WeakDerivativeFourierIdentity.lean` has scalar target
  and a single block. `cutoffCauchyParameterDeriv` is within-domain and scalar-valued.
  All three definitions were read; none supplies this node's mixed matrix derivative.
  The new helper expands only this node's missing three-block notation, as permitted
  for helpers in the owning module; no independent notion or new DAG node is introduced.
- `tools/blueprint_refs.py search 'partial Fourier'` returned zero blueprint matches;
  the ancestor is null, as inherited in the node. The proposed declaration names
  were searched in Mathlib, WeilConjectures, Sheaf and the upstream name index: no hits.

Validation: the prescribed scompile.py compiled both its sandbox and library versions
cleanly (2.5 s and 2.4 s). All variables are bound with autoImplicit false. Initial
NNReal notation elaboration was repaired by using the explicit type name `NNReal`.

## Second reading by NB

A separate rereading pass over the JSON statement and completed Lean file checked each
of the correspondences above. This is the dispatcher's single worker's own second pass,
not an independent-agent review; the prompt forbids starting other agents and assigns
the independent review to the maintainer. In particular the pass checked the product
association `(x,(z,ξ))`, the negative phase sign, normalization (2π)^(-m), the zero
middle derivative in the integral formula, β's order subtraction, and all quantifier
positions. The finite-list and K witnesses precede both b and C; this avoids losing
the last sentence's uniformity. The explicit NNReal type name was the only elaboration
repair. The node and proof plan remain unchanged; no new nodes or dependency repairs.
