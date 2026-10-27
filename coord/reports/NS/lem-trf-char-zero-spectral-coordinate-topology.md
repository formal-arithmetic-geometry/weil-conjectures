## Worker report

The module `Sheaf.Analysis.Normed.SpectralNormCoordinateBounds` states
`Module.Basis.spectralNorm_coordinate_bounds` with one postponed proof. It introduces no
definitions. The node's statement, dependency lists, and proof are unchanged.

Hypothesis and conclusion correspondence:

- The field K with its real-valued, multiplicative, nontrivial absolute value is
  `{K : Type u} [NontriviallyNormedField K]`. This class extends `NormedField`, hence
  `Field`; its nontriviality condition is existence of an element of norm greater than one.
  A multiplicative absolute value gives exactly this normed-field structure via
  distance `|x-y|`, so bundling that structure imposes no extra mathematical hypothesis.
- Characteristic zero is `[CharZero K]`, and nonarchimedeanness is `[IsUltrametricDist K]`.
- A finite field extension L/K is `{L : Type v} [Field L] [Algebra K L]
  [FiniteDimensional K L]`. No topology or norm is imposed on L.
- Every K-basis is `{ι : Type w} [Fintype ι] (b : Module.Basis ι K L)`.
  Arbitrary finite indexing covers the displayed indices 1,...,d by reindexing, and
  the index universe is independent of the field universes. A finite-dimensional
  space has only finite bases, so this encoding loses none of the bases in the node.
- The constants are `∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ...`; they may depend on the basis
  and extension, but are chosen before `∀ a : ι → K`.
- The coordinate maximum is `‖a‖`. Mathlib's `Pi.norm_def` identifies it with
  `↑(Finset.univ.sup fun i => ‖a i‖₊)`. Thus it is precisely `max_i |a_i|`,
  not a sum norm or a norm chosen on L.
- The element with coordinates a is `∑ i, a i • b i`.
- The minimal-polynomial spectral norm is the existing `spectralNorm K L`.
- The lower inequality is `c * ‖a‖ ≤ spectralNorm K L (∑ i, a i • b i)`;
  the upper inequality is `spectralNorm K L (∑ i, a i • b i) ≤ C * ‖a‖`.
  Their conjunction lies under the same coefficient quantifier.
- There is no `CompleteSpace K`, separability, normality, or auxiliary norm hypothesis.

Dependency declarations read and used:

- `def-weil-field`: Mathlib's `Field`,
  `Mathlib.Algebra.Field.Defs`, supplied through `NontriviallyNormedField` and `Field L`.
- `lem-trf-incomplete-spectral-algebra-norm`: the recorded Mathlib match in
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`, publicly imported.
  `spectralNorm` is defined as `spectralValue (minpoly K z)`; `spectralValueTerms`
  and `spectralValue` give the coefficient maximum. `spectralAlgNorm`,
  `spectralAlgNorm_def`, `isNonarchimedean_spectralNorm`, and `spectralNorm_one`
  give exactly the norm axioms named by the dependency. Their signatures do not
  require completeness. Finite-dimensionality supplies algebraicity when needed.
- `lem-trf-field-trace-minpoly-coefficient`: the Mathlib match
  `trace_eq_finrank_mul_minpoly_nextCoeff` in `Mathlib.RingTheory.Trace.Basic`.
- `lem-trf-char-zero-trace-dual-basis`: the Mathlib matches
  `Module.Basis.traceDual` and `Module.Basis.trace_mul_traceDual` in that same module.
  This module is imported without `public` because both trace lemmas are proof inputs.
  Separability for the dual basis follows from characteristic zero; it is not added
  as a hypothesis. The theorem docstring carries the full four-step trace-dual proof.
- `Mathlib.Analysis.Normed.Group.Constructions` supplies the finite-product norm used
  to state the coordinate maximum; its instance and `Pi.norm_def` were read.

Edge cases checked before writing:

- All coefficients zero: both sides reduce to zero since `spectralNorm_zero` holds.
- Dimension one, including L=K and a rescaled basis: the spectral norm extends the
  base absolute value; the two constants can be chosen equal to the norm of that
  basis vector. The statement permits these constants to depend on the basis.
- Empty index: no basis of the nonzero field L has an empty index type. No extra
  `[Nonempty ι]` assumption is needed, and the Pi norm remains defined for all indices.
- Incomplete K is explicitly included; no complete-base norm-equivalence API is used.
- Characteristic zero excludes the inseparable trace-pairing obstruction. A trivial
  base absolute value is excluded exactly as in the node, by NontriviallyNormedField.
- Arbitrary, independent universes u, v, w are explicitly declared and all variables
  are explicitly bound. No arbitrary extension norm or canonical-norm choice is added.

Searches for existing statements (prescribed `msearch.py`, group NS and this item):

- LeanFinder: "Over an incomplete nonarchimedean field of characteristic zero the
  minimal polynomial spectral norm on a finite field extension is equivalent to the
  maximum absolute value of coordinates in any basis". Eight hits, including
  `spectralNorm_eq_invariantExtension`, `spectralNorm_extends_of_finiteDimensional`,
  `spectralAlgNorm_def`, and `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`.
  None is the two-sided coordinate bound; the coefficient-zero formula requires
  completeness and the invariant-extension identity concerns normal extensions.
- LeanSearch: "spectral norm finite extension characteristic zero equivalent to
  coordinate norm without completeness". Eight hits, including `spectralNorm`,
  `spectralAlgNorm`, `spectralNorm_unique`, and `spectralNorm.normedSpace`.
  The first two supply the existing function and algebra norm, while the last two
  require completeness and do not state the requested bounds.
- Loogle: `"spectralNorm"`. Twelve hits, including the defining function and norm
  axioms; normed-field/metric-space constructions require `[CompleteSpace K]`.
  None states this node.
- Mathlib grep in `Analysis/Normed`:
  `spectralNorm.*(basis|coord|equiv)|weak.?cartesian|weakly.?stable`.
  Four hits in Krasner/SpectralNorm concerning invariance under field automorphisms,
  not coordinate equivalence.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `spectralNorm.*(coordinate|basis|equiv)|weak.?cartesian|weakly.?stable`.
  No coordinate-bound theorem; the Sheaf hits are p-adic coefficient constructions
  using equality with the complete-base spectral norm.
- Exact blueprint-id grep in `lean/WeilConjectures`: no hits.
- Proposed full declaration name searched in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`: no hits.

The current blueprint unit and local-term lemma were read; the node records this
as historical analytic input below that unit, not the unit's own statement. The
BGR source PDF is absent from the read clone, as already recorded by stage 1;
no source correction is needed. The recorded Mathlib source and the node's
explicit trace-dual proof determine the statement without importing a complete-base
normed-field construction. No node fault or statement dispute was found.

Validation: the prescribed `scompile.py` wrapper compiled the delivered file cleanly
in both its sandbox and library module contexts (exit code 0, no warnings). The
prescribed `deliver2.py --no-push` dry run and delivery follow this compile. There is
one file and one named `sorry`, namely the theorem recorded above.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
