## Worker report

The module `Sheaf.Analysis.EuclideanFixedSupportRellich` states
`MeasureTheory.euclidean_fixed_support_rellich`, with its sole proof `sorry`.
It introduces no definitions, additional nodes, or dependency replacements.
The node is unchanged except for its `lean` attachment.

Source read: Demailly, *Differential and pseudodifferential operators on manifolds*,
§2, equation (2.1) and the subsequent integer-order norm comparison, p.3;
Lemma 2.7 and its fixed-support Euclidean proof, pp.5–6, at orders one and zero.
The PDF is the supplemental source already recorded by the node:
https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf .
Its Fourier equicontinuity, Ascoli extraction, and ball/tail argument agree with
all six steps of the accepted split, reproduced in the declaration docstring.
The node's primary reference is Demailly, *Complex Analytic and Differential
Geometry*, VI §2, Rellich lemma (2.2), printed p.289.

Clause-by-clause rendering:

| Node clause | Lean rendering |
| --- | --- |
| Over the real field | The explicit scalar `ℝ`; its standard Mathlib `Field` instance, already used by `EuclideanSpace`, `Lp`, and `fderiv`. No arbitrary field or extra field hypothesis. |
| Integers `m ≥ 1`, `r ≥ 0` | `(m r : ℕ) (hm : 1 ≤ m)`. There is no positivity assumption on `r`. |
| Euclidean domain and target | `EuclideanSpace ℝ (Fin m)` and `EuclideanSpace ℝ (Fin r)`, with their Euclidean norms, rather than the supremum norm on unwrapped function types. |
| Compact set `K ⊆ ℝ^m` | `(K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K)`. |
| Lebesgue measure | `(volume : Measure (EuclideanSpace ℝ (Fin m)))`, the standard volume normalized by orthonormal bases. |
| Sequence of measurable functions modulo a.e. equality, with finite squared norms | `f : ℕ → Lp (EuclideanSpace ℝ (Fin r)) 2 volume`. An `Lp` element is an a.e. equivalence class of a.e. strongly measurable functions with finite `eLpNorm`; in finite-dimensional real target this represents exactly the Lebesgue-measurable square-integrable classes. The energy hypothesis in the node already requires each function to be in `L²`, so this type adds no assumption. |
| Every term vanishes a.e. off `K` | `hsupport : ∀ n : ℕ, ∀ᵐ x ∂volume, x ∉ K → f n x = 0`. Only an a.e. condition is imposed, not pointwise compact support of the chosen representative. |
| First distributional derivatives belong to `L²` | `d : ℕ → Fin m → Lp (EuclideanSpace ℝ (Fin r)) 2 volume`, together with `hweak` identifying these representatives as the actual first weak derivatives. Presenting a choice of derivative representatives as input is equivalent to the asserted existence of these `L²` derivatives; the theorem is valid for every such choice. |
| Compactly supported smooth scalar tests | `∀ (n : ℕ) (j : Fin m) (φ : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ...`. All smooth compactly supported tests are quantified, with no fixed support restriction on the tests. |
| Weak derivative identity including its minus sign | `(∫ x, φ x • d n j x) = -(∫ x, (fderiv ℝ φ x (EuclideanSpace.single j 1)) • f n x)`. `EuclideanSpace.single j 1` is the standard coordinate unit vector, so `fderiv` applied to it is `∂ⱼ φ`. Equality in the finite-dimensional target is equivalent to all componentwise distribution identities. The Bochner integrals are well defined: each test and each first test derivative is bounded and compactly supported, hence `L²`; Cauchy–Schwarz makes its product with an `L²` representative integrable. Thus total-integral conventions cause no vacuity. |
| Finite supremum of squared `L²` function and derivative norms | `hbounded : ∃ M : ℝ, ∀ n : ℕ, ‖f n‖ ^ 2 + ∑ j : Fin m, ‖d n j‖ ^ 2 ≤ M`. For the standard `Lp` norm at exponent two, its square is the integral of the squared Euclidean norm. Existence of a real common bound is precisely finiteness of the displayed supremum; no positivity or prescribed constant is added. |
| Strictly increasing subsequence of indices | `∃ (a : ℕ → ℕ) ..., StrictMono a ∧ ...`. Indexing from zero rather than one is the harmless relabeling `f n = f_original (n+1)`; `a k + 1` supplies the original positive indices. No term is omitted from the input sequence. |
| An `L²` limit with the same support | The existential `g : Lp (EuclideanSpace ℝ (Fin r)) 2 volume` and `(∀ᵐ x ∂volume, x ∉ K → g x = 0)`. |
| Norm convergence of the extracted sequence | `Tendsto (fun k : ℕ => ‖f (a k) - g‖) atTop (𝓝 0)`. This is exactly convergence in the node's `L²` norm. |

Dependency declarations read and used:

- Statement dependency `def-weil-field` is the Mathlib leaf `Field` in
  `Mathlib.Algebra.Field.Defs`, whose full declaration extends `CommRing` and
  `DivisionRing`. Its docstring and the current blueprint's `def-weil-field`
  statement were read. The standard real field enters through the public
  Mathlib imports; no extra Lean record is needed for the leaf.
- `MeasureTheory.Lp` and `MeasureTheory.Lp.norm_def` in
  `Mathlib.MeasureTheory.Function.LpSpace.Basic` supply the quotient and norm.
- `EuclideanSpace`, `EuclideanSpace.single` in
  `Mathlib.Analysis.InnerProductSpace.PiL2` supply Euclidean vectors and directions.
  `Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace` supplies their standard
  normalized volume; its orthonormal-basis and volume-preserving coordinate
  comparison were read.
- `ContDiff`, `fderiv` in `Mathlib.Analysis.Calculus.ContDiff.Defs` and its public
  dependencies, `HasCompactSupport`, and `MeasureTheory.integral` in
  `Mathlib.MeasureTheory.Integral.Bochner.Basic` give the explicit weak identity.
  No private Sobolev or distribution notion is introduced.
- The already stated proof leaves are imported without `public`:
  `FiniteDimensional.proper` from
  `Mathlib.Analysis.Normed.Module.FiniteDimension`;
  `BoundedContinuousFunction.arzela_ascoli` from
  `Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli`;
  `IsCompact.tendsto_subseq` from `Mathlib.Topology.Sequences`.
  Their complete signatures and available docstrings were read.
- The four other proof dependencies, `lem-sfb-l1-l2-fourier-realization`,
  `lem-sfb-fixed-support-fourier-lipschitz`,
  `lem-sfb-l2-weak-derivative-fourier-identity`, and
  `lem-sfb-euclidean-sobolev-graph-mollification`, have no Lean records yet in the
  read snapshot. They serve only the postponed proof, are named in its docstring,
  and supply no statement notions that require introducing them in this delivery.

Edge cases checked before writing:

- `r = 0` remains allowed: the target and its `Lp` space are zero spaces, the
  weak identity is zero equals zero, and the zero limit with identity indices works.
- `K = ∅`, or compact `K` of measure zero: the a.e. support condition makes
  each `Lp` term zero; its limit can be zero. No nonempty or positive-volume
  hypothesis occurs.
- The zero sequence and bound `M = 0` are admitted; a positive bound is merely a
  later proof choice. A negative proposed bound cannot witness the hypothesis,
  since squared norms are nonnegative.
- `m = 1` is admitted and the sum and unit direction have one coordinate.
  `m = 0` is excluded exactly as in the node by `hm`.
- Modifying representatives on null sets changes none of the integral identities,
  norms, or a.e. support conditions. The limit is not required to be smooth, nor
  is convergence asserted for derivatives or for the entire input sequence.
- All variables and dimensions are explicitly bound, with `set_option autoImplicit false`.

Searches for an existing statement (all through the prescribed `msearch.py`):

1. `leanfinder`, query `Rellich compactness bounded L2 weak first derivatives functions with fixed compact support Euclidean space`:
   eight hits, on `MeasureTheory.eLpNorm_le_eLpNorm_fderiv*`,
   `MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv_aux`,
   `MeasureTheory.Lp.dense_hasCompactSupport_contDiff`, and Sobolev constants.
   These are smooth Sobolev inequalities or density, not Rellich compactness.
2. `loogle`, query `"Rellich"`: no hits.
3. `grep`, query `Rellich|Kondrach|HasWeakDeriv|WeakDeriv`: no hits in Mathlib.
4. `leansearch`, query `Rellich compactness fixed compact support bounded weak first derivatives L2`:
   eight hits: `HasCompactSupport`, test-function support facts, the smooth
   Sobolev inequality, compactly supported `Lp` approximation/density, and
   compact support of derivatives; none gives this compactness conclusion.
5. Local `rg` in both `lean/Sheaf` and `lean/WeilConjectures` for
   `Rellich|weakDeriv|WeakDeriv|distributional|weak derivative` returned no hits;
   the required item-id search in `lean/WeilConjectures` also returned no hits.
   The final chosen declaration name was searched in Mathlib and both project
   source roots and is unused. A DAG search for weak-derivative and Rellich
   descriptions found related unrecorded proof prerequisites, not an existing
   declaration or an additional statement notion needed here.

Validation: the prescribed `scompile.py Q03 lem-sfb-euclidean-fixed-support-rellich`
compiled both the sandbox and actual library module successfully, with no errors
or unexpected warnings. The initial parser probe needed the standard `ContDiff`
scope for `∞`; the delivered module explicitly opens it. No statement dispute,
statement correction, or dependency-interface fault was found.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
