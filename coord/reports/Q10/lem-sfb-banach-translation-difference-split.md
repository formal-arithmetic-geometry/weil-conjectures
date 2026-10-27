## Worker report

The module `Sheaf.NumberTheory.Padics.BanachTranslationDifferenceSplit` states
`PadicInt.banach_translation_difference_split`, with its sole proof `sorry`.
No definitions, subsidiary theorems, new nodes, dependency repairs, or statement
corrections are introduced. The accepted stage-1 split is preserved verbatim.

The inherited BLOCKED ending concerned an already reviewed stage-1 split. I read
brief-stage2 §0, the current node (split, reviewed by Q160, no Lean record), and
the queue entry (stage 2). This is its first Lean statement, not a new split.
No released repair note exists for this item in the read repository.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph
(3). This invokes the open-coefficient result; the analytic expansion is recorded
in the item's six proof steps. I also read the inherited scalar-cochain module's
steps 4–5, which explicitly give the translation sequence and Mahler section.
The node makes clear that Stacks 0DVG supplies only cochain conventions, not this
analytic theorem; no claim of a Stacks proof of the analytic result is made.

Hypotheses and objects, clause by clause:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Complete normed Q_ell vector space: `(V : Type u) [NormedAddCommGroup V]`
  `[NormedSpace ℚ_[ell] V] [CompleteSpace V]`. The normed-space structure over
  the normed field gives precisely `‖a • v‖ = ‖a‖ * ‖v‖`.
- The strong triangle inequality is `[IsUltrametricDist V]`, equivalently
  `IsUltrametricDist.norm_add_le_max` for the existing additive norm.
- H is `ℤ_[ell]`, Mathlib's p-adic integers with their usual norm topology,
  identified with the inverse-limit topology by the cited profinite-tower node.
  R is exactly `C(ℤ_[ell], V)` with Mathlib's supremum norm and compact-open
  topology. No arbitrary action or arbitrary function-space model is assumed.
- `c`, `d`, and `e` are Q_ell continuous linear maps. Their first three
  conjuncts specify, respectively, `c v x = v`, `d f x = f (x + 1) - f x`,
  and `e f = f 0`. Thus their data is uniquely fixed by the formulas.
- The translation action is a family `τ` of Q_ell continuous linear maps,
  with `τ t f x = f (x + t)`. The next conjunct is joint continuity on
  `ℤ_[ell] × C(ℤ_[ell], V)`; zero and addition identities explicitly give
  the additive action laws.
- The trivial H-action on V and equivariance of the constant arrow are
  `τ t (c v) = c v`. Equivariance of difference is
  `d (τ t f) = τ t (d f)`. These express exactly the stipulated actions,
  without selecting an unrelated global action instance.
- Exactness at the two endpoints and in the middle is
  `Function.Injective c ∧ Function.Exact c d ∧ Function.Surjective d`.
  This is exactness of the abstract Q_ell-vector-space sequence, not
  a closure-of-image or topological exactness variant.
- The kernel is precisely constants via
  `d f = 0 ↔ f = c (e f)` and `e (c v) = v`. Since e is continuous and
  equals evaluation at zero, its restriction to the kernel is the required
  continuous inverse identification. Continuity is for the subspace topology.
- `ZeroAtInftyContinuousMap ℕ V` is Mathlib's c0: every sequence on the
  discrete naturals is continuous, and vanishing at the cocompact filter
  is convergence to zero at `atTop`. It has the existing supremum norm.
- The witness `M` is a Q_ell-linear isometric equivalence to this c0 space,
  characterized by `M f n = (fwdDiff 1)^[n] (⇑f) 0`. This is the exact
  coefficient formula of the recorded `PadicInt.mahlerEquiv_apply`; it
  specifies the same Mahler equivalence, upgraded to rational scalars,
  rather than postulating any additional basis or copying its definition.
- The coefficient shift is `M (d f) n = M f (n + 1)` for every n.
- P is a continuous Q_ell-linear map of c0, specified by `P a 0 = 0`
  and `P a (n + 1) = a n`.
- T is a continuous Q_ell-linear map, with the required conjugation
  `T f = M.symm (P (M f))`, right inverse `d (T f) = f`, and the stated
  bound `‖T f‖ ≤ ‖f‖`. There is no equivariance clause for T.
- The zero space is included: there is no Nontrivial instance on V,
  no finite-dimensional hypothesis, and the universe u is arbitrary.

Dependency declarations read and used:

- `def-weil-l-adic-numbers`: its Mathlib match, `Padic` in
  `Mathlib.NumberTheory.Padics.PadicNumbers` (Cauchy completion at line 531),
  and `PadicInt` in `Mathlib.NumberTheory.Padics.PadicIntegers` (the norm
  unit ball at line 60). These are the actual field and integers in the type.
- `lem-sfb-banach-mahler-coordinates`: its Mathlib matches
  `PadicInt.mahlerEquiv` and `PadicInt.mahlerEquiv_apply` in
  `Mathlib.NumberTheory.Padics.MahlerBasis` (lines 357 and 382). I read
  their signatures, construction, and docstrings. They are integral-linear;
  the theorem's coefficient characterization provides rational-linearity
  without adding an independent integral action hypothesis.
- Proof dependency `lem-sfb-integers-profinite-tower`:
  `Padic.coefficientExtension_integers_profinite_tower` in
  `Sheaf.NumberTheory.Padics.IntegersProfiniteTower` is imported privately.
  I read its full signature and proof docstring; its degree-one case
  supplies the topology identification used in the proof plan.
- Proof dependency `lem-sfb-compact-function-space-complete`: Mathlib's
  `ContinuousMap.instNormedAddCommGroup`, `norm_eq_iSup_norm`, and
  `normedSpace` in `Mathlib.Topology.ContinuousMap.Compact`, and
  `instCompleteSpaceOfCompactlyCoherentSpace` in
  `Mathlib.Topology.UniformSpace.CompactConvergence`.
- Proof dependency `lem-coef-compact-open-currying`: Mathlib's
  `ContinuousMap.curry`, `uncurry`, and
  `continuous_uncurry_of_continuous` in `Mathlib.Topology.CompactOpen`.
  Evaluation requires local compactness, available for compact Hausdorff H.
- `Mathlib.NumberTheory.Padics.ProperSpace` supplies the existing compactness
  instance. `Mathlib.Algebra.Exact.Basic` supplies `Function.Exact`.

Edge cases checked mathematically before writing: V = 0 makes every map and
identity the unique zero map; constants have only zeroth Mahler coefficient;
for constant v, the section is the function x ↦ x • v, so it should not be
required to commute with translations. A sequence supported only at index
zero becomes supported only at index one under P. The index n = 0 shift
and both P formulas include their boundary cases. No empty-domain case
arises for H, which contains zero; the coefficient space remains arbitrary.

Searches made through msearch.py, with no exact existing theorem found:

- LeanFinder: “Banach p adic continuous functions translation difference
  split exact sequence Mahler right inverse”; eight hits, led by
  `PadicInt.mahlerEquiv_apply` and `mahlerEquiv`. These give the existing
  coordinate dependency but not the whole exact equivariant sequence.
- Loogle: `PadicInt.mahlerEquiv, fwdDiff`; one hit,
  `PadicInt.mahlerEquiv_apply`, the same coordinate dependency.
- Grep in Mathlib NumberTheory/Padics:
  `mahlerEquiv|translation.*[Dd]ifference|shift`; five internal shift-formula
  hits in MahlerBasis, no split translation sequence.
- LeanSearch: “A continuous linear right inverse to translation difference
  on continuous p adic functions from Mahler coefficients”; eight hits,
  including generic continuous splitting interfaces and the Mahler equivalence,
  but no theorem with this exact conclusion and prescribed operators.
- rg of both project roots `lean/Sheaf` and `lean/WeilConjectures` for
  `mahler|translation.*[Dd]ifference|banachTranslation|banach_translation`,
  and later the proposed full declaration name and `mahlerEquiv`: the
  scalar-cochain module contains the informal analytic proof, and an unrelated
  abelian-variety module mentions a translation-difference point map; neither
  states this theorem. The new full declaration name has no match.
- `grep -rn` of the item id in `lean/WeilConjectures` has no hits;
  rg of `dag/lean_names_upstream.json` has no matching declaration.

The module docstring states the source and all six proof steps are carried in
the theorem docstring. The node copy changes only `lean`, including the full
verbatim theorem signature. The initial compile found an incorrect guessed
import path for Function.Exact; I replaced it with the existing
`Mathlib.Algebra.Exact.Basic`. The subsequent scompile.py run compiled both
sandbox and library module cleanly, with no errors or non-sorry warnings.
No STATEMENT-DISPUTED issue or source statement correction was needed.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
