## Worker report

The module `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` states
`AlgebraicGeometry.WeilSheaf.tateTwist_weight_shift`, with its proof postponed by `sorry`.
The mathematical source is the current main-20261015 blueprint node and its five-step proof.
The declaration uses the published sheaf realization of the recorded weight predicates.

Hypothesis and conclusion correspondence:

- The global finite-field conventions are supplied by `{k₀ : Type u} [Field k₀] [Finite k₀]`:
  `p = ringChar k₀`, `q = Nat.card k₀`, and the geometric fibre in `WeilSheaf` uses the fixed
  `AlgebraicClosure k₀`. Every finite field and every scheme universe `u` are permitted.
- The coefficient prime is `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`; the chosen
  coefficient closure is the published `PadicAlgCl l` over `Padic l`.
- The source's coefficient isomorphism is `(ι : PadicAlgCl l ≃+* ℂ)`; `ι.toRingHom` supplies
  its embedding to the published weight predicates. It is not an arbitrary ring map.
- A finite-type scheme over the finite field is `{X : Scheme.{u}}` with
  `[X.Over (Spec (CommRingCat.of k₀))]`, the locally-of-finite-type instance, and the explicit
  theorem binder `[QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]`. No separatedness is assumed.
- The constructible Weil sheaf is `(F : WeilSheaf k₀ l X)`, carrying its actual Frobenius
  isomorphism and constructibility property; `n : ℤ` includes every signed twist.
- The actual Tate twist is
  `(tateTwistSheaf k₀ l X n).tensorObj F (isLisse_tateTwistSheaf k₀ l X n)`.
  This is the published tensor product with the signed roots-of-unity Tate line.
  Placing the lisse coefficient line first permits an arbitrary constructible second factor.
  No substitute scalar action is introduced as the statement's twisted object.
- The first conjunct is universally quantified over `w : ℝ`, with hypotheses `F.IsLisse` and
  `F.IsPunctuallyPureOfWeight ι.toRingHom w`, and concludes the same predicate on the twist
  at exactly `w - 2 * n`.
- The second conjunct is universally quantified over `w : ℝ`, with hypothesis
  `F.IsMixedOfWeightsAtMost ι.toRingHom w`, and concludes the mixed upper bound on the
  same twist at exactly `w - 2 * n`. This keeps the source's mixed clause separate.

Recorded statement-dependency declarations read and imported:

- `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost`,
  `WeilConjectures.DeligneLaumon.Reduction.Weights`, and
  `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`, `WeilConjectures.WeilSheaf.Stalk`.
  These are the predicates used directly in the theorem; mixedness is an actual finite
  sheaf filtration, not pointwise Frobenius-module mixedness.
- `WeilConjectures.intrinsicQbarComplexTwistFunctor`,
  `Sheaf.Paper.IntrinsicCoefficientTwists`: this recorded operation acts on intrinsic
  complexes. The sheaf statement uses the existing `tateTwistSheaf` and `tensorObj`
  realization on the published `WeilSheaf` category on which the recorded predicates act.
- `WeilConjectures.FiniteFieldDatum`, `Sheaf.Paper.FiniteFieldFiber`, supplies the global
  conventions. The published sheaf API specializes to the algebraic closure model.
- `WeilConjectures.sfWeilComplex`, `Sheaf.Paper.SfWeilSheafComplex`, supplies the intrinsic
  fixed-pair complex interface. This theorem concerns sheaves, not derived Ext morphisms.

The imported sheaf tensor and signed Tate-line declarations are
`AlgebraicGeometry.WeilSheaf.tensorObj`, `tateTwistSheaf`, and `isLisse_tateTwistSheaf`, from
`WeilConjectures.WeilSheaf.Tensor` and `WeilConjectures.WeilSheaf.TateTwist`.
Their definitions use actual internal Homs, duals and signed tensor powers.
The module additionally imports recorded proof dependencies `Sheaf.Paper.PointFibreEquivalence`,
`Sheaf.Paper.LocalFrobeniusTrace`, and `Sheaf.LinearAlgebra.FrobeniusModuleWeights` without
`public`. The other non-Mathlib proof dependencies have no recorded module yet.

The docstring carries all five steps: trivialize the Tate line with scalar q^(-n), iterate
local Frobenius at degree m to obtain q^(-mn), scale eigenvalues in both directions without
semisimplicity, compute the absolute value using q_y=q^m, and twist the actual finite sheaf
filtration with quotient weights u_j-2n. Only this theorem has a postponed proof.

Edge cases checked: n=0 gives weight w and the coefficient unit; n<0 uses dual powers and
raises weights; the zero sheaf permits an empty mixed filtration and has vacuous purity;
an empty scheme has no closed-point conditions; arbitrary closed-point degrees require m
iterations; nonsemisimple local Frobenius is covered by eigenvectors and sheaf filtrations.
No rank, connectedness, normality, positivity, or separatedness assumptions were added.

Searches:

- `msearch.py Q136 lem-tw-tate-twist-weight-shift leanfinder` queried
  "A Tate twist of a lisse Weil sheaf shifts punctual purity and mixed weights by minus twice
  the twist": eight hits, light-condensed monoidal structures and shifted Lie weight spaces;
  none states this sheaf theorem.
- The Loogle query `TateTwist` returned zero hits (unknown identifier).
- Mathlib grep `TateTwist|tateTwist|IsPunctuallyPure|IsMixedOfWeightsAtMost` returned zero hits.
- `rg` over the upstream WeilConjectures sources found `tateTwistSheaf`, `tensorObj`,
  `tateTwistSheafIso`, `cyclotomicUnit_zpow_eq`, and the generic mixed constant-twist theorem;
  none combines the two required sheaf Tate-twist clauses.
- `rg` over `lean/Sheaf` found the recorded weight-related declarations and no exact match.
  The same identifier search in the DAG found the item and its citers.

## Second reading by Q136

Independent second reading (maintainer review service, 2026-10-18), replacing the worker's
in-session self-check, which the section itself described as such (H11). Read against the node
statement, its main-20261015 five-step proof, the four statement dependencies and the exact
published declarations `WeilSheaf`, `IsLisse`, `tensorObj`, `tateTwistSheaf`,
`isLisse_tateTwistSheaf`, `cyclotomicUnit_eq`, `IsPunctuallyPureOfWeight` and
`IsMixedOfWeightsAtMost`.

Node clauses and their Lean:

- Finite-field datum (p,a,q,k0,k): `{k₀ : Type u} [Field k₀] [Finite k₀]`, with q = `Nat.card k₀`,
  p = `ringChar k₀` and k = `AlgebraicClosure k₀` inside the published `WeilSheaf` API. Correct.
- Prime l ≠ p, Qlb: `[Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`, `PadicAlgCl l`. Correct.
- ι : Qlb ≅ C: `(ι : PadicAlgCl l ≃+* ℂ)`, passed to the predicates as `ι.toRingHom`. Correct.
- Finite-type k₀-scheme Y₀: `X.Over`, `LocallyOfFiniteType` and the theorem binder
  `QuasiCompact`. Together these are finite type; no separatedness. Correct.
- F(n) for n ∈ ℤ: `(tateTwistSheaf k₀ l X n).tensorObj F _`. This is the published signed Tate
  line (blueprint def-wf-tate-twist): Q(0) is the constant sheaf, Q(1) has geometric Frobenius
  χ_l(σ) = q⁻¹ (`cyclotomicUnit_eq`), positive n gives tensor powers and negative n gives duals.
  The upstream `WeilComplex.tateTwist` tensors in the same order, Tate line first. The recorded
  declaration of def-coefficient-twists-detailed acts on intrinsic complexes, not on the
  `WeilSheaf` category where the recorded weight predicates live. So the existing upstream
  sheaf realization is used, and no new definition is introduced. Correct.
- Pure clause: for every w : ℝ, `F.IsLisse` and `F.IsPunctuallyPureOfWeight ι w` imply the
  twist is punctually pure of weight `w - 2 * n`. Correct and complete.
- Mixed clause: the node's F is the same lisse Weil sheaf ("If a lisse Weil sheaf F ... The same
  shift holds for upper weight bounds: if F is ι-mixed ..."). The delivered conjunct omitted
  `F.IsLisse`. That drops a node hypothesis and strengthens the statement (H3).
  CHANGED: the conjunct now reads `F.IsLisse → F.IsMixedOfWeightsAtMost ι.toRingHom w → ...`,
  with the exact bound `w - 2 * n`. `IsMixedOfWeightsAtMost` is the actual finite Weil-sheaf
  filtration with quotients punctually pure of weights at most w, matching the node.
  The worker report's bullet on the second conjunct predates this change.

Edge cases: n = 0 gives the constant sheaf and weight w. Negative n uses the dual line. The zero
sheaf is covered: purity holds vacuously and the empty filtration witnesses mixedness. An empty
scheme has no closed points. Nonsemisimple Frobenius is covered by the eigenvalue definition.
Universes: k₀ and X share the universe u, as the published `WeilSheaf` requires; nothing else
is restricted.

Searches: rg over upstream WeilConjectures and lean/Sheaf for weight theorems on
`tateTwistSheaf`/`constantTwist`/`tensorObj`. Found `IsPunctuallyPureOfWeight.tensorObj`,
`IsMixedOfWeightsAtMost.constantTwist` and `IsMixedOfWeightsAtMost.map_add`. These are
ingredients only; none states the item. No duplicate.

Citers in the current DAG were checked: thm-weil-deligne-purity,
lem-rp-hc2-eigenvalue-determinant-weight, lem-a1-curve-hc2-bound, rem-dl-a1-conventions and
sk-d-dl-a1-setup. They apply the item to lisse sheaves or to Frobenius modules. None uses the
mixed clause on a non-lisse sheaf, so the restored hypothesis breaks no citer.

Compile: the fixed module compiles clean with the per-file side compiler (3.7 s, no
diagnostics besides the suppressed `sorry`).
