## Worker report

The module `Sheaf.Analysis.Calculus.WeightedCompositionDerivativeBound` states
`EuclideanSpace.matrixWeightedComposition_compact_derivative_bound` with `sorry`.
It defines two concrete expansions of expressions belonging to this same node:
`EuclideanSpace.matrixWeightedComposition` and
`EuclideanSpace.compactCoordinateDerivativeSup`. No mathematical assertion is proved.
The original natural-language statement, proof, proof dependencies, source and all
other metadata are unchanged. The already landed `def-sfb-bundle-sobolev-space`
is added to `stmt_deps` to reuse its existing real partial derivative.

The source is the agent-written six-step argument in this node. The inherited
Demailly Hodge reference remains unavailable locally and is not claimed to state
this auxiliary formula. There is no statement correction or disputed assertion.

Hypotheses and clauses, matched individually:

- Over R: `ℝ`, with Mathlib's field instance and ordinary real differential.
  `def-weil-field` records Mathlib `Field` (Algebra/Field/Defs.lean); its complete
  class signature and field docstring were read.
- All four nonnegative dimensions: `{d m q r : ℕ}`, without positivity hypotheses.
  Every real coordinate space is `EuclideanSpace ℝ (Fin n)`, whose norm is the
  Euclidean 2-norm, rather than the supremum norm on a plain function type.
- Open O and P: the two set binders and `hO : IsOpen O`, `hP : IsOpen P`.
- The map g:O→P: ambient `g` and `hgP : Set.MapsTo g O P`. Ambient extensions
  represent arbitrary functions on O; no property outside O is assumed.
- Smooth g: `hg : ContDiffOn ℝ ∞ g O`. In finite Euclidean dimension this is
  equivalent to smoothness of all coordinates to every finite order.
- Matrix-valued A: `A : EuclideanSpace ℝ (Fin d) → Matrix (Fin r) (Fin q) ℝ`.
  `hA` requires `ContDiffOn ℝ ∞` of each entry on O, exactly as the node specifies.
- Any smooth f:P→R^q: each f binder has ambient Euclidean type followed by
  `ContDiffOn ℝ ∞ f P`. Arbitrary ambient extensions, including zero extensions,
  impose no global smoothness or continuity condition. Since P is open, all
  repeated ambient derivatives at its points depend only on the function on P.
- T_{A,g}f: `matrixWeightedComposition A g f` wraps
  `(A z).mulVec (f (g z))` in `WithLp.toLp 2`, retaining the Euclidean output norm.
- Smoothness on O: the first conjunct quantifies over every smooth f and asserts
  `ContDiffOn ℝ ∞ (matrixWeightedComposition A g f) O`. This clause holds without
  first choosing a compact set or derivative order.
- Any compact S⊆O and integer k≥0: `∀ S, IsCompact S → S ⊆ O → ∀ k : ℕ`.
- There exists a strictly positive real constant: `∃ C : ℝ, 0 < C ∧ ...`.
  This quantifier precedes `∀ f` and its smoothness assumption, so the constant
  may depend on the fixed A,g,S,k but cannot depend on f.
- The displayed derivative bound: the final inequality uses
  `compactCoordinateDerivativeSup S k (matrixWeightedComposition A g f)` on
  the left and `C * compactCoordinateDerivativeSup (g '' S) k f` on the right.
  The same order k is used, and the right-hand set is exactly g(S).
- Multi-indices: `α : Fin d → ℕ` and `(∑ j, α j) ≤ k`. Scalar coordinate
  derivatives use the existing `BundleSobolev.multiPartial`, whose definition
  repeats direction j exactly α j times, orders coordinates increasingly,
  and folds the ordinary real Fréchet differential on the standard basis vectors.
  Applying that scalar operator to each output component gives the actual vector
  partial derivative in Euclidean norm. No derivative is taken within S or g(S).
- Maximum and supremum: `compactCoordinateDerivativeSup` takes the real sSup of
  the union of derivative norms for |α|≤k and z∈S. For compact S in the smooth
  domain these sets are bounded, and there are finitely many α (each α j≤k).
  Therefore this union supremum is exactly max_{|α|≤k} sup_{z∈S}, with no norm
  equivalence or substituted Fréchet operator norm in the stated inequality.
- Empty compact convention: the set in the sSup is empty when S=∅; Mathlib's
  real sSup of the empty set is 0. This also applies to g(S)=∅.
- Zero-dimensional target convention: `WithLp.toLp 2` of a function on `Fin 0`
  is the unique vector, with norm 0. No nonempty-index assumption occurs.

Dependencies used and source interfaces read:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`, realized by R.
- `def-sfb-bundle-sobolev-space`: public import
  `Sheaf.Geometry.Manifold.BundleSobolevSpace`; the used declaration is
  `BundleSobolev.multiPartial`, with scalar real signature and full docstring/
  fold definition read in the source. This is an existing landed statement
  dependency, not a new definition or a repair of its interface. Its manifold,
  metric and Sobolev objects are not assumptions of this theorem.
- `lem-sfb-real-smooth-differentiation`: its `mathlib_match` is a collection of
  Mathlib rules. The proof-relevant `ContDiffAt.comp`, `.fderiv_right`, `.add`,
  `.mul`, `ContinuousLinearMap.contDiff`, `contDiffAt_const`, `HasFDerivAt.comp`
  and `.mul` signatures/docstrings were read. Plain proof imports are
  `Mathlib.Analysis.Calculus.ContDiff.Comp` and `.Operations`.
- `lem-sfb-real-second-derivative-symmetry`: plain import
  `Mathlib.Analysis.Calculus.FDeriv.Symmetric`, recorded declaration
  `ContDiffAt.isSymmSndFDerivAt`; its signature and `IsSymmSndFDerivAt` definition
  and `.eq` were read, identifying the adjacent swap used in the proof.
- `lem-sfb-compact-continuous-norm-bound`: plain import
  `Mathlib.Analysis.Normed.Group.Bounded`, recorded additive declaration
  `IsCompact.exists_bound_of_continuousOn`; its complete to_additive source
  signature was read. There is no nonemptiness or positive-dimension condition.
- Public `Mathlib.Data.Matrix.Mul` supplies `Matrix.mulVec` and its finite-sum
  coordinate formula; the complete definition was read.

Edge cases checked before formulation and again against the final signature:

- S empty: both suprema are 0 and C=1 works.
- O empty: only the empty S occurs; all smoothness conditions are vacuous and
  both conclusions hold. If P is empty and O nonempty, MapsTo correctly cannot
  hold, so no forbidden domain map is silently introduced.
- k=0: only the zero multi-index occurs; partial differentiation is the identity,
  and the claim is the compact multiplication norm bound.
- d=0: there is one source point and one multi-index, even when k>0.
- m=0: g(S) lies in the singleton zero-dimensional space and there is only β=0;
  the right-hand maximum is the value norm, not a family requiring m>0.
- q=0: the matrix-vector sum is empty, so T is zero; r=0: the output vector
  is unique and has norm zero. Both admit C=1.
- Noninjective or constant g: derivatives are those of f on the open set P,
  merely evaluated on g(S); no unique-differentiability condition on g(S) is added.
- Scalar d=m=q=r=1, k=1: derivative is A' f(g)+A f'(g)g', controlled by the
  same input order one, as the signature requires.

Searches for reuse (prescribed msearch.py, group Q55 and this item):

- `leanfinder`: "For smooth matrix weights A and smooth g between real Euclidean
  open sets, compact sup norms of coordinate derivatives up to order k of
  A(x) f(g(x)) are bounded uniformly in smooth f". Eight hits including
  `norm_iteratedFDeriv_comp_le'`, `norm_iteratedFDeriv_clm_apply`,
  `norm_iteratedFDerivWithin_comp_le_aux` and `norm_iteratedFDeriv_comp_le`.
  Bounds.lean signatures read: these are pointwise operator-norm estimates
  with derivative-bound hypotheses, not this compact coordinate maximum with
  a constant quantified uniformly in f.
- `loogle`: `norm_iteratedFDeriv_comp_le, norm_iteratedFDeriv_clm_apply`:
  zero combined hits. The declarations themselves were read directly as above.
- `leansearch`: "Compact Ck seminorm bound for multiplication by a smooth matrix
  and composition with a smooth map": eight hits; continuous-map normed rings,
  `ContMDiff.clm_comp`, `ContDiffMapSupportedIn.seminorm_postcompLM_le` and
  `ContDiff.comp_continuousLinearMap`. These concern compact continuous maps,
  fixed linear postcomposition or fixed-support functions, not this estimate.
- `grep`: `iteratedLineDeriv|multiIndexPartial|weightedComposition|compact.*seminorm`
  under Mathlib Analysis: fourteen hits about iterated directional operators
  and their Schwartz/distribution support, with no compact estimate of this form.
- Direct `rg` of Mathlib calculus, `lean/WeilConjectures` and `lean/Sheaf` for
  multi-index derivatives, weighted composition and compact seminorms: no
  existing estimate. Sheaf has complex `EuclideanSpace.multiIndexPartialDeriv`
  and the exact real `BundleSobolev.multiPartial`; the real definition is reused.
- Direct `rg` for the item id in `lean/WeilConjectures`: no hit.
- Direct `rg` for all three newly declared names in Mathlib, `lean/Sheaf`,
  `lean/WeilConjectures` and `dag/lean_names_upstream.json`: no hit.

Validation: scompile.py compiled the sandbox and library-form module cleanly
against the live server build (10.4 s and 8.3 s respectively). It uses
`set_option autoImplicit false`, explicit size binders, module mode, public
statement imports and ordinary proof imports. The only postponed assertion is
this node's theorem; all helper data is defined in full. Its docstring carries
the entire six-step argument, including the coefficient recurrence and choices
of M and C independent of f.

## Second reading by Q55

Independent second reading by the maintainer reviewer (the delivered section was a
worker self-check). Node statement (unchanged from live; only `stmt_deps` + `lean`
differ) matched against
`EuclideanSpace.matrixWeightedComposition_compact_derivative_bound`:

- Over ℝ, d,m,q,r ≥ 0: `{d m q r : ℕ}`, `EuclideanSpace ℝ (Fin n)` (Euclidean
  2-norm). Correct, no positivity assumption.
- O ⊆ ℝ^d, P ⊆ ℝ^m open: set binders + `hO`, `hP`. Correct.
- g : O → P smooth: ambient `g`, `hgP : Set.MapsTo g O P`, `hg : ContDiffOn ℝ ∞ g O`
  (`∞` = `(⊤ : ℕ∞)`, C^∞ not analytic). Correct, nothing assumed outside O.
- A : O → Mat_{r×q}(ℝ) smooth: `hA` entrywise `ContDiffOn ℝ ∞` on O. Correct.
- T_{A,g}f(z) = A(z) f(g(z)): `matrixWeightedComposition` = `toLp 2 ((A z).mulVec (f (g z)))`.
  Real data, correct.
- "This function is smooth on O" for every smooth f : P → ℝ^q: first conjunct. Correct.
- ∀ compact S ⊆ O, ∀ k, ∃ C > 0 independent of f: quantifier order
  `∀ S, IsCompact S → S ⊆ O → ∀ k, ∃ C, 0 < C ∧ ∀ f, ContDiffOn ℝ ∞ f P → …`. Correct.
- Displayed inequality: `compactCoordinateDerivativeSup S k (T f) ≤ C * compactCoordinateDerivativeSup (g '' S) k f`.
  The helper is sSup over {‖(∂^α f_a(z))_a‖ : |α| ≤ k, z ∈ S}, using the landed real
  `BundleSobolev.multiPartial` (iterated ambient `fderiv` on `EuclideanSpace.single i 1`).
  Since S ⊆ O and g(S) ⊆ P with O, P open, ambient derivatives at these points equal the
  derivatives of the restrictions; the sets are bounded (finitely many α, continuous
  derivatives on compacts), so the sSup equals max_α sup_z exactly and the junk value
  of an unbounded sSup never arises under the hypotheses. Ordered partials agree with
  the multi-index convention by symmetry of smooth second derivatives.
- Conventions: sSup ∅ = 0 (empty S, empty g(S)); `Fin 0` Euclidean norm 0. Correct.

Edge cases: S = ∅ (both sides 0); O = ∅; P = ∅ with O ≠ ∅ excluded by MapsTo as it
should be; k = 0; d = 0; m = 0 (only β = 0); q = 0 or r = 0 (T = 0); non-injective g.
All covered by the signature.

Records: stmt_dep `def-sfb-bundle-sobolev-space` added (landed, reviewed; owns
`BundleSobolev.multiPartial`, which is used); its stmt_dep closure does not reach this
item (acyclic). `lean.statement` equals the file signature verbatim. Helpers are real
definitions with source/blueprint docstrings; theorem is `sorry` with the six-step
proof plan. Searches: no Mathlib/project compact C^k weighted-composition estimate;
`multiPartial` and the complex `multiIndexPartialDeriv` are the only project
multi-index derivatives; the real one is reused. No mismatch found; no Lean change.
