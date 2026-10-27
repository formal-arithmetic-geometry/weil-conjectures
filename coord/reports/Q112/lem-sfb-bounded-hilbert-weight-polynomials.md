## Worker report

The item is stated by `AlgebraicGeometry.BoundedHilbertWeight.exists_uniform_bounded_hilbert_weights`
in `Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials`. Its sole postponed proof is
`sorry`; the docstring gives all eight accepted DAG proof steps. No statement correction,
dependency-record repair, or extra mathematical hypothesis was needed.

Hypothesis and clause correspondence:

- `n : ℕ` and the recorded `HilbertPlucker.Coordinates n = ULift (Fin (n+2))`
  write r=n+2 and cover exactly r≥2. Projective space has dimension r−1=n+1.
- `d : ℕ`, `hd : 0 < d`, `c : ℤ` give the degree and constant term of the linear
  polynomial. Degree of a projective curve is integral; it is not a field element.
  `B : ℕ`, `hB : 1 ≤ B` give the positive integral weight bound.
- `∃ m₀ A : ℕ, 1 ≤ m₀ ∧ 1 ≤ A` occurs before the field, scheme, embedding, basis,
  weights, or Hilbert representative. Thus the bounds depend only on r,d,c,B.
- `∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (i : X ⟶ ℙ(...))`
  covers all algebraically closed fields, in an explicit universe. There is no
  characteristic restriction. The embedding assumption is exactly `IsClosedImmersion i`.
- `ProjectiveHilbertPolynomial.IsCoordinatePolynomial k (n+1) i
  (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (c : ℚ))` is the recorded
  eventual homogeneous-coordinate dimension predicate. It is not an Euler-polynomial
  replacement or an assumption about H⁰ in every degree.
- `topologicalKrullDim X = 1` is the topological dimension conclusion, before any
  basis or weight is chosen.
- The existential `ρ : ∀ m, ModuleCat.of k S_m ⟶ sections k n i m` packages the actual
  polynomial restriction arrows. These are fixed, in EVERY degree, by the equality
  of their images under `zeroSections` on every standard chart to
  `tensorPullbackSection i ... (chartRingEquiv ... (dehomogenizeX ... p))` times the
  specified `twistGenerator`. This is the existing uniform-vanishing interface;
  the arrows are not unconstrained maps or extra hypotheses. Standard charts cover X,
  so these values uniquely determine restriction.
- `sections` is an abbreviation of the existing
  `UniformProjectiveFibreVanishing.cohomology` at degree zero for the tensor pullback
  of `ProjectiveSpace.twist`; that helper is exactly `RingedSpace.moduleCohomology`
  with scalars restricted along the structure map. The target is actual module-sheaf
  cohomology H⁰(X,O_X(m)), not its coordinate quotient or bare abelian-group cohomology.
- For every `m₀ ≤ m`, `Function.Surjective (ρ m)`, `Module.Finite k (sections ...)`,
  and `(Module.finrank ... : ℚ) = (d : ℚ)*m+c` give restriction, finite dimensionality,
  and target dimension P(m).
- `b : Module.Basis (Coordinates n) k (LinearForms k n)` is a full ambient basis of
  linear forms, with no linear-normality assumption. `w : Coordinates n → ℕ`
  encodes exactly nonnegative integral weights. `∀ j, w j ≤ B` is their upper bound.
- The new definition's `monomial b m e` is the product of these linear forms with
  exponents summing to m; homogeneous projection fixes the product and only supplies
  the homogeneous-subspace type. `IsMonomialBasis` requires linear independence and
  spanning of the actual restricted monomials. `weight` is the natural-number infimum
  of their total weights. In the stated degree range the explicit `∃ S` clause proves
  that this infimum is attained by a monomial basis, so it is exactly the requested
  minimum, not a default value in an empty candidate set.
- The existential function `a b w : ℚ` is constrained on every bounded weighted basis
  by `∃ z : ℤ, a b w = (z : ℚ)/2`. The absolute-value inequality is exactly
  `|weight − a b w * m^2| ≤ A*m`, for every `m₀ ≤ m`.
- `flag b w s` is the span of b_j of weight at most s. Equality at every natural
  weight threshold expresses equality of weighted flags (negative thresholds are zero).
  The final quantified implication gives `a b w = a b' w'` for any two bounded
  compatible presentations of that flag, including reorderings and repeated weights.
- `IsHilbertSemistable i P m` means that there are a recorded numerical polynomial
  with value P, a `HilbertPlucker.Hilbert`, a `HilbertPlucker.Presentation`, and its
  k-valued point whose pulled-back universal ideal equals `i.ker`, with
  `E.sl_line.IsSemistable k x`. Thus the point represents this scheme, retaining its
  nilpotents, and semistability is the existing positive-power invariant-section
  definition for the specified determinant linearization. The dependency identifies
  this with PGL semistability. Its implication concludes exactly
  `weight ≤ (Σ_j w_j)/(n+2) * m * ((d:ℚ)*m+c)`.
- No reducedness, purity, connectedness, smoothness, linear normality, or further
  condition on the scheme appears. There is no nonemptiness assumption: positive
  linear coordinate polynomial excludes the empty scheme as a consequence.

Dependencies read and used:

- `Mathlib.Algebra.Field.Defs`, `Field` (line 180); `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` (line 42) and its morphisms;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `IsClosedImmersion` (line 45).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, `ProjectiveSpace`, and
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, `ProjectiveSpace.twist`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`, `moduleCohomology` and
  `globalSectionsFunctor` (lines 52--82); the supplied scalar restriction and
  zero-degree identification are reused from `Sheaf.AlgebraicGeometry.UniformProjectiveFibreVanishing`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection` and the normalized adjunction.
- `Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality`,
  `ProjectiveHilbertPolynomial.IsCoordinatePolynomial`, with its equations and coordinate
  pieces read at lines 55--86.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim` (line 39).
- `Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization`,
  `HilbertPlucker.Coordinates`, `Hilbert`, `Hilbert.H`, `Presentation`, including its
  `sl_line`, universal ideal, monomial determinant normalization, and common semistable
  locus; `Sheaf.AlgebraicGeometry.GroupSchemeLinearization`, `Linearization.IsSemistable`.
- `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`; Mathlib's existing
  homogeneous submodule, homogeneous projection, `Module.Basis`, `LinearIndependent`,
  `Submodule.span` and natural-number `sInf` are used directly.
- Proof-only imports include `WeilConjectures.AlgebraicGeometry.Cohomology.Serre`,
  `Sheaf.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences`, and
  `Mathlib.RingTheory.MvPolynomial.Groebner` (`MonomialOrder.div`, lines 128--135).
  The Hilbert linearization and uniform vanishing proof dependencies are already public
  through the definition module. The dimension and bounded-Gröbner-degree proof nodes
  have no Lean declaration in the read snapshot, so their imports cannot yet be added.

Edge cases checked before writing: r=2 is n=0, hence the ambient is P¹, not P⁰.
For X=P¹, d=c=1, and weights u,v, the weight is (u+v)m(m+1)/2; a=(u+v)/2 is
half-integral and the numerical inequality is equality. All-zero weights give weight
and a zero. Constant weights t give w=t*m*P(m), a=t*d, again with equality in the
numerical test. Repeated weights permit arbitrary changes of basis within their flag
subspaces. Finite isolated or embedded components are allowed and affect only the
lower terms. Negative c is allowed; m₀ absorbs degrees where P(m) is negative.
Unrealizable polynomials give a vacuous assertion about X. The empty finite monomial
set is allowed when H⁰ is zero, and m=0 is in the definition, although the estimate
has m≥m₀≥1. No use of division in k or characteristic-dependent diagonalization is made.

Searches actually run with msearch.py for this item:

1. LeanFinder: “Uniform bounded weight Hilbert polynomial minimum weight monomial basis
   semistability projective curve” returned 8 unrelated polynomial/Weierstrass hits.
2. Loogle: “MvPolynomial.homogeneousSubmodule, Module.Basis” returned zero hits.
3. LeanSearch: “minimum total weight monomial basis Hilbert point weighted filtration”
   returned weighted degrees, homogeneous pieces and power-series order; no exact match.
4. LeanSearch and LeanFinder: “weighted flag minimum total weight monomial basis of
   projective scheme sections” each returned 8 weighted-homogeneous polynomial or
   power-series declarations, with no flag or minimum-basis-weight definition.
5. Logged Mathlib grep `HilbertWeight|hilbertWeight|weightedFlag|WeightedFlag|minimum.*weight`
   returned zero hits. Direct rg over Mathlib AlgebraicGeometry and LinearAlgebra, upstream
   WeilConjectures and Sheaf found only unrelated polynomial approximation comments.
6. Searched upstream for the item id: zero hits. Searched DAG definition statements for
   weighted flags, weighted filtrations and minimum monomial basis weights: no definition
   node. The existing Hilbert monomial numerical criterion is a separate theorem with
   no recorded Lean interface and supplies no reusable definition. blueprint_refs search
   for “weighted flag” and “monomial basis” returned zero blueprint nodes; ancestor returns
   no blueprint ancestor, matching the item's inherited null from.node.

Source: read Morrison [arXiv:0810.2340](https://arxiv.org/pdf/0810.2340), §2.2,
Proposition 1 and Lemma 2(1), pp.6--8, against the node's accepted bounded-weight expansion.
Read the current latest six-functor-stability unit and its direct-image proof (3), preserving
that unit and the inherited supporting-input chain. No disputed statement or source fault found.

## New nodes

`def-sfb-weighted-monomial-basis-weight` defines the weighted linear-form flag, actual
H⁰ vector space (by abbreviation of the existing cohomology interface), monomial products,
the finite restricted-basis condition, total weight, and its natural-number minimum.
Its module is `Sheaf.AlgebraicGeometry.WeightedMonomialBasisWeight`; all seven declarations
are recorded in lean.declarations. Every definition has real data and no postponed proof.
Its statement introduces k,X,i,n,b,w,m,ρ and S; it cites the existing polynomial, twist,
pullback, projective space and cohomology nodes rather than copying those notions.
The low-degree empty-infimum convention is explicit, and the main theorem states minimum
attainment in the only degrees where it uses it. Its source is Morrison §2.2 before
Proposition 1, pp.6--7. The three logged search kinds are recorded verbatim in its
mathlib_searches, with their actual hits and no claimed exact match. DAG and blueprint
searches found no definition node for these objects. The item's stmt_deps gains only
this node; the item's statement and proof remain unchanged. Its blueprint ancestry
inherits the item's null ancestor and prepends the item to its recorded via chain.

Validation: both modules compiled separately in dependency order with scompile.py,
without errors or unexpected warnings. No global build or direct repository edits were run.

Dry-run repair: added the new node’s empty `import_flags` metadata required by server
preflight, and expanded a grouped list of dependency citations to individual `[id]` links.
The Lean and mathematical statements were unchanged by this metadata repair.

## Second reading by Q112

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
