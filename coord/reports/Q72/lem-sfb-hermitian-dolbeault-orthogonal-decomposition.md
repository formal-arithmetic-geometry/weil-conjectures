## Worker report

The module Sheaf.Paper.HermitianDolbeaultOrthogonalDecomposition states
ComplexManifold.hermitian_dolbeault_orthogonal_decomposition with sorry as its entire
proof. It preserves the accepted natural-language statement and all four proof steps.
The previous ending concerned stage-1 unchanged-item preflight; the current stage-2
queue and coord/brief-stage2.md §0 authorize this statement delivery. There is no
released repair note for this item.

Source read: Wenrui Kong, Notes on Complex Geometry (April 9, 2025),
https://cims.nyu.edu/~wk805/files/Complex_Geometry_Notes.pdf, §§3.1, 6.1 and
Theorem 6.7 (first decomposition), printed pp.23–24. The source PDF is WANTED
locally. The current literature/blueprint/latest unit sk-thm-sf-ctf-stability
and its direct-images proof (3) were read; the inherited analytic prerequisite
supports that route and does not alter the unit statement.

Hypothesis and clause correspondence:

- Complex scalars: every form submodule and operator uses ℂ and ℂ-linear maps.
  The sole original statement dependency def-weil-field is a Mathlib leaf,
  mathlib_match = Field. Its full class signature and docstring were read in
  Mathlib.Algebra.Field.Defs; Complex supplies that field instance.
- Dimension n ≥ 0: n : ℕ, and Model n is Fin n → ℂ. No positive-dimension
  restriction is imposed.
- Complex manifold without boundary: TopologicalSpace M, ChartedSpace (Model n) M,
  IsManifold (𝓘(ℂ, Model n)) ∞ M and T2Space M. The model with corners is the
  full complex vector space. Hausdorffness is the usual manifold convention.
  No connectedness or projectivity or Kähler assumption is added.
- Compactness: CompactSpace M. The arbitrary universe u covers every base carrier.
  No Nonempty premise excludes the empty manifold.
- Smooth positive definite Hermitian tangent metric: g : HermitianMetric n M.
  Its matrix is Hermitian and positive on every nonzero tangent vector; its
  coefficients are real-smooth after coordinate changes to every holomorphic chart.
- Smooth complex forms of integer type: p q : ℤ and typeForms p q. The latter is
  zero for either invalid index. Otherwise it consists of smooth covariant
  alternating tensors of degree p+q with J-insertion eigenvalue i(p-q).
  On dz this eigenvalue is i and on dbar-z it is -i, so the sign convention is correct.
- d = partial + barpartial: D.exterior_derivative identifies D.dbar + D.del in
  each coordinate degree with Mathlib.extDerivWithin on the open chart domain.
  D.dbar_type and D.del_type give their exact bidegrees; D.square_zero is D² = 0.
- The L² metric is l2Pair g μ. It is an explicit sum of Bochner integrals of the
  inverse-metric contraction of covariant alternating tensors, normalized by 1/k!.
  MetricVolume.chart_density fixes μ by sqrt(det(Re g)) against coordinate real
  Lebesgue measure. MeasurableSpace and BorelSpace give the canonical Borel
  measurable structure; neither is an arbitrary replacement of the volume.
- Formal adjoint: D.adjoint_type lowers the second index and D.formal_adjoint is
  exactly l2Pair g μ (D.dbar α) β = l2Pair g μ α (D.adjoint β).
- Dolbeault Laplacian: D.laplacian is literally D.dbar.comp D.adjoint +
  D.adjoint.comp D.dbar.
- Harmonic summand: D.harmonic p q is typeForms p q intersected with that kernel.
- Exact summand: D.exact p q is (typeForms p (q-1)).map D.dbar.
- Coexact summand: D.coexact p q is (typeForms p (q+1)).map D.adjoint.
- Sum equals the space: the first conjunct is the supremum equality of these three
  submodules with typeForms p q.
- Orthogonality: the next three conjuncts quantify over each of the three pairs of
  actual summands and set the complex integrated pairing to zero.
- Directness: the final conjunct gives a unique triple of summand components for
  every α : typeForms p q. It does not claim uniqueness of primitives in adjacent
  degrees. The component equation is α = h + a + b.
- Actual smooth images without closures: Submodule.map is algebraic image of the
  specified smooth source space. No completion, closure or dense-span substitution
  occurs anywhere.

Dependency declarations used:

- def-weil-field: Mathlib.Algebra.Field.Defs, Field; the concrete ℂ and ℝ instances.
- New def-sfb-hermitian-dolbeault-data: module
  Sheaf.Geometry.Manifold.HermitianDolbeaultData; ComplexManifold.HermitianMetric,
  MetricVolume, DolbeaultOperators, typeForms, l2Pair, and the harmonic/exact/coexact
  submodules in DolbeaultOperators. All helper declarations are listed in its lean record.
- Mathlib's ChartedSpace, ModelWithCorners/modelWithCornersSelf, IsManifold, atlas,
  chartAt, fderiv, ContinuousAlternatingMap.compContinuousLinearMap, ContDiffOn,
  extDerivWithin, Matrix.IsHermitian, determinant, nonsingular inverse, Measure.map,
  Measure.restrict, Measure.withDensity and the Bochner integral provide the data.
- The proof dependencies lem-sfb-dolbeault-laplacian-elliptic and
  lem-sfb-elliptic-smooth-fredholm-decomposition currently have no Lean declarations;
  no fabricated imports are added. Both are named in the proof docstring, which
  includes the complete four-step proof and realification argument.

Edge cases checked before finalizing:

- Empty M: all coefficient fields and smooth sections are zero, the volume is zero,
  and the unique decomposition is the zero triple.
- n = 0: the tangent model is zero; the only nonzero exterior degree is zero,
  the empty determinant and empty product are 1, and volume is counting measure in
  each point chart. All valid forms are harmonic; both images are zero.
- Negative or excessive p or q: typeForms is bottom. The adjacent-type images
  vanish by the recorded type laws, including at q = 0 and q = n.
- Zero forms, zero summands, disconnected compact manifolds: no nonzero or
  connectedness hypotheses have been imposed.
- Coordinate-basis contraction: in degree zero the formula is conjugate α times β;
  in degree one it is contraction with G inverse; in higher degrees summing all
  ordered real coordinate tuples and dividing by k! gives the alternating tensor metric.
- The generating sets used in smoothForms and typeForms are themselves complex
  subspaces. Taking their algebraic span therefore creates no extra objects.
- The operators are not arbitrary chain maps: their type laws and sum fix the
  decomposition of the actual exterior derivative; their adjoint is fixed by the
  actual metric integral. No decomposition assertion appears in their structure.

Searches made (all before introducing the new definition):

- msearch.py leanfinder, query "Smooth complex forms on a compact Hermitian manifold
  decompose as the orthogonal direct sum of Dolbeault harmonic exact and coexact forms":
  8 results, including Submodule.isHilbertSumOrthogonal and finite-dimensional spectral
  decomposition; none state the smooth Dolbeault decomposition.
- msearch.py leansearch, query "Smooth differential forms of type p q on complex
  manifolds Dolbeault derivative Hermitian metric volume and formal adjoint": 8 results,
  including LinearPMap.IsFormalAdjoint and chart extDeriv lemmas. The latter are reused;
  neither is a construction of smooth manifold Dolbeault forms.
- msearch.py leanfinder, query "Definition of smooth differential forms on a complex
  Hermitian manifold Dolbeault operators with the canonical L2 inner product": 8 results,
  including derivation-bundle notation, a two-dimensional Kähler form and extDeriv;
  no missing definition is supplied.
- msearch.py loogle, query '"Dolbeault", "Hermitian"': 0 hits.
- msearch.py grep, query Dolbeault|HodgeDecomposition|HermitianManifold|differentialForm|
  DifferentialForm: one import of DifferentialForm.Basic. That file explicitly lists
  manifold differential forms as not yet defined; its exterior derivative is reused.
- rg in lean/WeilConjectures and lean/Sheaf for Dolbeault, dolbeault, HermitianMetric,
  hermitian_dolbeault, smoothForms, typeForms: no matches. The item-id search in
  lean/WeilConjectures also has no matches. The upstream declaration index has no
  Hermitian/Dolbeault declaration.
- DAG statement scan for Dolbeault, Hermitian metric, complex manifold and differential
  forms found analytic theorem nodes, with no usable Lean bindings, but no definition
  node for these spaces, metric or operators. Exact definition-id regex search: no hits.
- tools/blueprint_refs.py search Dolbeault: zero blueprint nodes. Its ancestor command
  returns None for this inherited item. The new node uses exactly that null ancestor
  and prepends the item to its inherited via-chain.

No STATEMENT-DISPUTED fault or statement correction is needed. The added definition
node is the only extension of stmt_deps; the accepted statement and proof are unchanged.

Validation: both modules compiled individually through scompile.py in dependency order
against the live published library. Only the statement theorem contains sorry; there are
no proofs or postponed data in the definition module. The final dry run also compiles
each delivered file and checks the node and report records on the server.

## New nodes

`def-sfb-hermitian-dolbeault-data` defines the smooth Hermitian Dolbeault setup of Kong
§§3.1 and 6.1 and the three subspaces of §6.2 Theorem 6.7. Its coordinate presentation
uses real alternating tensors on the genuine complex tangent model and smooth chart
changes, the type eigenspace criterion, positive Hermitian matrices, the induced volume
density and inverse metric contraction. It specifies the canonical exterior-derivative
components and their formal adjoint rather than choosing arbitrary maps or abstract
form spaces. Existing Mathlib manifold, matrix and integral data are reused. The searches
above are recorded verbatim in its mathlib_searches and show no existing definition node
or declaration for this combined setup. Its module contains definitions and structure
fields only and no sorry. Its statement dependencies are exactly def-weil-field.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
