## Worker report

The module `Sheaf.AlgebraicGeometry.SubcurveSpanWeightBound` states
`AlgebraicGeometry.SubcurveSpanWeight.subcurve_span_weight_bound`, with proof `sorry`.
The three auxiliary definitions specialize the existing tensor pullback of O(1), the
existing degree on a canonical component normalization, and the standard-chart
characterization of restriction used by the bounded Hilbert-weight theorem. They have
real data; no existence-based object or arbitrary map is selected. The item statement
and its proof are unchanged. Two already landed definition nodes are added to stmt_deps
so that the equation subspace and monomial-weight definitions are explicit dependencies.

Hypotheses and clauses, matched individually:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`. Scheme and
  coefficient universes agree with the recorded projective-space and cohomology APIs;
  the universe u itself is arbitrary. No characteristic restriction is imposed.
- `n : ℕ` parametrizes `r=n+2`, with the existing `HilbertPlucker.Coordinates n` index.
  A nonempty proper component union is impossible in projective dimension zero, so this
  includes every instance of the statement; even the projective-line ambient case is
  allowed (its nontrivial component-union hypothesis is impossible).
- `X`, `i`, `[IsClosedImmersion i]`, `[ConnectedSpace X]`, and `hdim` say connected
  one-dimensional closed subscheme of the specified projective space. `hgeneric` says
  the stalk at every point whose closure is an irreducible component is reduced.
  It allows embedded nilpotents at finitely many points; there is no `[IsReduced X]`.
- `D`, `δ`, `[IsClosedImmersion δ]`, `[IsReduced D]`, and `hred` present X_red: a reduced
  closed immersion with full underlying image is the reduced induced closed subscheme,
  unique over X. These are presentation data for exactly the named D, not a further
  geometric hypothesis. `hnondegenerate` says its degree-one equation subspace is zero.
- `hnodal` quantifies over nonsmooth closed points of D, using the structural stalk map
  to Spec k, and requires exactly the completed-local-ring model k[[u,v]]/(uv).
  It uses `AdicCompletion` and `MvPowerSeries (Fin 2) k` from the two recorded nodes.
- The finite list C and j consists of integral closed components, with `hdistinct`
  excluding repetition and `hcomponents` requiring exactly all irreducible components.
  Finite enumerability follows from the projective hypothesis and does not restrict X.
  Each `(C a).normalization` and `(C a).fromNormalization` is the recorded canonical
  normalization and map, not a substitute smooth curve or arbitrary finite morphism.
- S is the chosen subcurve's component set; `hne` and `hproper` say nonempty and proper.
  `y`, `[IsClosedImmersion y]`, `[IsReduced Y]`, and `hY` identify Y with the reduced
  closed union of exactly those components. No connectedness assumption is put on Y.
  The complementary component indices Sᶜ give precisely Z; its separate scheme
  presentation is unnecessary because neither inequality refers to its sections.
- `selected a` is a finset on the canonical normalization. Its cardinal is b_E; finset
  membership enforces distinctness. `hselected` requires closed points whose images
  lie on Y for each complementary component a∉S. Such points are exactly preimages of
  boundary nodes: the component is not in Y and D is nodal, so its intersection with Y
  is the nodal boundary (the imported nodal-subcurve-boundary theorem). We require no
  independence of these point conditions and do not select every boundary branch.
  Entries of selected on Y-components are unused, so they may be chosen empty.
- `hyperplane` is the actual tensor pullback of the recorded projective O(1).
  `componentDegree (j a ≫ δ ≫ i)` is its degree after the canonical normalization,
  using the existing Euler-characteristic degree over the composite structural map.
  `hdegree` is e_E>0 on complementary components. The first finite sum in the coefficient
  inequality is e_Y, exactly the normalized-component degree convention in the node.
- `hexception` is the componentwise disjunction b_E≤e_E or the rational-normal exception.
  The exceptional conjunction is e_E=b_E-1, b_E≥2, and an isomorphism of the component
  with P¹ over k for which ambient linear forms surject onto its H⁰(O(1)). Because the
  component is already closed embedded and smooth P¹, this says its embedding in its
  own span uses the complete degree-e_E linear series. Its normalization is then
  canonically isomorphic to that same component. This neither admits a singular rational
  component nor an incomplete projection of a rational normal curve. No restriction is
  added to the first alternative, even when the second alternative also holds.
- `IsRestriction` specifies ρ on every standard chart by dehomogenization times the
  standard twist generator, pulled back by the section-normalized tensor adjunction.
  Thus `ρ` and `hρ` only present the canonical restriction arrows already supplied in
  the bounded-weight dependency; they do not allow unrelated linear maps.
- `basis`, `w`, `hw`, and `hflag` present exactly the zero/one flag: every basis vector
  has weight zero or one, and its weight-zero subspace is the existing chartwise equation
  space on Y, which is the kernel W of restriction V→H⁰(Y,L|Y). The latter equality
  follows from the standard opens covering projective space and the degree-zero
  cohomology/sections identification; no extra hypothesis on W is imposed.
- `aF` and `haF` specify the same a_F as the bounded-weight theorem: eventual monomial
  bases and |w_F(m)-a_F m²|≤Am. This coefficient is unique, since two such bounds imply
  |a-a'|m²≤(A+A')m for arbitrarily large m. Hence it agrees with that theorem's
  half-integral coefficient without an extra integrality hypothesis. It is not a new
  weight invariant or an arbitrary real number. Natural A and m₀ allow every O(m) bound.
- The first conclusion is `finrank k (LinearForms ⧸ equations(Y,1)) ≤ finrank k H⁰(Y,L)`.
  This is exactly s≤h⁰, using V=k[x]_1≅k^r and W=equations(Y,1). The second is
  `sum_(a∈S) e_a + (sum_(a∈Sᶜ) card(selected a))/2 ≤ aF` over ℚ, exactly a_F≥e_Y+b/2.
  There is no semistability assumption or semistability conclusion.

Dependency declarations read and used:

- `Field` (Mathlib.Algebra.Field.Defs); `Scheme`, `Scheme.Hom`
  (Mathlib.AlgebraicGeometry.Scheme); `IsClosedImmersion`
  (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion); `IsReduced`
  (Mathlib.AlgebraicGeometry.Properties).
- `ProjectiveSpace.twist` (WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist),
  `RingedSpace.moduleCohomology` (WeilConjectures.Topology.RingedSpaceModuleCohomology),
  `Scheme.Modules.degree` (WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar),
  `Scheme.normalization` and `Scheme.fromNormalization`
  (WeilConjectures.Mathlib.AlgebraicGeometry.Normalization).
- `AdicCompletion` (Mathlib.RingTheory.AdicCompletion.Basic, ring structure from Algebra),
  `MvPowerSeries` (Mathlib.RingTheory.MvPowerSeries.Basic).
- `BoundedHilbertWeight.exists_uniform_bounded_hilbert_weights`
  (Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials); its signature and docstring
  supply the chart restriction and quadratic-error conventions used here.
- `ProjectiveHilbertPolynomial.equations`
  (Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality), carried by
  def-sfb-projective-coordinate-hilbert-polynomial, and `BoundedHilbertWeight.sections`,
  `LinearForms`, `flag`, `IsMonomialBasis`, and `weight`
  (Sheaf.AlgebraicGeometry.WeightedMonomialBasisWeight), carried by
  def-sfb-weighted-monomial-basis-weight. Both definition nodes already landed; no copies.
- The stated proof dependencies `nodal_subcurve_boundary`
  (Sheaf.TraceFormula.NodalSubcurveBoundary) and `Scheme.Divisor.moduleOfSmoothConnectedCurve`
  (Sheaf.AlgebraicGeometry.DivisorModule) are imported without public. The normalization
  section-defect and smooth-curve section-cap proof nodes have no recorded Lean module
  in the read clone and are not used to define any object in this statement; their proof
  steps are retained in the theorem docstring. There is no missing statement dependency.

Edge cases checked: disconnected Y; selected finsets empty, including b_E=0; the case
b_E=e_E; exceptional b_E=2,e_E=1 (e_E=b_E/2); a component satisfying both alternatives;
two lines meeting once in P² (s=2, e_Y=1,b=1 and a_F=3/2); finite embedded nilpotents on X;
all field characteristics; ambient r=2 has no nontrivial proper component union; one
irreducible component cannot satisfy `hne` and `hproper`. Low-degree m is not required to
have a monomial basis; only eventual m occurs in haF. The target H⁰ is the actual
cohomology module and is finite-dimensional geometrically, rather than assumed finite.
The rational-normal alternative uses a complete embedding and not just a genus-zero
normalization. No statement fault or STATEMENT-DISPUTED flag remains.

Searches (also logged by msearch.py in searches.jsonl):

- LeanFinder: “Leading Hilbert weight of linear forms vanishing on a nodal subcurve with
  selected boundary branches”: eight unrelated Lagrange/affine-combination/polynomial hits.
- Loogle: `AlgebraicGeometry, subcurve`: zero hits, unknown identifier AlgebraicGeometry.
- Mathlib grep: `subcurve|subCurve|rationalNormal|GenericallyReduced` under AlgebraicGeometry:
  zero hits. Additional `rational normal|RationalNormal|rationalNormal`: zero hits.
- LeanSearch: “rational normal curve complete linear series projective line”: eight
  unrelated elliptic/projectivization/configuration declarations, no match.
- rg of the full project Sheaf and WeilConjectures trees for RationalNormal,
  rationalNormal, GenericallyReduced, subcurve and the item id: the parent
  GiesekerPotentialStability and NodalSpecialCliffordSubcurve provide compatible component
  and cohomology conventions, but neither states this estimate. No declaration of the
  estimate exists. The parent mentions the item only in its proof docstring.
- DAG search identifies the existing integral-curve-span-degree-rigidity theorem node,
  which describes the rational-normal equality case but has no Lean binding or module;
  a `scompile.py --source Sheaf.AlgebraicGeometry.IntegralCurveSpanDegreeRigidity` check
  likewise reports source unavailable. This theorem is not a statement dependency of
  the present estimate. Its conclusion is not assumed here.
- `tools/blueprint_refs.py search subcurve`: zero blueprint-node matches. The latest
  direct-images blueprint proof was read; the item's inherited ancestor metadata is
  preserved. Morrison [arXiv:0810.2340](https://arxiv.org/pdf/0810.2340), Section 3.2,
  Definition 7 and Theorem 8 proof steps (7), (9)--(10), was opened online. The specific
  selected-branch extension and rational-normal exception are the agent reconstruction
  explicitly recorded in the source node, whose six proof steps are all preserved.

Validation: compiled through the prescribed scompile.py against current server sources;
no Lean error or non-sorry warning. Its initial cache-overlay attempt reports a disk-space
failure, and its built-in server confirmation succeeds. No launcher tool was modified.
The final dry-run and delivery results are recorded by the delivery wrapper.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the
maintainer's independent review is the only review.
