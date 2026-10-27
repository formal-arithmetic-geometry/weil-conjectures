## Worker report

The module `Sheaf.AlgebraicGeometry.BranchMultiplicityTangentCriterion` states
`AlgebraicGeometry.ProjectiveCurveBranches.branch_multiplicity_tangent_criterion`.
Its only postponed proof is this named theorem. Definitions have actual data.
The statement of the DAG node is unchanged. No statement correction or new node is needed.

Hypothesis and clause correspondence, read against the node:

- Algebraically closed k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- r >= 2: `(r : ℕ) (hr : 2 ≤ r)`. Ambient is the existing projective space
  `ℙ(ULift.{u} (Fin r); Spec (.of k))`, which has r homogeneous coordinates, hence dimension r-1.
- Reduced closed subscheme D of pure dimension one: `(D : Scheme.{u}) [IsReduced D]`,
  `(i : D ⟶ Ambient k r) [IsClosedImmersion i]`, `(hpure : D.IsPureDimension 1)`.
  The structure morphism of D is the specified composite of i with the ambient projection.
- Closed rational p: `(p : D) (hp : IsClosed ({p} : Set D))` and `hprational`,
  bijectivity of the actual structural map from k to the residue field. Thus this means D(k),
  rather than an arbitrary point endowed with an unrelated coefficient identification.
- Componentwise normalization: `Component D Z` is the existing normalization of the existing
  reduced component; `D.normalizedComponentMap Z` is its canonical map to D.
  `hnormal` writes precisely the stated smooth, proper, connected conditions, over the induced
  structure map. There is no integral assumption on D, or restriction to distinct components.
- The actual fibre is `Branch D p`, a sigma of component labels and points q with canonical
  normalization image p. `localMap` transports the actual stalk map along that equality.
  `branchIdeal` is exactly the extension of m_p along this map.
- The e_i are `componentDegree`: existing `Scheme.Modules.degree`, applied to the existing
  tensor pullback of `ProjectiveSpace.twist ... 1` along the composite component map into P.
  The explicit Over instance uses its induced k-structure; no arbitrary line bundle is supplied.
- The t_p convention is `HasMultiplicity D p t`: eventually finite length of
  `O_D,p / m_p^(n+1)` and equality to `t*n+a` for an integer a. This characterizes the slope
  without choosing a polynomial or taking `toNat` of an infinite length. The statement is for
  every t satisfying the displayed definition, just as it is for the t_p in the node.
- Positive b_q and its defining ideal equality: existential b, then the conjunct
  `∀ q, 1 ≤ b q ∧ branchIdeal ... q = maximalIdeal ... ^ b q`.
- Finite sum over the whole fibre: s is a Finset of actual branches with `∀ q, q ∈ s`;
  `t = ∑ q ∈ s, b q`. This also supplies finiteness rather than assuming it.
- Each component bound: for every Z, sum the b_q with `q.1=Z`, as integers, and compare to
  `componentDegree ... Z`. An empty component fibre gives the empty sum zero.
- Tangent zero iff b_q >= 2: `tangentImage ... q = {0} ↔ 2 ≤ b q`.
  `tangentImage` uses the existing `schemeTangentMap` on the actual ambient composite and the
  canonical induced residue-field isomorphism. Its image is transported into the ambient
  tangent space at i(p). Bijectivity is an existential proposition attached to the canonical
  map, never an arbitrary map or a new assumption on branches. In the rational situation it
  holds. No private tangent-space model replaces `schemeTangentSpace`.
- When t=2 and every tangent map is nonzero: two implications with exactly these premises.
  Exist q₁ != q₂, every branch equals one of them, and both exponents are one.
- Their one-dimensional tangent images: `Module.finrank` of the ambient-residue-field span
  of each actual tangent image is one. Projective lines through i(p) are represented dually
  by their subspace of vanishing homogeneous linear forms. `lineEquations` uses zero
  dual-number pullback on every vector in the actual tangent image, in every affine frame.
  This means vanishing at p and on the direction, not a condition imposed on higher jets of
  D. The theorem says this set is a k-submodule W of codimension two, hence a projective line.
- Distinct projective lines iff the completed local algebra is k[[u,v]]/(uv): inequality of
  the two equation spaces iff `HasSplitNodeCompletion`. The latter explicitly gives a ring
  equivalence commuting with structural scalars k. An isomorphism between these local rings
  preserves maximal ideals and their powers, so it also preserves their adic topologies.
  Thus this is the complete-local k-algebra isomorphism, not merely an abstract ring match.
- Coincident lines T and forms vanishing on T: equality of equation spaces, followed by
  `∀ a, a ∈ lineEquations ... q₁ → HasOrderAtLeastTwo ... q₁ a ∧ ... q₂ a`.
  The latter is membership in the squared branch maximal ideal in every standard frame.
  It includes zero and identically vanishing pullbacks, whose order is infinite.

Dependency declarations read and used:

- Mathlib `Field`, `Scheme`, `Scheme.Hom`, `IsReduced`, `IsClosedImmersion`, `Module.length`,
  `AdicCompletion`, `MvPowerSeries`: their recorded source definitions were opened.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization`,
  `Scheme.fromNormalization` (through the canonical reduced-component construction).
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalizationComponent`
  and its integral structure. Existing node `def-weil-pbc-reduced-normalization` added to stmt_deps.
- `Sheaf.AlgebraicGeometry.StablePointedCurve`: `Scheme.normalizedComponentMap`.
  Its owning existing node `def-sfb-stable-pointed-curve` is added to stmt_deps solely for
  this recorded helper; the theorem assumes no stable-curve predicate or nodal hypothesis.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: `ProjectiveSpace.twist`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible`: `ProjectiveSpace.coordRatio`
  and imported `ProjectiveSpace.standardOpen`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: `Scheme.Modules.degree`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`.
  Its existing owning node `def-pc-module-pullback` is added to stmt_deps.
- `Sheaf.AlgebraicGeometry.DivisorModule`: recorded smooth-curve divisor convention, supplying
  the dependency import; orders in this statement are written as exact ideal powers, as in
  the node, so no second valuation definition is introduced.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace`, its canonical
  additive and module instances, and `schemeTangentMap`.

All stated proof-dependency modules are imported non-publicly (finite-quotient completion,
Hilbert--Samuel growth, rational tangent/cotangent duality, power-series structure, complete
local quotient, completion modulo powers and maximal ideal, cotangent surjectivity, and
Mathlib length additivity). Unstated proof dependencies are named in the nine-step docstring
and remain future proof work; they are not required to elaborate this statement.

Sources opened: current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md` (its clause (3)),
Stacks curves.tex section Multicross and nodal singularities (0C1U--0C1W), and Morrison online
at https://arxiv.org/pdf/0810.2340, printed pp.14--15 (Theorem 8 branch/tangent discussion).
The node correctly identifies itself as an expansion rather than a quotation of all these
assertions from the Stacks tags.

Edge cases checked mathematically: the empty D has no p, hence is not silently ruled out by
an added nonempty-curve hypothesis. D need not be connected. Components missing p are included
in the degree inequality. A smooth branch has b=1 and nonzero tangent; the cusp has b>=2 and
zero differential. A node has two exponent-one branches and distinct equation spaces; a
self-node has both branches on one global component and is included by the sigma type.
Two tangent branches (tacnode) have the same equation space; the final clause covers the zero
form and a hyperplane containing a component. r=2 is permitted (the ambient projective line),
and no characteristic is excluded. All scheme/field/index types use u, with coordinate
ULift giving exactly r coordinates in that universe.

Searches made before stating, using msearch.py with Q95 and this item:

- leanfinder: “The multiplicity of a reduced projective curve is the sum of branch orders on
  its normalization and two distinct tangent lines characterize a node”: eight Weierstrass
  nonsingularity hits; none states this theorem.
- loogle: `"AlgebraicGeometry", "multiplicity"`: zero hits.
- grep: `branch.*multiplicity|multiplicity.*branch|ordinary.*node|tangent.*line` in
  Mathlib/AlgebraicGeometry: zero hits.
- leansearch: “Reduced projective curve normalization branch multiplicity tangent criterion
  ordinary double point”: eight Weierstrass projective nonsingularity hits; no match.
- rg in both lean/WeilConjectures and lean/Sheaf for component normalization, branch order,
  HilbertSamuel, tangent image/line, and the item id: found the reused normalization, twist,
  tangent and degree interfaces; no declaration states this theorem. Existing ordinary-node
  predicates do not impose the structural k-algebra compatibility required here. The new
  helpers in this module unpack the item's own notions and are listed in lean.declarations;
  they do not create independent mathematical prerequisites.

No STATEMENT-DISPUTED flag or node correction is necessary.

## Second reading by Q95

I reread the node, each dependency signature/docstring, and the final module after compilation.
The dispatcher explicitly forbids starting another agent, so this is a separate self-reading,
not a claim of independent authorship; the maintainer supplies the independent review.

The rereading checked every correspondence listed above against the actual binders and
conjuncts. In particular, r counts homogeneous coordinates (dimension r-1), the normalization
is canonical componentwise, the k-structure used by degree is induced, and the fibre includes
its component label. The finite sum includes all branches, and the component inequality is
not restricted to components meeting p. The equality-of-lines test uses ambient dual-number
first jets rather than defining the line by second-order vanishing along the curve. Its
codimension-two assertion certifies an actual projective line. The node equivalence keeps the
structural k-map in its coefficient equation. The common-line conclusion applies to every
linear form and allows a zero pullback. The exponent shift n+1, positivity b>=1, b=1 at both
double-point branches, and the same-global-component case were all checked explicitly.

Changes after reading/compile: corrected an initially guessed import path to the actual
`ProjectiveSpace.OfInvertible`; imported the existing tensor pullback construction and used
an explicit structural residue map; wrapped one line exceeding 100 columns. No mathematical
hypothesis, conclusion, or DAG statement changed. Only existing notion nodes were added to
stmt_deps, and no dependency record is replaced.
