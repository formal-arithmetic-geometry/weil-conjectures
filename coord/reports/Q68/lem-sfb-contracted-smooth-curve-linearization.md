## Worker report

Delivered statement: `AlgebraicGeometry.contracted_smooth_curve_etale_linearization` in
`Sheaf.AlgebraicGeometry.GroupScheme.ContractedSmoothCurveLinearization`. Its sole proof
is `sorry`; its docstring supplies all nine proof steps and their DAG dependencies.
Definitions have complete data. The existing statement is unchanged. Its `stmt_deps`
gains the new additive-coordinate definition and the already-landed constant-rank
module definition used by `hrank`.

Clause-by-clause translation:

- A commutative ring and S=Spec A: `(A : Type u) [CommRing A]`, with every object
  in `Over (Spec (.of A))`. The zero ring is allowed.
- Group scheme: `(U : Over (Spec (.of A))) [GrpObj U]`, exactly the group object
  of the recorded `def-sc-group-scheme` interface, now over the specified base.
- Smooth affine finite presentation: `[IsAffine U.left] [Smooth U.hom]
  [LocallyOfFinitePresentation U.hom]`. An affine scheme over an affine base has
  affine, hence quasi-compact and quasi-separated, structure morphism; locally
  finite presentation therefore gives finite presentation here. No stronger
  finiteness condition is imposed.
- G_m and its action: existing `RingGroupSchemes.multiplicative A` is the Laurent
  Hopf group; `[ModObj ... U]` gives an actual action morphism satisfying the
  action diagrams. `haut` imposes compatibility with the group multiplication
  on every test algebra. The internal action by a group already has inverses,
  so these multiplication-preserving maps are group automorphisms. Their identity
  and inverse compatibility follow from the group laws, without extra data.
- Additive geometric fibres: `hgeom` quantifies over every algebraically closed
  field Ω with A-algebra structure, requiring an `IsAdditiveCoordinate A U Ω q`.
  Its Cartesian clause says A^1_Ω is U_Ω and its point clause says the isomorphism
  respects addition. Thus it is a group-scheme isomorphism, not just an affine-line
  isomorphism or a bijection on Ω-points.
- Contraction: `hcontract` takes every A-algebra B and x in U(B), and supplies
  `q : line A B ⟶ U` with `q(0)=1`. Its equality on every compatible B-algebra D
  and every G_m(D)-point identifies the restriction to G_m with the orbit of x.
  A map over A from the B-line to U is canonically the same as a B-map to U_B;
  the extra component is the B-line's structure map. No arbitrary extension is
  substituted for the orbit condition.
- Lie rank one: `hrank` is `(GrpObj.lieAlgebraSheaf U).IsFiniteLocallyFreeOfRank 1`.
  This reuses the upstream dual-of-identity-cotangent sheaf. Over this affine
  smooth base its sections identify with the tangent kernel in the node;
  `tangentGroup`, `infPointsEquivTangentGroup`, `toLie` and the tangent equivalence
  in upstream Lie modules implement the bridge. No field hypothesis is used.
- Positive integer: `(n : ℕ) (hn : 0 < n)` represents exactly the positive integers;
  no positive integer is omitted.
- Differentiated coaction: `hweight` tests every B, t in G_m(B), and v in
  U(B[ε]) reducing to 1 under `TrivSqZeroExt.fstHom A B B`. Lift t constantly to
  B[ε]; its action on v equals pullback along `DualNumber.scale (t^n)`.
  For smooth U the finite-projective cotangent module gives tangent base change;
  evaluating the original coaction on all B-units is precisely this identity.
  In particular this is the entire character t^n and does not identify n with
  its image in B. It tests nilpotent B and infinitesimal points.
- Affine étale cover: the conclusion supplies I, commutative rings R i and
  A-algebra structures, requires `Etale (Spec.map (algebraMap A (R i)))`, and
  explicitly requires every point s of Spec A to have a preimage in some Spec R i.
  I may be empty, as necessary when Spec A is empty.
- Group-scheme isomorphisms q_i: `IsAdditiveCoordinate A U (R i) q` gives the
  Cartesian isomorphism A^1_(R i) ≅ U_(R i) and additive group-law compatibility.
  The identity and inverse follow from multiplicativity into a group, so no
  group clause is lost by using this coordinate encoding.
- Equivariance after every extension: the last universal quantifier runs over
  every R i-algebra B with compatible A-structure, every t and every x in B,
  and states `q(t^n*x)=t • q(x)`. `unitValue` is evaluation of T^1 through the
  actual Laurent point; it is necessarily a unit, not an arbitrary scalar.
- Final nonhypotheses: no `IsUnit (n : A)`, `IsReduced`, `IsNoetherian`, nonempty
  spectrum, or chosen nonidentity section occurs anywhere in the signature.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`;
  their full signatures and docstrings are read in the recorded source.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, with its group
  diagrams; `Hom.group` from the Cartesian group module gives group-valued points.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`:
  `AlgebraicGeometry.RingGroupSchemes.multiplicative` (recorded declaration list
  of `def-sfb-split-torus-over-ring`), exactly the arbitrary-ring Laurent group.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring`: `points`, `points.map`,
  `tangentGroup`; its public dependency `Lie.Basic` supplies `GrpObj.lieAlgebraSheaf`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`, the already-recorded rank notion.
- `WeilConjectures.Mathlib.Algebra.DualNumber`: `DualNumber.scale`.
- `Mathlib.AlgebraicGeometry.Group.Affine`: `algSpec`, the canonical contravariant
  spectrum on algebras; `Polynomial.aevalTower` supplies explicit point evaluation;
  `Spec.homEquiv` reads the Laurent point's coordinate map.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`;
  the helper uses `IsPullback`, the same universal property for the displayed square.

Proof-only recorded modules are imported plainly: ring-hom properties, smooth
algebras, Kähler differentials and their tensor base change, separated morphisms,
proper base change, and upstream smooth affine space. The four proof inputs
`lem-sfb-smooth-space-cover-etale-sections`, `lem-sfb-mu-n-fixed-subgroup-smooth`,
`lem-sfb-space-relative-lfp-permanence`, and `lem-sfb-flat-geometric-fibre-open-criterion`
have no `lean` or Mathlib match in the read DAG, so have no module to import;
they are retained by name in the proof docstring. They are proof inputs only,
not required to state this theorem.

Edge cases checked mathematically before writing and again against the signature:
zero ring/empty base (empty cover allowed), n=1, n=p in characteristic p, nilpotent
base and test rings, zero test algebra, disconnected base and nontrivial Lie line
bundle. The weight condition is never reduced to n acting in a Lie algebra.
There is no chosen global basis. Additivity at x=y=0 forces q(0)=1 by cancellation,
and additivity at x and -x forces inverse compatibility. Testing polynomial
algebras detects the group law as a scheme identity. All rings, schemes and
quantified algebras have universe u; no independent smaller test universe makes
hypotheses vacuous. Geometric points can be represented in the same universe
as A by the usual residue-field algebraic closure construction.

Searches made (prescribed `msearch.py`, plus read-only rg):

- LeanFinder: “A smooth affine group curve contracted by multiplicative scaling
  with positive tangent weight is etale locally the additive group”: 8 hits,
  standard-smooth charts and Weierstrass coordinate changes; none states this.
- LeanSearch: “Multiplicative group action on a smooth affine group curve is
  locally isomorphic to the additive group”: 8 abstract additive-action and
  elliptic-curve hits; no group-scheme theorem.
- Loogle: `"GrpObj", "Spec"`: 3 affine Hopf group structure instances, reused
  through the existing Laurent group, not a linearization theorem.
- Mathlib grep: `contracted|linearization|LieGroup|additiveGroup` under
  AlgebraicGeometry: 0 hits.
- Upstream `rg` for item id: no hits. Searches for Lie, tangent, additive and
  multiplicative group interfaces found the ring-level Lie modules and the
  field-only `StandardGroupSchemes` construction; `GroupSchemeLinearization`
  instead concerns line-bundle linearizations over fields.
- `rg` in Sheaf for contraction and smooth-curve linearization found no matching
  declaration. `dag/lean_names_upstream.json` has no corresponding theorem.
- Additional helper searches are recorded verbatim as JSON results in its
  `mathlib_searches`: LeanSearch, LeanFinder, Loogle, Mathlib grep and project/DAG
  grep, plus `blueprint_refs.py search 'additive coordinate'` (0 blueprint nodes).

Source opened online: https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf,
printed pp.117–119 (PDF pages 116–118), including the preceding nonidentity section
and the full proof of Lemma 4.2.2. The node already records that the local Conrad
archive is missing; the online source supports the unrestricted contraction and
mu_n argument used here. No statement correction or disputed assertion found.

Validation: `scompile.py Q68 lem-sfb-contracted-smooth-curve-linearization` compiled
both modules separately in dependency order, sandbox and library mode. Clean,
no errors or warnings (about 1.6s helper and 3.0s main).

## New nodes

`def-sfb-relative-additive-coordinates` defines, over arbitrary A and an A-algebra R,
the explicit line `Spec R[x]`, evaluation at B-valued elements, evaluation of the
existing Laurent coordinate, and `IsAdditiveCoordinate`. The last predicate means
the line-to-U square is Cartesian and q preserves addition on every test algebra.
It is exactly a parametrization as an additive R-group. Source: Conrad Lemma 4.2.2,
pp.118–119, where the affine-line parameter and final additive law are constructed.
The searches above found no such ring-level predicate or DAG node. Mathlib's
existing affine spectra, polynomial evaluation and pullback universal property
are reused; the field-only StandardGroupSchemes module is insufficient, and no
second group structure or hollow existence choice is introduced. All four
helper declarations have real data and source/blueprint docstrings.

## Second reading by Q68

The dispatcher explicitly prohibits spawning agents, so this is a separate pass
by the same worker, not a claim of independent authorship; the maintainer's
independent review remains to follow. Reopened both node statements and both
Lean files. Matched every hypothesis and conclusion as listed above. Checked
that `IsPullback` has the correct four legs, q maps the R-line to U over A,
point evaluation extends coefficients through the actual A→R→B tower, the
additive law is tested for every B and not just geometric points, and the
multiplicative coordinate is evaluated through the actual point's affine ring
map. Checked contraction restriction for all units after every base change;
checked tangent reduction uses the canonical fst map and scaling uses the full
character. The rank sheaf is the upstream Lie sheaf. Finite presentation is
rendered by lfp with affine source/base, and no Noetherian or field condition
is introduced. The I/R cover is jointly surjective, allows I empty, and supplies
a Cartesian additive coordinate and the exact t^n formula over every R_i-algebra.
No source-statement change, dependency repair or further mismatch was needed.
The original compilation repair merely enabled Mathlib's existing `MonObj`
scoped group-on-Hom instance; it did not define any new instance or notation.
