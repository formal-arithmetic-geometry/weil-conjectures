## Worker report

The module `Sheaf.AlgebraicGeometry.RationalProjectiveAttractingCells` states
`AlgebraicGeometry.RationalProjectiveAttractingCells.rational_projective_attracting_cells`.
Its only theorem has proof `sorry`. All six auxiliary definitions contain real data or
explicit predicates. The item statement, proof, and proof dependencies are unchanged.
The added definition interface is described below.

Source read: Milne, Algebraic Groups (2017), printed pp.272–275 (Theorem 13.47,
Corollary 13.49, Lemma 13.46 and the application following Lemma 13.51), and
pp.277–278 (Remark 13.57 and Proposition 13.58). Projectivity is retained for
exhaustion; the source's exhaustion assertion without properness is not used.
The latest blueprint snapshot is ef6f9619, as recorded in COMMITS.txt.

Hypothesis and clause correspondence:

- The arbitrary field is `{F : Type u} [Field F]`, with no algebraic closure,
  perfectness or characteristic restriction.
- The F-scheme and its structure map are `X : Over (Spec (.of F))` and `X.hom`.
  Nonemptiness, smoothness, projectivity, and geometric connectedness are exactly
  `[Nonempty X.left]`, `[Smooth X.hom]`, `[IsProjective X.hom]`, and
  `[GeometricallyConnected X.hom]`.
- The action is `a : ModObj (StandardGroupSchemes.multiplicative F) X`.
  `ModObj` includes the unit and associativity laws for a morphism of F-schemes.
- A basis of the given nonzero finite-dimensional E identifies it with F^(n+1).
  The representation is the scheme morphism `rho` to the existing GL_(n+1),
  with `[IsMonHom rho]`. Every positive dimension occurs, including dimension one.
  This is a coordinate presentation of the given representation, not an assumption
  that it is already diagonal. `p` and `hp` specify its projective line action by
  the full universal matrix substitution, including coefficients. `i` is the closed
  immersion, and `hi` is equality of the two equivariance morphisms.
- `I : Type u` with `[Finite I]` indexes the rational sections `x`.
  `hfixed` uses `RepresentsFixed`: the canonical morphism `Sigma.desc x` from
  the actual finite coproduct of Spec F is injective on A-points and its image
  is exactly the fixed points, for every algebra A. Together these give unique
  factorization. The final review strengthened the initial draft's mere iff-unique-
  factorization condition by explicitly requiring injectivity: without it, extra
  duplicated nonfixed sections could have escaped the image criterion. It is not the false assertion that every A-valued fixed point
  chooses one globally constant index: disconnected A can use several components.
- `IsFixed a A y` quantifies over every algebra map A → B and every unit t of B.
  `unitPoint` is the Spec map of Laurent evaluation; fixedness is a morphism equality.
  Thus finite fields and nonreduced test algebras are covered, without using only F-points.
- `IsAttractorMap a (x b) A q` writes A¹_A → X_A as the equivalent F-map
  Spec A × A¹_F → X. Its first conjunct says q(0)=x_b. Its second quantifies
  over every A-algebra B, every unit t and every scalar v and says q(tv)=t q(v).
  `linePoint` is Spec of polynomial evaluation, so this includes the universal
  scalar and unit, giving scheme equivariance, not a geometric-point condition.
- `RepresentsAttractor` gives both directions of the evaluation-at-one bijection:
  each equivariant q uniquely factors at one through the cell and every cell point
  has exactly one such q. Naturality follows from these explicit equations and
  uniqueness under precomposition; no unconstrained bijection is supplied.
- The conclusion provides schemes `C b`, inclusions `j b` and natural numbers `d b`.
  `Smooth (C b).hom` and `IsImmersion (j b).left` give smooth locally closed
  subschemes. Their F-isomorphisms to the recorded `AffineSpace (ULift (Fin (d b)))`
  are isomorphisms in Over Spec F. No affine coordinate ring is substituted for the
  scheme notion. The represents clause quantifies over all algebras A.
- `∀ y : X.left, ∃! b, y ∈ Set.range (j b).left` is the topological disjoint partition.
- `b₀`, `IsOpenImmersion (j b₀).left`, `DenseRange (j b₀).left`, and the
  closure equivalence give exactly the unique open dense cell and exclude dense
  closures of all other cells.
- For each `[Field L] [Algebra F L]`, all fixed and attracting identities are
  stated on every F-algebra A with `[Algebra L A] [IsScalarTower F L A]`.
  This ranges over exactly all L-algebras after restriction of scalars. By the
  actual pullback/restriction adjunction, Hom_L(Spec A,C_L) is Hom_F(Spec A,C),
  so these unique-factorization assertions specify precisely the fixed scheme
  coproduct Spec L and the attracting scheme `(C b)_L`, with their base-changed
  inclusions. The conclusion additionally states smoothness and immersion of
  these actual `Over.pullback` objects, their L-isomorphisms to affine spaces of
  the same dimensions, the partition of every point of X_L, and openness and
  uniqueness of the dense cell with the very same index b₀. No arbitrary comparison
  maps or unspecified base-change objects are used.
- For X F-isomorphic to Spec F the final implication gives `Nonempty (Unique I)`
  and `d b = 0` for every b. Combined with the preceding affine-space isomorphisms,
  this is the sole-stratum affine-zero-space clause, invariant under isomorphism.

Dependencies read and used:

- Mathlib.Algebra.Field.Defs: `Field`; Mathlib.Algebra.Algebra.Defs: `Algebra`.
- Mathlib.AlgebraicGeometry.Scheme: `Scheme` and its scheme morphisms.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsProjective`.
- Mathlib.AlgebraicGeometry.Geometrically.Connected: `GeometricallyConnected`,
  the fourth geometric notion stated by def-pc-geometrically-irreducible;
  its recorded Geometrically.Integral module is imported as well.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `affine`, `map`, `multiplicative`,
  `multiplicativeGroup`, and `additive`.
- Sheaf.AlgebraicGeometry.LinearGroupSchemes, with the canonical upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear:
  `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`;
  Morphisms.ClosedImmersion: `IsClosedImmersion`; Morphisms.Immersion: `IsImmersion`.
- Mathlib.AlgebraicGeometry.AffineSpace: `AffineSpace` and its structural morphism.
- The new node imports the existing polynomial Proj and homogeneous maps instead
  of creating a new projective-space scheme. Its definition uses
  `Proj.projectiveSpaceOverAffineToSpec`, `Proj.map`, and `MvPolynomial.eval₂Hom`.

Stated proof dependencies are imported: GmRepresentationWeightBasis,
Compactification.ProjectiveSpace, Regular, ReducedInducedClosedSubscheme,
LfpSmoothFlatBaseChange, and Mathlib smooth/open-immersion/flat APIs.
lem-sfb-smooth-affine-concentrator and lem-sfb-positive-graded-regular-polynomial
have no recorded Lean module in the inspected DAG and do not occur in the signature;
they remain named proof steps in the docstring. No dependency interface was replaced.

Edge cases checked before writing: Spec F gives one zero-dimensional cell; projective
one-space with weights (0,1) gives A¹ and its complementary point. Repeated weights
are allowed in rho (a scalar representation with higher-dimensional X cannot satisfy
the finite fixed-scheme hypothesis). An empty I is permitted syntactically but its
fixed-functor hypothesis and the other geometric hypotheses force it nonempty; the
conclusion establishes this by b₀. Zero coordinate algebras and disconnected algebras
are allowed. The coproduct formulation handles idempotent partitions correctly.
Finite and imperfect F and positive characteristic are not excluded. Negative weights
are represented by Laurent units. The natural number d includes zero. All test algebras,
fields and schemes use the common scheme universe u (not a separate smaller universe).

Searches actually run with msearch.py: LeanFinder query “A smooth projective scheme
with a multiplicative group action and isolated rational fixed points has affine
attracting cells” returned AffineSpace, Proj and affine-cover results, no match;
Loogle `"AffineSpace", "IsImmersion"` returned zero matches; Mathlib grep
`Bialynicki|Birula|attracting|concentrator` returned zero matches. Direct rg of
WeilConjectures and Sheaf found only references in proof plans, not this theorem.
The algebraically closed variant lem-sfb-projective-attracting-cells has no Lean
record and its field hypothesis is strictly different. Searches for the new notion
are recorded with the actual search-log results in its mathlib_searches.

No STATEMENT-DISPUTED issue or statement correction is needed.

## New nodes

`def-sfb-projectivized-gm-representation` owns
`Sheaf.AlgebraicGeometry.ProjectivizedGmRepresentation`. It reuses `DiagonalProjectiveAction.space` verbatim for polynomial projective
space; its new real definitions are the universal matrix of rho,
the ring substitution z_i ↦ Σ_j M_ij z_j, and the predicate identifying an internal
projective action with Proj of this substitution. Both projections characterize the
canonical product comparison, so the action cannot be changed by an arbitrary
identification. Its source is Milne 7.26 and 13.46. The source uses lines, so the
matrix has indices ij rather than the contragredient action on E.

The whole-DAG and whole-blueprint searches for projective action and projectivization
found no node with this notion. The existing def-sfb-diagonal-projective-action treats
only specified diagonal weights for a different torus presentation; it does not give
this general rational-representation interface. LeanSearch and LeanFinder queries for
the scheme projectivization returned Mathlib's vector-space Projectivization actions,
which require division-ring valued points and do not define projective scheme actions
on arbitrary algebras. Mathlib grep in AlgebraicGeometry returned only an unrelated
locally-fraction predicate. Direct rg of Sheaf and WeilConjectures confirmed no general
scheme interface; the existing diagonal-action interface was read and its coordinate
comparison convention followed without copying its diagonal-action predicate.
`blueprint_refs.py ancestor` reports None; the inherited via is retained with the item
prepended, as required for this supporting prerequisite.

Validation: both modules compiled separately in dependency order through scompile.py;
the server reported no errors or warnings. Final dry-run and delivery results follow
from the prescribed deliver2.py wrapper.

Final clause review also checked the zero algebra: both the coproduct Hom set and
the fixed-point Hom set have one element on the empty affine test scheme, so the
injectivity plus image formulation remains correct. This repair changes only the
Lean rendering, not the node statement. The prescribed dry run is repeated below.

A final duplication check removed the initial projective-space wrapper: the new
module now directly reuses the landed `DiagonalProjectiveAction.space`, and cites
its owning definition node. Only the general representation action predicate is new.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
