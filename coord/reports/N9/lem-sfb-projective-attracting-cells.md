## Worker report

The main module `Sheaf.AlgebraicGeometry.ProjectiveAttractingCells` states
`AlgebraicGeometry.ProjectiveAttractingCells.exists_projective_attracting_cells`.
Its only theorem has proof `sorry`. The source is Milne, Algebraic Groups (2017),
Theorem 13.47, Corollaries 13.48--13.49, pp.272--274, the linear projective application
following Lemma 13.51, p.275, and Remark 13.57/Proposition 13.58, pp.277--278.
Read these passages and the appended p.273 properness erratum. The existing node already
retains projectivity; its statement has not been changed. No statement is disputed.

Hypotheses, clause by clause:

- Algebraically closed field: `(F : Type u) [Field F] [IsAlgClosed F]`.
- F-scheme: `X : Over (Spec (.of F))`.
- Nonempty, smooth, connected, projective: `[Nonempty X.left]`, `[Smooth X.hom]`,
  `[ConnectedSpace X.left]`, `[IsProjective X.hom]`.
- G_m action: `a : ModObj (StandardGroupSchemes.multiplicative F) X`; its internal
  action includes unit and associativity equations. This uses the existing Spec F[t,t^-1].
- Given equivariant linear projective closed embedding: `hlinear` supplies `n`, all
  integer weights `w`, the existing diagonal action `b`, a group isomorphism `e` from
  G_m to the rank-one Laurent torus, and a closed immersion `j`. The equation
  `a.smul ≫ j = (e.hom.hom.hom ⊗ₘ j) ≫ b.smul` is equivariance as scheme morphisms.
  Choosing a homogeneous basis of the given finite-dimensional representation converts
  exactly the original embedding to these coordinates. Conversely such weights define
  the finite-dimensional diagonal representation. No restriction on weights is imposed.
  Taking a nonempty coordinate set is harmless: P(0) is empty and X is nonempty.
  The isomorphism avoids identifying distinct existing models of the rank-one torus.
- Finite disjoint reduced rational fixed scheme: `m`, `Z`, the maps `z : Fin m →
  (𝟙_ _ ⟶ Z)`, `hz : IsColimit (Cofan.mk Z z)`, and the closed immersion `jZ`.
  A coproduct of the base point is precisely a finite disjoint union of reduced
  F-points. `hfixed` represents the fixed subfunctor on every test scheme after
  every further change of test scheme. It detects infinitesimal fixedness, not
  merely the fixed underlying geometric points.

Conclusions, clause by clause:

- `C`, `i`, `d` give the cell schemes, inclusions, and dimensions indexed by all fixed
  points. `IsImmersion (i r).left`, `Smooth (C r).hom`, and `IsReduced (C r).left`
  say locally closed, smooth and reduced.
- The first all-algebra iff identifies factorization through `i r` with `Attracts`.
  `Attracts` means an orbit extension on Spec A times A1 with the fixed zero value
  and specified evaluation at one. Maps over F out of this product are equivalently
  A-morphisms A1_A → X_A. `IsExtension` specifies the restriction along
  F[t] → F[t,t^-1] as exactly the orbit of its value at one. Remark 13.57 proves
  this is equivalent to equivariance for multiplication on A1. Separatedness gives
  uniqueness, even with nilpotents. The next two conjuncts explicitly assert both
  directions of the evaluation-at-one bijection, each with unique witnesses.
- `C r ≅ Over.mk (AffineSpace (ULift (Fin (d r))) (Spec F) ↘ Spec F)` is an
  isomorphism over F with the recorded Mathlib affine space. The adjacent finrank
  equality is exactly dimension of the strictly positive character tangent subspace.
  The residue field at a displayed rational point is canonically F; computing
  dimension over it is the same integer. The existing `schemeTangentSpace` is the
  dual-number space canonically dual to m/m² (the existing rational cotangent-duality
  interface supplies this interpretation). `weightSpace` uses t^n, not the derivative
  n, so it preserves the characteristic-p distinction between integer characters.
- `∀ p : X.left, ∃! r, p ∈ Set.range (i r).left` is finite disjoint exhaustion.
- The algebraically closed K-point iff is the exact geometric-point limit description.
  The following two conjuncts state that the pullbacks of the same inclusions
  partition X_K and that the pulled-back cells are A_K^(d r). Together with the
  all-algebra representing property this explicitly gives scalar compatibility.
- The `Y, jY` conjunct says every smooth reduced immersed scheme with the prescribed
  points over every algebraically closed extension has a unique isomorphism over X
  to the cell. This is uniqueness as subschemes, not equality of chosen presentations.
- `∃! r, IsOpenImmersion (i r).left ∧ DenseRange (i r).left` is the unique open dense
  cell. The next iff says exactly those fixed points have full strictly positive
  tangent space; it includes the converse used in the node's Step 8.
- `IsIso X.hom → Nonempty (Unique (Fin m)) ∧ ∀ r, d r = 0` renders the Spec F case
  invariantly under F-isomorphism; combined with the affine-space clause, its sole
  cell is A0_F.

Dependency declarations used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`; the dependency's algebraic
  closure record explicitly identifies this predicate.
- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: `IsProjective`.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `multiplicative`, `affine`, `map`,
  `additive`, `identitySection`; read their full definitions and group instance.
- Mathlib.AlgebraicGeometry.AffineSpace: `AffineSpace`, canonical `over` projection.
- Sheaf.AlgebraicGeometry.DiagonalProjectiveAction: `torus`, `space`, `IsDiagonal`;
  this already landed definition node is added to stmt_deps.
- WeilConjectures.AlgebraicGeometry.SchemeTangentSpace: `schemeTangentSpace`,
  its canonical additive group and residue module instances.
- The new definition node supplies `positiveSpace` and its explicitly constructed maps.

Already stated proof dependencies are imported plainly: GmRepresentationWeightBasis
(`weightDecomposition_and_basis`), WeilConjectures.Compactification.ProjectiveSpace
(`AffineSpace.isOpenImmersion_toRelativeProjectiveSpace`), Regular
(`IsRegular.of_smooth`, `IsRegular.isIntegral`), ReducedInducedClosedSubscheme
(`Scheme.IdealSheafData.reduced_induced_closed_subscheme`), and
WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
(`IsRegularLocalRing.exists_span_eq_of_isRegularLocalRing_quotient`). Read their
recorded signatures/docstrings. The Mathlib closed-immersion, smooth-composition and
open-factorization dependencies are exposed by the imported geometry modules.
The two proof nodes `lem-sfb-smooth-affine-concentrator` and
`lem-sfb-positive-graded-regular-polynomial` have no current recorded declarations;
they supply proof inputs only and are not imported or restated.

Edge cases checked before writing: the empty X is expressly excluded. m=0 is allowed
as input syntax but contradicted by nonempty projectivity and the fixed-functor
hypothesis, as the theorem's partition states. For Spec F, tangent=0, all weights
vacuously positive, d=0, and there is one cell. P1 with weights (0,1) has A1 at zero
and a point at infinity, with positive (not negative) tangent weight on the open cell.
A trivial action in positive dimension fails the finite reduced fixed-scheme hypothesis.
Arbitrary A includes the zero algebra, products, dual numbers, and nonreduced algebras;
no reducedness, domain or nonzero assumptions were introduced on test algebras.
Positive characteristic and weights divisible by the characteristic remain distinct
through integer powers of units. Universes are explicitly bound, with scheme/test
algebra universe u, including the conventional ULift finite coordinate index.

Searches actually run with msearch.py N9 lem-sfb-projective-attracting-cells:

- leanfinder: `Bialynicki Birula attracting cells for smooth projective scheme with
  multiplicative group action and isolated fixed points` returned eight hits on
  Proj, affine space and affine charts; no attracting-cell theorem.
- loogle: `ModObj, AlgebraicGeometry.AffineSpace` returned zero hits and unknown
  identifier ModObj. This search is inconclusive on the action name.
- grep: `Bialynicki|Birula|concentrator|attracting.*cell` returned zero Mathlib hits.
- leansearch: `linear multiplicative group action on projective space given by a
  Laurent polynomial coaction` returned projectivization of linear actions and
  Laurent coalgebra; no scheme attracting-cell theorem.
- rg of WeilConjectures for the item id and attracting/Bialynicki/concentrator found
  no existing statement; rg of Sheaf found the node's consumers and specialized
  cocharacter limits, but no projective attracting-cell theorem. Existing diagonal
  action and group-only tangent-weight definitions were opened and reused or
  distinguished, rather than duplicated.

Both delivered files compile separately through scompile.py against the live build;
latest run had no errors or warnings. No local compiler or global build was run.

## New nodes

`def-sfb-fixed-point-tangent-weights` defines the character eigenspaces and strictly
positive sum on the existing scheme tangent space, for arbitrary scheme actions.
Its own module is `Sheaf.AlgebraicGeometry.FixedPointTangentWeights`. All data are
explicit: structural residue scalar map, dual-number base, tangent point, span of
actual character-eigenvector equations, and supremum over positive integer weights.
There are no theorems or holes. It cites the existing scheme tangent-space and G_m
nodes. Source: Milne p.272 tangent convention before Theorem 13.47 and Corollary
13.48; Stacks Tag 0B2C for dual numbers. The project interface
TorusCharacterTangent.weightSpace requires a group scheme and computes Lie at the
identity, so cannot be used at fixed points of arbitrary projective schemes.
GmRepresentation.weightSpace requires a supplied Laurent coaction; the action here
is on X, so that also does not supply the needed notion. Searches by leansearch,
leanfinder, Mathlib grep, Sheaf/upstream rg and blueprint_refs.py are recorded in the
new JSON. Search results concern Lie weights, cotangent complexes or manifolds;
blueprint search returned zero matches. `blueprint_refs.py ancestor` returns None,
matching the item's inherited null ancestor. Its full inherited place and via are
preserved and extended to the tangent dimension clause.

## Second reading by N9

This is a single dispatcher worker; no other agent was started, as instructed.
This section records a fresh self-reading of the two modules and both JSON files;
it does not claim independent review. The maintainer's independent review remains
part of the delivery workflow.

Rechecked every binder and conjunct against the unchanged natural-language node.
The first draft only said that cell points factor iff an extension exists; I added
both unique evaluation-at-one directions so the arbitrary-algebra equivalence is
explicit. The first draft made scalar compatibility implicit in the representing
property; I added the actual Over.pullback partition and affine-space isomorphisms.
The tangent helpers initially lived in the theorem module; they now have their own
searched definition node and module because general scheme fixed-point weights are
not supplied by the group-scheme-only interface. All helpers have source and blueprint
docstrings, all variables and universes are explicit, all lines are at most 100 columns,
and the one postponed theorem carries all eight natural-language proof steps.
The hlinear coordinate presentation and coproduct fixed-scheme presentation were
checked to encode exactly the given objects rather than strengthen their hypotheses.
No dependency node was changed and no statement correction was made.
