## Worker report

The module `Sheaf.AlgebraicGeometry.CurveGraphFixedPolynomialCover` states
`AlgebraicGeometry.CurveGraphFixedPolynomial.exists_affine_numerical_cover` with
`sorry`. Its four helper definitions contain real expressions and predicates, not
chosen objects or postponed data. They package the clauses of this node; they do
not introduce independent geometric notions. All five declarations are listed in
`lean.declarations` and carry the owning blueprint identifier.

Source read: `literature/stacks-project/moduli-curves.tex`,
`lemma-curves-diagonal-separated-fp`, especially the four numerical functions and
the displayed graph calculation (Tag 0DSQ); `perfect.tex`,
`lemma-chi-locally-constant-geometric` (0B9T); `varieties.tex`,
`lemma-degree-tensor-product` (0AYX). The first source uses the reverse order of
X and Y; the formula here follows the order in the node. There is no statement
correction and no disputed clause.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Locally Noetherian S, schemes X and Y over S | `{S X Y : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) (g : Y ⟶ S)` |
| Flat finitely presented projective morphisms | `IsHProjective`, `Flat`, `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` for both f and g. The last three together express finite presentation; there is no smoothness or integral-curve assumption. |
| Specified embeddings into P^a and P^b over S | `a b`, `iX`, `iY`, `IsClosedImmersion iX/iY`, and the two equations `hiX/hiY` fixing their structural maps. |
| Geometric fibres have dimension at most one | `hX/hY` use `topologicalKrullDim` of the pullback at the recorded `geometricPoint S s`. The empty scheme has dimension bottom and is admitted. |
| L and N are the degree-one pullbacks | The final two module arguments of `HasLocalValues` pull back the recorded `ProjectiveSpace.twist ... S 1` along `pullback.fst ... ≫ iX/iY`. By pullback composition these are exactly the restrictions of iX*O(1) and iY*O(1). No arbitrary line bundles or extra invertibility hypotheses replace them. |
| Affine Noetherian open cover | `∃ (I : Type u) (U : I → S.Opens), (⨆ i, U i) = ⊤`, followed by `IsAffineOpen (U i)` and `IsNoetherian (U i).toScheme`. The cover may be empty when S is empty. |
| Restricted morphisms proper, flat and finitely presented | The first ten conjuncts of `HasLocalValues`, applied to `pullback.snd f/g (U i).ι`. |
| Four integers constant at every field-valued point | Existential `cX lX cY lY : ℤ`; each `HasFibreValues` quantifies `(K : Type u) [Field K] (t : Spec (.of K) ⟶ S)`. `fibreEuler ... 0 = c` and `fibreEuler ... 1 = l` give O and the polarization, respectively. Tensor power zero is the structure module; power one is canonically the polarization. |
| d=lambda-c, PX(n)=n*dX+cX, PY(n)=n*dY+cY | In `HasFibreValues`, `P = C (l-c) * X + C c`, and all n satisfy the integer Euler equation and the rational evaluation equation. Differences `l-c` are expanded instead of bound with a hidden let. |
| Product E and its closed projective embedding | `j : pullback f g ⟶ ℙ(ULift (Fin (((a+1)*(b+1)-1)+1)); S)`, `IsClosedImmersion j`, and its structural-map equation. Since (a+1)*(b+1)>0, the displayed coordinate count is exactly (a+1)*(b+1), including a=b=0. |
| Pulled-back degree-one module equals M=prX*L tensor prY*N | The `Nonempty` module isomorphism in `HasLocalValues`; M itself is the actual tensor of those two existing tensor pullbacks, also passed explicitly to `HasGraphValues`. |
| Every algebraically closed field point and every fibre isomorphism | `HasGraphValues` quantifies K with `[Field K] [IsAlgClosed K]`, t, and `e : Over.mk (pullback.snd f t) ≅ Over.mk (pullback.snd g t)`. The Over isomorphism is an isomorphism over K, not merely an abstract scheme isomorphism. |
| Closed graph Γ_f inside E_t | The source of `γ` is X_t itself. Its three projection equations fix the field projection, the X projection as identity, and the Y projection as e. Thus it is precisely the closed graph, not an arbitrary immersion. Its codomain is the field fibre of E using the structural map of j, equal to E's own structure by the previous equation. |
| Graph Euler formula for every n>=0 | The integer `eulerChar` in `HasGraphValues` pulls M_t^n back by γ. Its field structure is explicitly the second fibre projection. It equals `n*((lX-cX)+(lY-cY))+cX`. |
| R(n)=n(dX+dY)+cX=PX(n)+PY(n)-PY(0) | The first two equalities in `HasGraphValues` define R as the linear polynomial and identify it with `PX + PY - C (PY.eval 0)`. Thus evaluating R gives the preceding integer Euler value. |
| Coordinate Hilbert polynomial for j_t | The recorded `IsCoordinatePolynomial K r (γ ≫ baseChangeEmbedding r j t) R`. |
| Every homogeneous ideal defining the embedded graph, including nonsaturated ideals | The subsequent universal J/d clause identifies `Proj(coordinateQuotientPiece J)` with X_t over its embedding and gives `∃ n₀, ∀ n≥n₀, finrank K (coordinateQuotientPiece J n) = R.eval n`. No saturation, radicality, or nonzero quotient is assumed. The canonical total-degree grading is passed explicitly to `HomogeneousIdeal`, not installed with a local instance. |
| If an isomorphism exists then cX=cY | The first conjunct after each e is `cX = cY`. |
| Empty fibres have zero Euler characteristic and zero polynomial | The empty-fibre implication in each `HasFibreValues` gives `c=0`, `l=0`, `P=0`; its all-n equations then give every Euler characteristic zero. For a graph, emptiness gives `R=0`, and the universal ideal clause gives eventual coordinate dimensions zero. |
| No reducedness, pure dimension, connectedness or nonemptiness | None of these occurs among the hypotheses, the cover clauses, or the coordinate-ideal conditions. |

The polynomial-Proj and base-change definitions of projective space have separate
Lean types. `HasGraphValues` supplies an isomorphism `q` between these two models
over K, before quantifying e. This is a conclusion, not an additional hypothesis
or an arbitrary replacement for j_t. The embedding used in
`IsCoordinatePolynomial` is always the existing canonical `baseChangeEmbedding`
composed with the fixed graph. The universal homogeneous-ideal clause uses q only
to express that an ideal defines this same embedded scheme. One can take q to be
the identification matching standard coordinate charts. Any change of q over K
is a projective-space automorphism and preserves the degree-one polarization and
the coordinate Hilbert polynomial. Thus this type bridge changes no mathematical
clause of the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FinitePresentation`, `.Proper`,
  `.ClosedImmersion`: `Flat`, `LocallyOfFinitePresentation`, `IsProper`,
  `IsClosedImmersion`; finite presentation includes qc and qs.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Scheme.Opens`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  two projections and universal property. This supplies both the geometric-fibre
  specialization and all other products; no fibre definition is copied.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `IsInvertible` and
  `tensorPow` (including its actual zero-power unit and recursion).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` (publicly imports the
  canonical upstream tensor pullback): `Scheme.Modules.tensorPullback`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `ProjectiveSpace.twist`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `Scheme.Modules.eulerChar`, with `OverClass.ofHom` fixing each field action.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  tensor-product dependency; scheme modules use the existing specialized tensor.
- `Sheaf.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality`:
  `ProjectiveHilbertPolynomial.IsCoordinatePolynomial`, `geometricPoint`,
  `baseChangeEmbedding` and the coordinate-dimension definitions.
- `Sheaf.RingTheory.CoordinateQuotientGrading`: `coordinateQuotientPiece` and its
  unique induced `coordinateQuotientGrading`. This already-landed definition node
  is added to stmt_deps, since the every-ideal clause uses its pieces explicitly.
- `Sheaf.AlgebraicGeometry.ProjectiveCoordinateRingEulerPolynomial`:
  `coordinateQuotientImmersion` for the actual quotient-induced closed subscheme.
  This module was already a recorded proof dependency.

The modules of every recorded proof dependency are imported without `public`
unless already needed by the statement. The two unstated proof dependencies
`lem-sfb-flat-projective-twist-base-change-data` and
`lem-sfb-hilbert-graph-family-base-change` have no module in their current records;
their proof instructions remain in the theorem docstring. No proof prerequisite
is used as a missing statement construction.

Edge cases checked before writing: empty S (empty cover); empty X or Y fibres
(no isomorphism to a nonempty fibre); both fibres empty (zero polynomial, unit
homogeneous ideal allowed); n=0 (unit module, cX=cY forced by an isomorphism);
a=b=0 (one homogeneous coordinate); proper zero-dimensional schemes; nonreduced
proper curves; disconnected fibres with components of dimension zero and one;
unequal constants (no e, so graph conclusions are vacuous); arbitrary
characteristic; nonsaturated coordinate ideals (only eventual equality is
claimed). No edge case requires a correction.

Searches actually run through the prescribed msearch wrapper:

- leanfinder: "Flat projective curves affine base cover constant Euler
  characteristics fixed coordinate Hilbert polynomial isomorphism graphs" —
  eight Weierstrass-curve results; none states this theorem.
- leansearch: "Graphs of isomorphisms of projective flat curves have a fixed
  Hilbert polynomial locally on the base" — eight generic flatness and
  scheme-morphism-property results; no matching theorem.
- loogle: `AlgebraicGeometry, eulerChar` — rejected/unknown identifier
  AlgebraicGeometry, not evidence of absence. Repeated as `"eulerChar"` — twelve
  homological Euler-characteristic declarations, not this geometric assertion.
- grep: `graph.*[Pp]olynomial|[Pp]olynomial.*graph` in Mathlib/AlgebraicGeometry —
  no hit.
- rg in the project `lean/WeilConjectures` and `lean/Sheaf`: searched the item id,
  graph/polynomial combinations, `curveGraph`, `curve_graph`, and fixed polynomial
  names. The parent `ProjectiveCurveIsomGraphs` mentions this calculation only in
  its proof docstring; it states representability, not the numerical-cover lemma.
  Other hits concern polynomial Koszul graph classes or unrelated polynomial
  algebra. The existing locality and coordinate-ring modules are used rather
  than redefined.

Compilation: prescribed scompile.py compiled both the sandbox and final library
module names cleanly, each in 2.4 seconds, after explicit scheme coercions and
canonical grading arguments fixed elaboration. The only postponed theorem is
this item. No local/global library build or direct shared-repository edit was run.
The final import visibility and delivery preflight are checked again by deliver2.

## Second reading by Q14

This dispatcher brief forbids starting other agents and explicitly assigns
independent delivery review to the maintainer. Accordingly this section records
my second pass with the node, the Lean file and the source open; it does not claim
an independent second worker or replace the maintainer's independent review.

I checked every row above against the node and definitions. In particular I
checked the four numerical values are independent of K and t, while q and γ are
chosen after the appropriate field point/isomorphism; R is chosen before either
and is fixed over the whole open. The two factor projections and the field
projection identify γ uniquely with the graph. I checked the graph restriction
is pullback of M_t^n, and that the coordinate clause covers every homogeneous
ideal presentation rather than only the canonical vanishing ideal. The
polynomial-Proj bridge q is supplied over K without an input assumption. The
coordinate count was normalized to `((a+1)*(b+1)-1)+1` to match the dimension
index definitionally; positivity makes it the same coordinate count. I checked
zero powers, empty fibres, a=b=0 and unequal cX/cY separately. No source statement
or dependency interface was changed. The helper definitions are exposed,
public, real and assigned to this node; no hidden local notation, local
instance, private declaration, or statement-level let is present.
