## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceEventuallyFibreDimension` states
`AlgebraicGeometry.AlgebraicSpace.eventually_geometric_fibre_dimension_le_of_isLimit`.
Its sole theorem has proof `sorry`; there are no new definitions or helper theorems.
The node statement, proof, and proof dependencies are preserved.

Hypothesis and clause correspondence:

- The absolute base is `Spec (.of (ULift.{u} ℤ))`. Its lift puts Spec Z in the same
  scheme universe without changing the scheme. `X₀ : AlgebraicSpace ...` uses the
  recorded fppf-sheaf definition, without requiring the space to be a scheme.
- The small nonempty directed index set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. The index universe agrees with the scheme
  universe. No least index, linear order or countability is assumed.
- `D : Iᵒᵖ ⥤ Over ...` is the inverse system of schemes over Spec Z;
  `[∀ i, IsAffine (D.obj (op i)).left]` makes all bases affine, and `haff`
  records their affine transition maps. `c : Cone D` and `hc : IsLimit c`
  specify T and its actual limiting projections. A limit over Spec Z is the same
  scheme limit with its canonical structural map.
- `i₀ : I`, `X₀` and `f₀ : X₀.obj.obj ⟶ yoneda.obj (D.obj (op i₀))`
  are the fixed stage and the space morphism to that represented scheme.
- Finite presentation is exactly the three hypotheses `hqc : MapIsQuasiCompact f₀`,
  `hqs : MapIsQuasiCompact (pullback.diagonal f₀)` and
  `hlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X₀ ... f₀`.
  The last predicate tests every representable etale source chart; because the
  target is a scheme it is the usual equivalent chart form of the node's condition.
  There is no separatedness, flatness, purity or representability hypothesis on f₀.
- `d : ℕ` is the integer d ≥ 0, without excluding zero.
- `hdim` quantifies over every `Ω : Type u` with `[Field Ω] [IsAlgClosed Ω]`
  and every geometric point `a : Spec (.of Ω) ⟶ c.pt.left`.
  `Over.homMk` packages the composite `a ≫ (c.π.app (op i₀)).left` over Spec Z;
  `Limits.pullback f₀ (yoneda.map ...)` is its actual presheaf fibre product.
  Pullback pasting identifies this with the geometric fibre of the limiting
  family `X₀ ×_{T₀} T → T`. The comparison is canonical and introduces no
  arbitrary map or choice of fibre model.
- `topologicalKrullDim (Point (...)) ≤ (d : WithBot ℕ∞)` is precisely the
  topological Krull bound on the fibre, using the existing point classes and atlas
  topology. The conclusion `∃ (i : I) (hi : i₀ ≤ i), ∀ (j : I) (hij : i ≤ j)`
  gives every later stage, including i itself. Its inner quantifiers again range
  over every algebraically closed field and every geometric point of T_j.
  The transition used is `D.map (homOfLE (le_trans hi hij)).op`, so the fibre
  is exactly `X₀ ×_{T₀} Spec Ω`, canonically the fibre of `X_j → T_j`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and its universal property. The geometric-fibre dependency records
  this same construction; here geometric points range over all algebraically
  closed fields, as the item's own statement and reviewed proof require.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` and
  `MapToSchemeIsLocally`. Only these general predicates are used; the curve
  predicate, and hence its bound one or properness, is not assumed.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`.
- The last three existing definition nodes were added to stmt_deps to cite these
  already landed general interfaces; no dependency node was edited.
- The size convention is implemented by explicit `universe u`, Scheme.{u}, and
  fields and index type in Type u; point classes live in Type (u+1).

Proof imports follow all currently stated proof dependencies: the affine-etale
neighbourhood theorem, affine finite-type algebra theorem, scheme limit dimension
bound, algebraic-space fibre products and etale covers, quasi-compactness locality,
field-extension dimension equality, affine-transition limits, and the Mathlib
finite-type, affine, separated and pullback interfaces. The two proof nodes
`lem-sfb-quasiseparated-space-atlas-dimension` and
`lem-sfb-space-relative-dimension-base-change` currently have no recorded Lean module,
so there is no import to add for them. Their applications remain in the seven-step
proof docstring, matching the DAG. They are not prerequisites to stating the item.

Sources opened: spaces-limits.tex, Situation 084W and the complete statement/proof
of Tag 0D4K; spaces-morphisms.tex, Tags 06LR and 04NS(1). The affine-chart proof and
its passage from ordinary to all geometric fibres are retained in the docstring.

Edge cases checked: d = 0; empty space, empty affine base and empty fibres;
singleton index; directed preorder with no least element; non-surjective
transitions; mixed-dimensional fibres; algebraically closed extensions larger than
a chosen residue-field algebraic closure. Empty fibres have dimension bottom, so
impose no condition. No nonemptiness of a fibre or equality of dimensions is added.
All geometric fields within the chosen big-site universe are included.

Searches actually run using msearch.py, group NW, this item:

- leanfinder: "For finitely presented algebraic spaces over an inverse limit of affine
  schemes geometric fibre dimension at most d eventually holds at every later stage".
  Eight hits, including scheme limit factorization and local finite presentation,
  but no algebraic-space fibre-dimension eventual bound.
- loogle: `AlgebraicGeometry.AlgebraicSpace, topologicalKrullDim`.
  Zero hits; AlgebraicGeometry.AlgebraicSpace is unknown to the Mathlib index.
- grep: `eventually.*[Dd]im|[Dd]im.*eventually|AlgebraicSpace`, subdirectory
  AlgebraicGeometry. Zero hits.
- leansearch: "A geometric fibre dimension bound for a finitely presented algebraic
  space over an inverse limit of affine schemes holds at every sufficiently late stage".
  Eight hits on scheme affine-limit descent, scheme fibres and finite presentation;
  none states the item.
- Direct rg searches in lean/WeilConjectures and lean/Sheaf for eventual dimension,
  geometric fibre dimension, the item id and the proposed theorem name: no exact
  declaration. Found the existing scheme-only LimitFibreDimensionBound and the
  consumer CurveLimitPreservation; the former is a proof dependency, not this result.
  `grep -rn 'lem-sfb-space-eventually-fibre-dimension' lean/WeilConjectures`
  returned no hits.
- Direct source searches found the already landed MapIsQuasiCompact,
  MapToSchemeIsLocally, Point and pointTopologicalSpace, whose full definitions
  and source docstrings were opened instead of introducing private copies.

No statement correction or STATEMENT-DISPUTED issue was needed.

Validation: scompile.py compiled the theorem in sandbox and library module modes
in 1.6 and 1.7 seconds respectively, with no errors or unexpected warnings.

## Second reading by NW

Independent maintainer reading (2026-10-24) of delivery 197334d9; the earlier text of this
section was the author's own second pass. Node clauses against the Lean:

- Base Spec Z, size convention: `Spec (.of (ULift.{u} ℤ))`, `Scheme.{u}`, `I : Type u`,
  `Ω : Type u` — same encoding as the landed `IsProperCurveFamily`. Correct.
- Small nonempty directed set: `[Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`, no least
  element or order assumed. Correct.
- Inverse system of affine schemes with affine transitions: `D : Iᵒᵖ ⥤ Over Spec Z`,
  `IsAffine (D.obj (op i)).left`, `haff`. T = lim via `c`, `hc : IsLimit c`; for nonempty
  directed (connected) I the forgetful functor `Over S ⥤ Scheme` creates the limit, so this is
  the scheme limit. Correct.
- Finitely presented f_{i₀} : X_{i₀} → T_{i₀}: `MapIsQuasiCompact f₀`,
  `MapIsQuasiCompact (pullback.diagonal f₀)` and
  `MapToSchemeIsLocally (@LocallyOfFinitePresentation)` — exactly the finite-presentation
  conjuncts of the landed `IsProperCurveFamily` (def-sfb-proper-curve-moduli). No extra
  separatedness, flatness, properness or representability hypothesis. Correct.
- X_i, X, f_i, f and geometric fibres: the fibre of f (resp. f_j) at `a : Spec Ω ⟶ T`
  (resp. `T_j`) is written `pullback f₀ (yoneda.map (Over.homMk (a ≫ π_{i₀})))`
  (resp. along `a ≫ D.map (i₀ ≤ j)`). By pullback pasting this is canonically isomorphic to
  (X₀ ×_{T₀} T) ×_T Spec Ω, resp. (X₀ ×_{T₀} T_j) ×_{T_j} Spec Ω; `Point` and its topology
  are functorial in presheaf isomorphisms, so the Krull dimension is the same. Same encoding
  of geometric fibres as `IsProperCurveFamily`. Every algebraically closed Ω and every
  geometric point is quantified in both hypothesis and conclusion. Correct.
- Dimension: `topologicalKrullDim (Point …) ≤ (d : WithBot ℕ∞)`, d : ℕ (d ≥ 0, d = 0
  included); empty fibres have dimension ⊥ and impose no condition. Correct.
- Conclusion: `∃ i, i₀ ≤ i ∧ ∀ j ≥ i, …` — every later stage, quantifier order as in the
  node. Correct.

Records: `lean.statement` is verbatim the signature in the file. Added stmt_deps
def-sfb-proper-curve-moduli (MapIsQuasiCompact, MapToSchemeIsLocally),
def-a1-space-point-topology (pointTopologicalSpace) and def-a1-algebraic-space-point-classes
(Point) are landed definition nodes owning the cited declarations; no cycle. Docstrings
carry the Stacks places (0D4K, 084W, 06LR, 04NS), `(blueprint: …)` and the node's seven proof
steps (step 7 via lem-sfb-space-relative-dimension-base-change). Proof is `sorry`, no new
definitions, no pro-étale substitute. All private proof imports exist in the live tree.
No mismatch found.
