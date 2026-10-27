## Worker report

The module `Sheaf.AlgebraicGeometry.NodalFamilySplitPointNeighbourhood` states
`AlgebraicGeometry.exists_nodal_family_split_point_neighbourhood`, with its whole proof
`sorry`. No definitions, helper theorems, or dependency modules are introduced.

Source read: `literature/stacks-project/curves.tex`, Tag 0CBY,
`lemma-etale-local-structure-nodal-family`, first proof, especially the second paragraph
(lines 5126 onward in this checkout). It realizes the finite separable residue extension
and the splitting quadratic extension by an étale base neighbourhood, then base changes.
The affine refinement and total-space residue compatibility are the five existing DAG
proof steps, reproduced in the theorem's docstring.

Clause-by-clause correspondence:

- `X₀ S₀ : Scheme.{u}` and `f₀ : X₀ ⟶ S₀` are precisely the two schemes and morphism.
- `[Flat f₀]` is flatness. `[LocallyOfFinitePresentation f₀]`, `[QuasiCompact f₀]`,
  `[QuasiSeparated f₀]` together are finite presentation, with exactly the node's meaning.
- Each of X₀ and S₀ has `LocallyOfFiniteType` and `QuasiCompact` of
  `specULiftZIsTerminal.from` as hypotheses. These are finite type over Spec ℤ.
  The lifted integers give the same base in every scheme universe, without imposing
  affinity or separatedness on either scheme.
- `hgeom` quantifies over every algebraically closed field Ω in the scheme universe and
  every geometric point `g : Spec (.of Ω) ⟶ S₀`. The geometric fibre is `pullback f₀ g`.
  `IsPureDimension 1` expresses the equidimension clause; it holds vacuously on the empty
  scheme, so writing it without an explicit empty disjunct retains precisely the empty
  case. Every point has the completion requirement only when no open neighbourhood of
  it has smooth structural morphism. This is nonsmoothness at that point, not global
  nonsmoothness of the fibre morphism.
- `Orgogozo.IsOrdinaryDoublePoint (pullback.snd f₀ g) z` is exactly the Ω-algebra
  completion equation. Its definition is an actual ring equivalence from
  `AdicCompletion (IsLocalRing.maximalIdeal (F.presheaf.stalk z)) (F.presheaf.stalk z)`
  to `MvPowerSeries (Fin 2) Ω ⧸ Ideal.span {X 0 * X 1}`, together with compatibility
  with every scalar through the canonical structural map. It adds no rationality,
  closedness, connectedness, or nonemptiness condition.
- `x₀ : X₀` is the prescribed point. `hx₀` states that f₀ is not smooth on any open
  neighbourhood of x₀. The base point s₀ and its field k are used as the expressions
  `f₀ x₀` and `S₀.residueField (f₀ x₀)`; neither is independent additional data.
- The existential `V₁`, `e`, `v₁`, `x₁` supplies the pointed base neighbourhood and
  the total-space point. `IsAffine V₁` and the finite-type conjunction for its
  canonical map to Spec ℤ give the two required properties of V₁.
- `Etale e` and `e v₁ = f₀ x₀` express the pointed étale map.
- `x₁ : pullback f₀ e` makes X₁ exactly the stated fibre product. Its two projection
  equalities give images x₀ and v₁, with no surrogate total space.
- `(e.residueFieldMap v₁).hom.Finite` is finiteness of K/k, and the explicit
  `@Algebra.IsSeparable ... (e.residueFieldMap v₁).hom.toAlgebra` uses that very
  residue-field map as the algebra structure. Its source is κ(e(v₁)), identified
  with κ(f₀(x₀)) by the preceding equality. There is no arbitrary field embedding.
- `Flat (pullback.snd f₀ e)` and `LocallyOfFinitePresentation (pullback.snd f₀ e)`
  give the asserted properties of the base-changed morphism f₁.
- `Function.Bijective ((pullback.snd f₀ e).residueFieldMap x₁).hom` says its induced
  residue-field map is an isomorphism. Its source is κ(f₁(x₁)) = κ(v₁), by the
  projection equality already required. A bijective field homomorphism is exactly
  a field isomorphism; no replacement embedding has been chosen.
- The existential `z₁ : (pullback.snd f₀ e).fiber v₁` with `fiberι ... z₁ = x₁`
  is the point of the scheme-theoretic fibre corresponding to x₁. `fiberι` is an
  embedding, so this is unique and is only an explicit expression of the node's
  implicit identification of fibre points. The final `Orgogozo.IsOrdinaryDoublePoint`
  uses `fiberToSpecResidueField v₁`, hence is the stated K-algebra isomorphism of
  the completed fibre local ring with K[[u,v]]/(uv), not the total-space completion.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`; `Mathlib.AlgebraicGeometry.ResidueField`:
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `.FinitePresentation`, `.FiniteType`,
  `.QuasiCompact`, `.QuasiSeparated`, `.Etale`, `.Smooth`: the recorded morphism
  classes. Pointwise smoothness is rendered by open neighbourhoods, as in the
  previously landed splitting theorem; no extra finite-presentation assumption
  is needed for such a predicate.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `RingHom.toAlgebra`;
  `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`;
  `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.Paper.OrgogozoInductionData`: `Orgogozo.IsOrdinaryDoublePoint`,
  `Orgogozo.nodeRing`, `Orgogozo.localScalar`. The existing landed node
  `def-trf-orgogozo-induction-data` is added to stmt_deps to cite this reuse.
  This is the only stmt_deps addition, under STMT_DEPS MAY GAIN LANDED NODES.
- `Mathlib.AlgebraicGeometry.Limits`: `specULiftZIsTerminal` gives the canonical
  integer structure maps.
- Proof imports retain `nodal_point_finite_separable_splitting` from
  `Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting`,
  `nodal_family_fitting_singular` from
  `Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular`,
  `Scheme.exists_etale_neighbourhood_prescribed_residueField` from
  `WeilConjectures.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField`, and
  the iterated-base-change comparisons in
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
  Other proof dependencies are the Mathlib facts already supplied by the imported
  finite-type, finite-presentation, flat, étale, fibre, and pullback modules.

Edge cases read before writing: empty fibres are allowed; an empty X₀ has no x₀,
so no false existence is demanded. Disconnected geometric fibres and reducible curves
are allowed because only pure dimension is imposed. No properness or separatedness
of X₀, S₀, or f₀ is assumed. Split and nonsplit nodes, including separable quadratic
splitting in characteristic 2, are covered: the conclusion has no prescribed extension
degree or characteristic constraint. The node xy=0 over a field already split permits
K=k. The fibre completion is distinct from the total-space completion in a smoothing.
All types and universes are explicitly bound; same-universe geometric tests match
Mathlib's convention and include an algebraic closure of every residue field.

Searches:

- `msearch.py ... leanfinder`: “A flat finitely presented nodal curve family admits an
  etale base neighbourhood where a chosen nonsmooth point is rational with split
  completed fibre ring”: 8 hits, smooth charts and étale loci, no match.
- `msearch.py ... loogle`: `AlgebraicGeometry.Etale,
  AlgebraicGeometry.LocallyOfFinitePresentation`: 2 hits, the flat/unramified
  characterization of étale morphisms, no split-point neighbourhood theorem.
- `msearch.py ... leansearch`: “etale base neighbourhood making a nodal fibre point
  rational and split”: 8 hits concerning étale loci/localizations, no match.
- `msearch.py ... grep 'nodal|splitNode|split_node' AlgebraicGeometry`: no Mathlib hits.
- `rg` on `lean/WeilConjectures` for the same nodal patterns found only unrelated
  examples in comments/docstrings. The exact item-id search had no hits there.
- `rg` on `lean/Sheaf` found the nodal splitting theorem over a field, the Fitting
  singular theorem, the larger étale local-model theorem, and the reusable ordinary
  double point predicate. None states this pointed base neighbourhood conclusion.
  `HasNodalGeometricFibres` was specifically rejected: it adds connectedness and
  nonemptiness, and its completion comparisons are only ring isomorphisms.
- The proposed full declaration name was searched in Mathlib, WeilConjectures,
  Sheaf, and `dag/lean_names_upstream.json`: no existing declaration.

No statement correction, new definition node, dependency repair, or unresolved
STATEMENT-DISPUTED issue is needed. The former example module CompactObject is withdrawn
in the current checkout; its node records the upstream existing definition instead.
The module follows the required module/public-import/public-section conventions.

## Second reading by Q46

I made a separate second pass with the node and final Lean signature open. This is a
self-review: the dispatcher explicitly forbids starting another agent; the maintainer's
independent review follows delivery. I checked all four finite-presentation hypotheses,
the separate finite-type conditions on both original schemes, and the universal geometric
fibre hypothesis. In particular the latter uses algebra-compatible completed equations
and permits empty or disconnected fibres. I checked the affine/finite-type/étale clauses,
the pointed image equalities, the finite and separable residue extension, both properties
of f₁, total-space rationality, and the completion at the corresponding point of the
actual scheme-theoretic fibre. Both residue-field maps are the canonical maps of the
specified morphisms. Equalities identify their source fields with the fields named in
the prose. The fibre point is unique, so making it explicit adds no choice condition.
No clause mismatch was found, and no source statement change was made. The landed
Orgogozo definition node was cited explicitly rather than defining a duplicate predicate.

Validation: the prescribed `scompile.py Q46 ... NodalFamilySplitPointNeighbourhood.lean`
completed successfully for both sandbox and library checks, with no errors or warnings.
The local shape check confirms only `lean` and the authorized `stmt_deps` addition differ
from the item; the recorded theorem signature is verbatim and the maximum line width is 92.
