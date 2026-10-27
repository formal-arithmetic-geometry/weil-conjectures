## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitReductiveLocalGaussAtlas` states
`AlgebraicGeometry.splitReductive_local_gauss_atlas`, with one `sorry` and no new definitions.
The node's mathematical statement and five-step proof are unchanged. Its `stmt_deps` gains
the two already landed definition nodes `def-sfb-split-torus-over-ring` and
`def-sfb-reductive-torus-centralizer-terminology`, whose declarations the signature uses.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Nonzero commutative Noetherian local ring A | `A : Type u`, `[CommRing A]`, `[IsNoetherianRing A]`, `[IsLocalRing A]`; the last class extends `Nontrivial A` (Mathlib LocalRing/Defs.lean:30). |
| Group diagrams over Spec A | `H S : Grp (Over (Spec (.of A)))`: actual group objects in the category of A-schemes. |
| H smooth, affine, finite type | `[Smooth H.X.hom]`, `[IsAffine H.X.left]`, `[LocallyOfFiniteType H.X.hom]`, `[QuasiCompact H.X.hom]`. Finite type is the last two conditions, as in the recorded dependency. |
| Every geometric fibre reductive | `hred`, quantified over all algebraically closed fields `F : Type u` and every ring map `f : A →+* F`, applies `ReductiveTorusCentralizer.IsReductive` to the actual pullback group object. |
| Connected fibres and no nontrivial smooth connected normal unipotent subgroup | The existing `IsReductive` uses geometric connectedness and triviality up to group isomorphism of every closed normal connected algebraic unipotent subgroup after algebraic closure. Its `SolvableGroupStructure.IsUnipotent` includes smoothness, a faithful closed matrix representation, and matrix nilpotence on every algebraically closed extension. Over algebraically closed F this is exactly the node's condition. Smoothness, affineness and finite type of the fibres are already consequences of the corresponding global hypotheses. |
| S closed subgroup of H | `i : S ⟶ H` is a homomorphism of group objects, with `[IsClosedImmersion i.hom.hom.left]`. |
| Specified split-torus isomorphism of rank r ≥ 0 | `r : ℕ`, `e : S ≅ RingGroupSchemes.splitTorus A r`, an isomorphism of group objects, using the actual Laurent Hopf group and its finite products. |
| S geometrically maximal | `hmax` applies the existing `IsMaximalTorus` to the pullback of the same `i`, for every algebraically closed A-field; it means closed torus inclusion maximal under subgroup inclusion. |
| One integer d ≥ 0 | Existential `d : ℕ`, shared by all charts. |
| Finite nonempty index I | Existential `I : Type u`, `Finite I`, `Nonempty I`. A finite index can always be realized in this universe; no cardinality restriction results. |
| Displayed Laurent polynomial spectrum | `Spec (.of (MvPolynomial (Fin d) (AddMonoidAlgebra A (Fin r → ℤ))))`. The group algebra consists of finite sums of monomials with integral exponent vectors, hence precisely A[z_1^±,...,z_r^±]; the polynomial ring adjoins the d ordinary variables. |
| Each θ is an A-morphism | `θ` takes values in morphisms in `Over (Spec (.of A))`, with source `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A ...)))`. Thus the source has its canonical coefficient structure and θ commutes with the structure maps. |
| Open immersions | `∀ j : I, IsOpenImmersion (θ j).left`. |
| Images cover underlying H | `∀ x : H.X.left, ∃ j : I, x ∈ Set.range (θ j).left`. |

Dependency declarations read and used (the docstrings and full signatures were inspected):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` (bundled as `Grp`).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, used inside the recorded reductivity
  predicate, including its nonempty condition.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`:
  `AlgebraicGeometry.RingGroupSchemes.multiplicative` and `splitTorus`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive` and `IsMaximalTorus`.
  Their subordinate unipotence, base-change and torus definitions in
  `SolvableGroupStructure`, `ToriMultiplicativeType` and `StandardGroupSchemes` were read.

The public imports provide the statement dependencies. The already stated proof dependency
`Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts` is imported privately.
At inspection, `lem-sfb-local-split-root-data-weyl-lifts`,
`lem-sfb-relative-root-product-open-cell` and `lem-sfb-borel-root-product-coordinates`
have no recorded Lean declaration and no module, so cannot yet be imported. They are
proof-only inputs, not missing notions in this statement; their roles are retained in
the theorem's five-step proof docstring. The maintainer can add their proof imports on landing.

Source check: read Conrad's original PDF online at
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed p.136
(Definition 5.1.1 and connected-base discussion), pp.142--143 (Corollary 5.1.11),
and pp.143--144 (Theorem 5.1.13 and its proof). The finite atlas is the node's stated
consequence of these relative facts and geometric Bruhat decomposition; it is not claimed
to be the literal statement of Conrad 5.1.13. Locality gives connectedness of the base
and freeness of the root lines. No extra root data, chosen cell, henselianity or residue-field
hypothesis appears in Lean. The geometric hypotheses use precisely the same encoding
as the landed `splitReductive_dvr_cartan_decomposition`.

Edge cases checked before writing: the zero ring is excluded by `IsLocalRing`; for
the trivial group r=d=0 permits the coefficient ring A itself and a singleton cover.
For a split torus take d=0 and one chart. Rank r=0 and d=0 are permitted independently
in the signature. `Fin 0 → ℤ` is the trivial exponent group and `MvPolynomial (Fin 0)`
adds no variables. Nonreduced local bases such as k[ε]/ε², arbitrary residue fields,
and every characteristic remain allowed. All geometric fields are in the ring's universe,
which includes algebraic closures of the residue fields of the group scheme; thus the
geometric-point quantifiers are not vacuous. An empty cover is explicitly forbidden.

Searches actually run, using `msearch.py NB lem-sfb-split-reductive-local-gauss-atlas`:

- LeanFinder: `A smooth affine reductive group scheme with a split maximal torus over a local ring admits a finite open cover by affine spaces times split tori`.
  Eight hits, including `Scheme.affineBasisCover`, `affineCover`, `AffineOpenCover` and
  `affineRefinement`; these give arbitrary affine covers, not the Laurent polynomial atlas.
- Loogle: `AlgebraicGeometry.IsReductive, AlgebraicGeometry.SplitTorus, MvLaurentPolynomial`.
  Zero hits; reported unknown identifier `AlgebraicGeometry.IsReductive`.
- Mathlib grep: `Reductive|reductive|MaximalTorus|MvLaurentPolynomial`.
  Four hits, all about reductive Lie algebras; no relative group atlas.
- LeanSearch: `Finite open Laurent polynomial atlas for a split reductive group scheme over a local ring`.
  Eight hits: Laurent polynomials and Laurent series, their localization and coefficient
  instances, and `Scheme.affineOpens`; no theorem matching this node.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `Reductive|reductive|SplitTorus|splitTorus|MaximalTorus|IsUnipotent|Laurent.*(Atlas|atlas)|localGauss`.
  Found the already landed torus and reductivity definitions and DVR Cartan theorem;
  no local-ring Gauss atlas. A separate node-id search in `lean/WeilConjectures` had no hits.
- `rg` for `relative.*atlas|gauss.*atlas|splitReductive.*atlas|local_gauss|localGauss` over
  both source trees and `dag/lean_names_upstream.json` found unrelated relative atlas
  text and no existing declaration for this result.
- DAG search for the existing notions located `def-sfb-split-torus-over-ring` and
  `def-sfb-reductive-torus-centralizer-terminology`; `tools/blueprint_refs.py search
  'split reductive'` supplied no matching unit statement. No new definition node is needed.

No statement dispute, dependency repair, statement correction, or hollow definition.
Initial compilation identified a redundant `[Nontrivial A]` binder; it was removed because
`IsLocalRing A` already extends it. All validation uses the prescribed wrappers.

## Second reading by NB

This is the author's second reading under the dispatcher/direct-delivery protocol, not
an independent worker review; the maintainer supplies the independent review. I reopened
the node and the finished signature and checked the table above against both.
The base hypotheses, group structures, closed inclusion, specified group isomorphism,
geometric reductivity and geometric maximality each have their own binder or predicate.
The conclusion has one common d, a finite nonempty index, canonical A-algebra spectrum
sources, A-morphisms, open immersions and pointwise coverage, with no omitted clause.
In particular the morphisms are in `Over`, not arbitrary scheme maps, and the torus
isomorphism is in `Grp`, not merely an isomorphism of underlying schemes.
I read the nested `IsReductive`/`IsUnipotent` definitions to check smoothness and faithfulness,
and the rank-zero recursion of the split torus. I also checked that the chart ring uses
the same rank r, not an existential rank unrelated to S. The sole mismatch found in the
first draft was duplicate nontriviality, corrected as explained above. No mathematical
statement change was needed. There are no new nodes or dependency modules to review.
