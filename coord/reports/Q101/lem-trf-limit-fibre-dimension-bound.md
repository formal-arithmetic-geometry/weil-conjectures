## Worker report

The module `Sheaf.AlgebraicGeometry.LimitFibreDimensionBound` states
`AlgebraicGeometry.limit_fibre_dimension_bound`, with its proof exactly `by sorry`.
The two helper definitions are real canonical constructions: `limitFibreComparison` is
`pullback.lift` of the transition map and the later structure map, with naturality as its
commutativity witness; `limitFibreMap` is the limit lift of the postcomposed source cone.
No arbitrary comparison or limit map is a parameter. There are no new DAG notions or
repairs of dependencies and no change to the natural-language statement.

Source read: `literature/stacks-project/limits.tex`, lines 4504–4553,
Tag 05M5, `lemma-limit-dimension`. Its four assumptions and its conclusion are precisely
those of this node. The node has expanded the proof into seven affine-cover steps;
the theorem docstring records each step and the dependency nodes that it uses.

The correspondence, hypothesis by hypothesis and clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| Nonempty directed set I | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]` |
| Inverse systems of schemes S_i and X_i | `S X : Iᵒᵖ ⥤ Scheme.{u}`; functor laws give identity and composition of transitions |
| Each S_i quasi-compact | `[∀ i : I, CompactSpace (S.obj (op i))]`, Mathlib's compactness without a Hausdorff assumption |
| Each S_i quasi-separated | `[∀ i : I, QuasiSeparatedSpace (S.obj (op i))]`, the qc intersection condition on the scheme's space |
| Affine base transition for i ≤ j | `hSaff`, using `S.map (homOfLE hij).op : S_j ⟶ S_i` |
| An inverse system of morphisms X_i → S_i | `τ : X ⟶ S`; naturality is the commuting square at every transition |
| Every morphism is finite type | `hfinite i`, exactly `LocallyOfFiniteType (τ.app (op i)) ∧ QuasiCompact (τ.app (op i))` |
| Canonical comparison X_j → X_i ×_{S_i} S_j is closed | `hclosed hij : IsClosedImmersion (limitFibreComparison τ hij)`; the helper's target is that pullback and its two projections are the prescribed maps |
| Limit S | `cS : Cone S`, `hcS : IsLimit cS`; S itself is `cS.pt` |
| Limit X and induced f | `cX : Cone X`, `hcX : IsLimit cX`; X is `cX.pt` and f is `limitFibreMap τ cS hcS cX` |
| Integer d ≥ 0 | `d : ℕ`; this is the exact parametrization of nonnegative integers, including zero |
| Every scheme-theoretic fibre at the limit has dimension at most d | `hdim`, quantifying over **all** `s : cS.pt`, and using Mathlib's `Scheme.Hom.fiber` and `topologicalKrullDim` |
| Some finite stage has the bound for every fibre | `∃ i : I, ∀ s : S.obj (op i), topologicalKrullDim ((τ.app (op i)).fiber s) ≤ (d : WithBot ℕ∞)` |

All universes are explicitly declared. The index and the schemes use the same `u`, as
required by the project limit convention. No independent smaller test universe or finite
index restriction is introduced. The canonical map is independent of the source limit
witness, which is used to assert that the source cone really is limiting.

Dependency declarations read and used:

- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom`,
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`, definition and docstring at lines 43–48.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, in `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  and `.QuasiCompact`, definitions and docstrings at lines 39–47 and 38–46 respectively.
  The node's record explicitly requires their conjunction for finite type.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, lines 42–46, closed embedding
  with surjective maps on stalks.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`, lines 35–41, dimension of irreducible closed subsets
  valued in `WithBot ℕ∞`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.lift` and its
  projections, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, lines 92–131.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `Mathlib.AlgebraicGeometry.Fiber`, lines 37–46, pullback along `fromSpecResidueField`.
- `lem-weil-pbc-limit-affine-transition`: module
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`, declaration
  `AlgebraicGeometry.exists_limit_affine_transition`. Its full current source was read
  using `scompile.py --source`; the directed index, limit cones, affine projections,
  open-chart limits and affine colimit comparison agree with the node. This module is
  publicly imported. The theorem quantifies over arbitrary supplied limiting cones,
  so it does not select a particular witness of the existential limit theorem.
- `def-weil-pbc-scheme-conventions` explicitly fixes no additional notion; its record
  points to the Mathlib properties above. There is no convention declaration to import.

Proof imports include the recorded modules
`Sheaf.AlgebraicGeometry.AffineLimitFibreDimensionBound`,
`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`,
`WeilConjectures.Mathlib.Topology.KrullDimension`, and
`WeilConjectures.Topology.DimensionSupremumLocalDimensions`, as well as the Mathlib
modules containing the affine-cover, open/closed base-change and affine-pair statements.
The local and current server source were read where needed. The current upstream dimension
supremum module is used, following its updated record, rather than its retired side copy.

Edge cases checked:

- Empty bases are allowed; universal quantification over their points is empty and any
  stage can witness the conclusion. No `Nonempty` condition is imposed on schemes.
- Empty fibres have dimension `⊥`, so both occurrences of the dimension bound include
  them. In particular the all-empty-source system is covered.
- `d = 0` is included; no positivity or existence of fibre points is assumed.
- Constant and singleton diagrams recover the stated bound; identity comparisons are
  closed immersions. The conditions do not require strict inequalities of indices.
- Preorders, including distinct mutually comparable equal stages, are admitted; functor
  laws make the transition maps between equivalent indices isomorphisms. For the later
  affine proof, a directed preorder may be replaced by its partial-order quotient with
  chosen representatives before invoking the affine lemma's partial-order interface.
- No finiteness, finite presentation, flatness, separatedness, geometric-fibre, or
  surjectivity assumption has been added. Closed immersion does not mean a Cartesian
  comparison: nonisomorphic closed subschemes remain allowed.

Searches actually run for this delivery:

1. `msearch.py ... leanfinder` with query “For inverse systems of finite type scheme
   morphisms over qcqs bases with affine transitions and closed immersion comparison
   maps, a bound on fibre dimensions at the limit descends to a finite stage”. Eight
   hits: `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`,
   `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`,
   `ExistsHomHomCompEqCompAux.exists_index`, `exists_appTop_π_eq_of_isLimit`,
   `exists_mem_of_isClosed_of_nonempty`, `ExistsHomHomCompEqCompAux.i'`,
   `exists_map_preimage_le_map_preimage`, and `exists_mem_of_isClosed_of_nonempty'`.
   These concern morphism approximation, sections, opens and nonempty limits, not
   the fibre-dimension bound; their returned signatures/docstrings do not match.
2. `msearch.py ... loogle 'topologicalKrullDim, Scheme.Hom.fiber'`: zero hits,
   with an unknown-identifier diagnostic for `Scheme.Hom.fiber`.
3. `msearch.py ... grep '(limit|Limit).*(fibre|fiber).*(dim|Dim)|(fibre|fiber).*(dim|Dim).*(limit|Limit)' AlgebraicGeometry`:
   zero hits.
4. `msearch.py ... leansearch` with query “An upper bound on all scheme theoretic
   fibre dimensions of an inverse limit of finite type morphisms with affine base
   transitions and closed immersion comparison morphisms holds at some finite stage”.
   Eight hits include `Scheme.isAffine_of_isLimit`, `Scheme.compactSpace_of_isLimit`,
   approximation of compact/affine opens, zero-section detection, and finite-morphism
   fibre finiteness. None gives this dimension descent theorem.
5. `rg` in both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared
   `lean/Sheaf`, first for the item id and proposed declaration/helper names (also in
   `dag/lean_names_upstream.json`), then for fibre/fiber, dimension/KrullDim, and
   limit/colimit combinations. No name collision or exact theorem was found. The
   existing affine theorem `exists_stage_fibre_dimension_le` was found and read:
   it covers ring diagrams only, so it is the proof dependency rather than an exact
   match for the scheme statement.

Validation: the final module is compiled with the prescribed `scompile.py` wrapper;
no error or unexpected warning. No mathematical statement correction or disputed clause.

## Second reading by Q101

This is the worker's self-check; the independent review is the maintainer's, as specified
in the remote-worker brief. Reopened the source statement (05M5, four numbered hypotheses),
the full node and the Lean signature. Each source hypothesis is present in the table above.
The source has ordinary scheme-theoretic fibres over every base point, exactly the two
quantifications using `.fiber`; no replacement by geometric fibres or only closed points.
Checked the direction `j → i` of the contravariant transitions and the order of the two
factors of the comparison pullback. Naturality supplies precisely
`X_j → X_i → S_i = X_j → S_j → S_i`. The induced limit map is the genuine universal map,
not an arbitrary morphism assumed to have the bound. An early draft passed that map with
its normalization equation; it was replaced by `IsLimit.lift` of `Cone.postcompose` so
that the canonical map is fully constructed. No unresolved mismatch remains.
