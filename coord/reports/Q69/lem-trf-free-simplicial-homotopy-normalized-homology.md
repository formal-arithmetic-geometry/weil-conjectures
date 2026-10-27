## Worker report

The module `Sheaf.AlgebraicTopology.FreeSimplicialHomotopyNormalizedHomology` states
`AlgebraicTopology.free_normalized_homology_inverse_of_homotopy_equivalence`.
Its only proof is `sorry`. No definitions, dependency repairs, new nodes, or statement
corrections are needed. The item's original statement and dependency lists are unchanged.

Read the item and both statement-dependency nodes, their recorded declarations and docstrings,
and Stacks `simplicial.tex`, Tag 08P2 (`lemma-homotopy-equivalence`), first proof paragraph.
The theorem states the free-homology assertion used there. The accepted five-step proof is
included in the declaration docstring, including comparison naturality and both inverse
identities. The higher-face convention is explicit in both the node and Mathlib; no change
of normalization convention is assumed.

Hypothesis and clause correspondence:

- Simplicial sets `K,L`: `{K L : SSet.{u}}`, with arbitrary explicit universe `u`.
  `SSet` is `SimplexCategoryᵒᵖ ⥤ Type u`.
- The maps `u:K→L`, `v:L→K`: `(u : K ⟶ L) (v : L ⟶ K)` are natural transformations.
- The finite homotopy chain from `vu` to `id_K`: `hK : Relation.EqvGen
  (fun a b ↦ Nonempty (SSet.Homotopy a b)) (u ≫ v) (𝟙 K)`.
  The identical expression with `(v ≫ u)` and `(𝟙 L)` is `hL`. Category composition
  reads left to right: `u ≫ v` is the paper's `v ∘ u`. `EqvGen` is the inductively
  generated reflexive, symmetric, transitive closure, so witnesses give precisely finite
  chains, allow either cylinder orientation, and include length zero.
- Cylinder homotopy: Mathlib's `SSet.Homotopy a b` is a map `S ⊗ Δ[1] ⟶ T`
  with endpoint equations `ι₀ ≫ h = a`, `ι₁ ≫ h = b`. The tensor here is the pointwise
  cartesian product. `Δ[1]` consists of monotone maps into `[1]`; its endpoints have
  constant values zero and one, as verified in `SimplicialSet/Monoidal.lean` at
  `ι₀_app_snd_apply` and the definition of `ι₁`.
- Free simplicial abelian group `F(S)`: the actual functor composite
  `S ⋙ AddCommGrpCat.free`. `free.obj α = AddCommGrpCat.of (FreeAbelianGroup α)`;
  `free.map f = AddCommGrpCat.ofHom (FreeAbelianGroup.map f)`. This is the integral
  free abelian group on precisely the simplices of `S`, with every operator acting
  on the basis by that of `S`. Read `Grp/Adjunctions.lean:49-65` and
  `FreeAbelianGroup.map_of`, so no arbitrary map or chosen comparison enters.
- The specified `F(a)`: `Functor.whiskerRight a AddCommGrpCat.free`, whose components
  are the basis-induced free maps of the components of `a`.
- `N(Z)₀=Z₀`, intersections of `ker d_i` for `1≤i≤m`, differential `d₀` and zero
  differential leaving degree zero: `normalizedMooreComplex AddCommGrpCat.{u}`.
  Read `MooreComplex.lean:64-90,116-164`: `objX 0=⊤`, `objX (n+1)` is the finite
  intersection of kernels of `δ k.succ`; `objD` is induced by `δ 0`; `ChainComplex.of`
  inserts the zero differential outside the downwards natural-number shape.
- Restriction `N(a)` is `.map (Functor.whiskerRight a AddCommGrpCat.free)`;
  `NormalizedMooreComplex.map` at `MooreComplex.lean:128` factors each component through
  those kernel intersections, exactly the stipulated restriction.
- `H_n = ker ∂_n / im ∂_(n+1)` and its induced map: `HomologicalComplex.homologyMap ... n`.
  The abstract abelian homology is canonically that quotient; see
  `ShortComplex.abLeftHomologyData` and `ShortComplex.abHomologyIso` in
  `Mathlib.Algebra.Homology.ShortComplex.Ab`. The induced map is the standard homology
  map of the chain map, not an arbitrary isomorphism or another homology theory.
- Every `n≥0`: `(n : ℕ)` with no positive-degree restriction.
- First identity `H_n(N(F(v))) ∘ H_n(N(F(u))) = id`: the first conjunct is the forward
  homology map followed by the reverse map, equal to `𝟙` on the source homology.
- Second identity: the second conjunct is the reverse map followed by the forward map,
  equal to `𝟙` on the target homology.
- Bijectivity of the forward map: the third conjunct is `Function.Bijective` of its
  underlying additive homomorphism `.hom`.

Dependency declarations used:

- `def-weil-pbc-simplicial-object`: `Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
  `CategoryTheory.SimplicialObject`, `CategoryTheory.SimplicialObject.δ` and `.σ`.
- `def-weil-pbc-simplicial-set`: the recorded Mathlib match `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`. Its other recorded definitions
  (degeneracy, subcomplexes and finiteness) are not needed by this statement.
- Proof-only import for `lem-cbc-normalized-alternating-homotopy-equivalence`:
  `Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence`, especially
  `AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`
  and `AlgebraicTopology.inclusionOfMooreComplex`.
- Proof-only import for `lem-weil-pbc-simplicial-homotopy-free-chain-homotopy`:
  `Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance`,
  `SSet.Homotopy.chainComplexMap` and `.congr_homologyMap`.

Edge cases checked before writing: length-zero chains (`EqvGen.refl`), reversed cylinders
(`EqvGen.symm`), arbitrary finite concatenations (`EqvGen.trans`), empty simplicial sets
(the free group is zero), `n=0` (whole group and zero outgoing differential), identity
maps, and arbitrarily large/infinite simplex sets. Both simplicial sets share a common
arbitrary universe as in the recorded `SSet` interface; any pair can be placed in a common
universe. There is no Kan, nonemptiness, finiteness, additive-homotopy or positivity assumption.

Searches actually run using `batch2/msearch.py`:

- LeanFinder: `Finite chains of cylinder homotopies of simplicial sets induce mutually
  inverse homology maps on normalized free abelian chains`: 8 hits, including the
  normalized/alternating homotopy equivalence and chain-cylinder results. No exact theorem
  from finite simplicial homotopy chains to both free normalized inverse identities.
- Loogle: `"normalizedMooreComplex"`: 12 hits, supplying the normalized Moore functor,
  its objects, maps, kernel intersections and differentials; no statement of this theorem.
- Mathlib grep, subdirectory `AlgebraicTopology`:
  `normalizedMooreComplex|congr_homologyMap`: 25 hits, giving Moore normalization,
  normalized/alternating comparison and single-cylinder alternating homology invariance.
  These are ingredients, not an exact existing statement of the item.
- LeanSearch: `Simplicial set homotopy equivalence induces inverse maps on normalized
  free abelian homology`: 8 hits, including `HomotopyEquiv.toHomologyIso`, quasi-isomorphism
  results for chain homotopy equivalences and `Homotopy.homologyMap_eq`. Their input is
  already a chain homotopy equivalence, so none is the requested statement.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for normalization/free simplicial
  and homotopy terms found the parent `SimplicialAbelianSetHomotopyQuasiIso` and unrelated
  normalization modules. The parent proves a different statement about an additive map
  of simplicial abelian groups; its finite-chain hypothesis uses the same `EqvGen` encoding.
  Searches for this exact node id in `lean/WeilConjectures` (both `rg` and the requested
  `grep -rn`) returned no hits. `dag/lean_names_upstream.json` was also searched for
  `Homotopy|normalizedMooreComplex|AddCommGrpCat.free`; no exact existing declaration.

Validation: `scompile.py` compiled the module in sandbox and library module modes cleanly.
The first attempt identified a required public import of the homology-map API; adding
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` repaired that visibility issue.
`autoImplicit` is disabled; all parameters and universes are explicit. The theorem proof
remains `sorry`. No statement dispute or node fault was found.

## Second reading by Q69

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
