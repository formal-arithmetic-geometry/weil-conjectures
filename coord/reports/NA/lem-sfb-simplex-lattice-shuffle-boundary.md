## Worker report

The delivery states `AlgebraicTopology.SimplexLatticeShuffle.shuffle_boundary_augmentation_naturality`
in `Sheaf.AlgebraicTopology.SimplexLatticeShuffleBoundary`. This is the single postponed theorem.
All eleven helper definitions have real data and are listed in `lean.declarations`. The natural-language
statement, dependencies, proof, and stage-1 review are unchanged. The earlier worker's stale-dispatch
report confused the completed stage-1 split with stage 2: the live node had no `lean` record.

Source read: the complete node (including its ten proof steps), its sole statement dependency, and
paragraph (3) of the main-20261015 direct-image blueprint proof. That paragraph motivates the
comparison but contains no combinatorial calculation; the node correctly labels the calculation
agent-written and Weibel 8.5 WANTED. No claim is made to have read Weibel. The complete labeled
cancellation argument is reproduced in the theorem docstring for stage 3.

Hypothesis and clause correspondence:

- Integral coefficients and chain complexes: `ChainComplex (ModuleCat.{0} ℤ) ℕ`, built by
  `AlternatingFaceMapComplex.obj` and `ModuleCat.free ℤ`. The dependency explicitly permits
  nonnegative complexes, understood as extended by zero in negative degrees. Nothing in the
  asserted identity concerns negative degrees. The finite generators and ℤ need only universe zero;
  all universe choices are fixed explicitly, with no auto-bound variables.
- Nonnegative integers p,q and degrees a,b: the theorem quantifies independently over
  `(p q a b : ℕ)`. No positivity or injectivity assumption is added.
- `U(p)_a`: `(simplexChains p).X a` is the free integral module on
  `(Δ[p] : SSet.{0}) _⦋a⦌`. Read `SSet.stdSimplex.objEquiv`, `asOrderHom`, and `objMk`:
  these generators are exactly order-preserving functions `Fin (a+1) →o Fin (p+1)`.
  No quotient by degeneracies is taken, so repeated entries survive.
- Alternating deletion differential and its zero-degree convention: the existing
  `AlternatingFaceMapComplex.obj_d_eq` gives the signed sum of faces;
  `SSet.stdSimplex.δ_objEquiv_symm_apply` identifies a face with precomposition by
  `SimplexCategory.δ`, whose order map is `Fin.succAboveOrderEmb`. The complex's
  `d 0 0` is zero by its shape. Consequently the first theorem clause also includes a=b=0.
- `V(p,q)_n`: `(productChains p q).X n` is the free module on
  `(Δ[p] ⊗ Δ[q] : SSet.{0}) _⦋n⦌`. `SSet.prodStdSimplex.objEquiv` identifies these generators
  with coordinatewise monotone pair strings; its `objEquiv_δ_apply` gives exactly deletion.
  This is Mathlib's existing product-simplex construction, not a replacement carrier.
- A partition μ⊔ν of the a+b step positions: `LatticePath a b` consists of monotone coordinate
  functions `w : Fin (a+b+1) → Fin (a+1) × Fin (b+1)` with coordinate sum k at vertex k.
  The first vertex is (0,0), the last is (a,b), and monotonicity together with successive sums
  k and k+1 forces exactly one unit horizontal or vertical step. Thus horizontal positions
  form μ of cardinality a and vertical positions form its complement ν of cardinality b.
  Conversely the prefix counts in the node give exactly one such path. In particular this
  indexing neither drops nor repeats any partition. This is a finite subtype of a finite
  function type, and its `Fintype` is supplied by `Fintype.ofFinite` on that subtype.
- Prefix counts A_k and B_k: they are `(w.val k).1` and `(w.val k).2`. The previous bijection
  shows these are precisely the counts in the displayed formula. `pathSimplex` composes the
  two input order homomorphisms with these coordinate functions, producing
  `(u_(A_k),v_(B_k))` in the existing product-simplex type.
- ε(μ,ν): `pathSign` is (-1) to the number of positions i<j where i is vertical and j is
  horizontal. Those are exactly the cross-block inversions of the permutation listing μ,
  then ν, each increasingly; neither increasing block has any internal inversions.
- The displayed shuffle sum, extended bilinearly: `shuffle` takes the finite sum
  `∑ w, pathSign w • ModuleCat.freeMk (pathSimplex u v w)` and extends it by
  `Finsupp.linearCombination ℤ`. Mathlib's `ModuleCat.FreeMonoidal.μIso` canonically identifies
  the tensor product of the two free modules with the free module on pairs of basis strings;
  its `μIso_hom_freeMk_tmul_freeMk` sends u⊗v to the corresponding basis pair.
  Therefore `shuffle` is an actual linear map on the specified tensor product, rather than
  a map only on individual strings.
- The boundary identity: the first conjunct is equality of linear maps from that tensor
  product, `d.comp shuffle = horizontalBoundary + (-1)^a • verticalBoundary`.
  `horizontalBoundary` is zero in degree a=0 and otherwise shuffles after d⊗id;
  `verticalBoundary` is zero in degree b=0 and otherwise shuffles after id⊗d.
  The `XIsoOfEq` maps identify a+b with the equal predecessor-degree expression; they change
  no generators or signs. These definitions encode exactly the node's omitted terms.
- Augmentation on each vertex: `augmentation` is the linear combination of the constant
  family 1, on any free integral module. Its specialization to degree-zero simplex and
  product-simplex groups gives exactly ε_p, ε_q, and ε_V.
- The augmentation identity: the second conjunct says
  `augmentation (shuffle p q 0 0 (u ⊗ₜ v)) = augmentation u * augmentation v` for arbitrary
  degree-zero chains. Under ℤ⊗ℤ≃ℤ this is ε_V σ_0 = ε_p⊗ε_q. Equality on pure tensors is
  equivalent to equality of these linear maps, since pure tensors generate.
- Every pair of monotone postcompositions: the third conjunct quantifies over arbitrary
  `f : Fin (p+1) →o Fin (p'+1)` and `g : Fin (q+1) →o Fin (q'+1)`. `simplexMap` and
  `productMap` are the existing standard-simplex maps, followed by the free functor and
  `AlternatingFaceMapComplex.map`. They are chain maps by construction. The asserted equality
  of linear maps is precisely postcompose-after-shuffle = shuffle-after-postcomposing-inputs.
  Neither map is required to be injective or surjective.

Dependency declarations read and used:

- The sole dependency, `def-weil-pbc-module-chain-complex-homology`, records
  `HomologicalComplex.homology` in `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`.
  Its complete docstring, section binders, and signature were read. This is a standard
  Mathlib chain-complex/homology convention, not missing data; the recorded module is imported
  publicly. `ChainComplex`, `HomologicalComplex.Hom`, and the complex shape supply its chain
  complexes and chain maps. No homology group is asserted in this node.
- `Mathlib.AlgebraicTopology.AlternatingFaceMapComplex`: `obj`, `objD`, `obj_d_eq`, `map`.
- `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex`: `objEquiv`, `asOrderHom`, `objMk`,
  `δ_objEquiv_symm_apply`, and `SSet.stdSimplex.map`.
- `Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex`: `objEquiv` and `objEquiv_δ_apply`.
- `Mathlib.Algebra.Category.ModuleCat.Adjunctions`: `free`, `freeMk`,
  `FreeMonoidal.μIso`, and `FreeMonoidal.μIso_hom_freeMk_tmul_freeMk`.
- `Mathlib.LinearAlgebra.Finsupp.LinearCombination`: `Finsupp.linearCombination`.

The helpers spell out the constructions already introduced in the assigned node. They introduce
no independent extra mathematical notion needing an additional DAG node and no postponed theorem
other than the node's own statement. There are no dependency repairs or statement corrections.

Edge cases checked before finalizing:

- a=b=0 has a unique path, sign 1, zero boundary, and the required vertex augmentation.
- a=0 or b=0 has only one coordinate direction; its missing boundary contribution is literally
  the zero linear map. a=1 or b=1 has only the appropriate endpoint faces in that direction.
- p=0 or q=0 and all constant or repeated strings are retained; the cancellation is on labeled
  paths before gathering identical generators.
- A separate integer-coefficient enumeration passed all 2,704 generator pairs with p,q≤2
  and a,b≤3, retaining repetitions, using alternating deletion and the same inversion sign.
  This is a sign/edge-case check, not a Lean proof.
- Constant monotone postcomposition can identify every generator; the naturality formula still
  compares the same individual signed path terms. No cancellation needs injectivity.

Searches (the required msearch wrapper, and local source searches):

- LeanFinder query: "Signed lattice path shuffle on unnormalized free simplex chains commutes
  with alternating deletion boundary". Eight hits: DoldKan.hσ'_eq', Rep.standardComplex.d_of,
  simplex generator-relation statements, and Dold-Kan higher-face statements. None is this
  product-simplex shuffle identity.
- Loogle query: `"shuffle", "ChainComplex"`. Zero hits.
- Mathlib grep query: `shuffle|Eilenberg.Zilber|Alexander.Whitney` in AlgebraicTopology.
  Zero hits.
- LeanSearch query: "Free abelian chain complex on weakly monotone strings signed shuffle map".
  Eight hits include FreeAddGroup.mk, Rep.standardComplex, complex-shape tensor signs,
  singularChainComplexFunctor, shifts, and Hom.fAddMonoidHom. None states the identity.
- LeanFinder query: "Finite monotone lattice paths rank equals position signed shuffle map
  of free simplex chains". Eight hits, mostly ranks of simplicial pairings and simplex
  generators; `SSet.prodStdSimplex.orderHomOfSimplex` is relevant to encoding a path, but does
  not construct the signed free-chain map or prove the boundary formula.
- `rg` on the full upstream and Sheaf source trees for `shuffle|Shuffle|lattice.path|LatticePath`,
  and `grep -rn` for the item id upstream. No upstream declaration states the assigned node.
  The Sheaf result `AlgebraicTopology.BicosimplicialShuffle.exists_shuffle` was opened in full:
  it concerns cochain totalizations of arbitrary bicosimplicial complexes and cites this node
  as a proof dependency; it is not this universal free-simplex chain identity. Its subset-indexed
  surjections and signs belong to that downstream cochain construction. The present helpers
  use the equivalent coordinate-path indexing specified by this node. Importing that downstream
  theorem here would reverse the intended proof dependency and close an import cycle when its
  proof-dependency import is installed, so this universal calculation uses Mathlib directly.
- DAG search for simplex/shuffle/weakly increasing strings/lattice paths found the assigned
  node and its downstream bicosimplicial-totalization/product-bar consumers, with no alternative
  existing free-chain construction. `tools/blueprint_refs.py search 'lattice shuffle'` returned
  zero blueprint matches; its ancestor query returned None, as the node already records.
- Read the example CompactObject module; its Sheaf version has been withdrawn, so also read
  the upstream recorded implementation and its namespace/module/docstring conventions.

Validation: `scompile.py` compiled the file independently in sandbox and library-module mode,
2.6 seconds each, with no Lean errors or warnings. The only environmental messages were an
SSH multiplex session refusal followed by successful nonmultiplexed compilation. No source or
build artifacts in the shared library were written directly.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
