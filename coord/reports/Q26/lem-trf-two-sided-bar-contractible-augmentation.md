## Worker report

The module `Sheaf.CategoryTheory.TwoSidedBarVerticalAugmentation` states
`CategoryTheory.TwoSidedBar.contractible_vertical_augmentation`. Its only theorem
has proof `sorry`. No other theorem is introduced, and no definition chooses
data from that theorem. The node is unchanged except for its `lean` record.

The bar complex is specified by `Presentation`: actual complexes and their
coproduct inclusions, the coproduct universal properties, and the exact formulas
for differentials and augmentations. This is a presentation of the construction
in the item's own statement, not a hypothesis of contractibility or of the desired
conclusion. The theorem asserts that a presentation exists and that the result
holds for every such presentation. In particular it cannot be made vacuous by
assuming an unavailable bar complex, and its augmentations cannot be replaced by
arbitrary maps. An inclusion-preserving isomorphism between presentations is fixed
by the coproduct universal properties and intertwines every displayed map.

The helper declarations belong to the construction stated by this node and are
listed in `lean.declarations`. No independent missing notion or dependency repair
was needed. The two tensor helpers are direct applications of existing Mathlib
`Functor.mapHomotopy` and `Functor.mapHomotopyEquiv`; their data contain the actual
tensor maps and the preserved homotopy identities, with no new proof obligations.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Fixed universes; small ordinary category D | Explicit `universe u w`, `D : Type u`, `[SmallCategory D]`. The coefficient ring and all modules live in the same chosen common bound; `w` is the localization morphism universe. |
| R commutative; covariant F | `R : Type u`, `[CommRing R]`, `F : D ⥤ ModuleCat.{u} R`. |
| Simplicial Q | `Q : SimplicialObject D`, the exact Mathlib dependency declaration. |
| A indexed by strings and a final arrow, coefficient F(T0) | `Presentation.a`, indexed by `c : ComposableArrows D p` and `f : c.right ⟶ Q.obj (op ⦋q⦌)`, with source `F.obj c.left`; `aCoproduct` is precisely the universal property of that direct sum. |
| Horizontal faces delete a vertex, compose arrows, and apply F only at the first face | `reindex c (SimplexCategory.δ j)` deletes vertex j; `coefficient` applies F to the map from vertex zero to the first retained vertex (an identity except at j=0); `lastMap` composes the final arrow with the edge from the last retained vertex to the original last vertex (an identity except at the last face). These are the terms of `Presentation.horizontal`. |
| Vertical operators postcompose f with Q operators | `verticalOperator` and `verticalOperatorFormula` for every simplex operator α, not just faces. `vertical` gives their alternating face sum. |
| Alternating differentials for positive p or q, zero at index zero | `horizontal`, `vertical`, and `barDifferential` use all `Fin (n+2)` faces of degree n+1, weighted by `(-1 : ℤ)^j.val`. In degree zero their targets are positive cochain terms and vanish by `aPositive` and `bPositive`. |
| Bidegrees (-p,-q); total sign dh+(-1)^p dv | The inclusions land in `(A.X (-↑p)).X (-↑q)` and totalization is Mathlib `A.total (.up ℤ)`. `ComplexShapeSigns` sets horizontal sign to 1 and vertical sign to `Int.negOnePow (-p)`, equal to `(-1)^p`. The underlying `HomologicalComplex₂` is a commuting double complex. |
| S^{-q}=F(Q_q), positive terms zero | `evaluationComplex F Q` is the alternating face map complex of `Q ⋙ F`, extended along `embeddingDownNat`, which sends q to -q. This contextual complex is defined, although the vertical conclusion concerns B. |
| B^{-p}=direct sum over strings of F(T0); its bar differential; positive terms zero | `Presentation.B`, `b`, `bCoproduct`, `barDifferential`, `bPositive`. |
| Complexes and derived category | Mathlib `CochainComplex`, `HomologicalComplex₂`, `QuasiIso`, `DerivedCategory.Q` and the bound `[HasDerivedCategory.{w} (ModuleCat.{u} R)]`. |
| Each Hom(T,Q) admits inverse to singleton map up to finite zigzags of cylinder homotopies | `evaluation Q T = Q ⋙ coyoneda.obj (op T)`. `hQ` quantifies over all T and supplies f and g with `Relation.EqvGen (fun a b ↦ Nonempty (SSet.Homotopy a b))` for both inverse equations. `EqvGen` is finite reflexive/symmetric/transitive closure; `SSet.Homotopy` is the cylinder `X ⊗ Δ[1] ⟶ Y`. The map to the constant singleton is unique, so quantifying f adds no choice of augmentation. |
| Fixed σ, Xσ=Hom(Tp,Q), Mσ=F(T0); arbitrary coefficients; summation is a chain homotopy equivalence | The third conjunct quantifies over p, c and every `M : ModuleCat R`, and supplies `CoefficientAugmentation (evaluation Q c.right) M` and a `HomotopyEquiv` whose `hom` is exactly its summation augmentation. Specialize M to `F.obj c.left` for Mσ. `sumFormula` is identity on every degree-zero summand, and all higher target terms are zero. There is no flatness, projectivity, or Kan assumption. |
| Free chains tensored with M identify with chains of copies of M | `CoefficientAugmentation.tensorIso` identifies the degreewise tensor of `X.chainComplex (ModuleCat.of R R)` with `X.chainComplex M`. `tensorFormula` fixes it by `[x] tensor m ↦ inclusion_x m`, in every degree. Thus its inverse is the finite-support sum described in proof step 1. |
| The displayed summation map is the free-chain augmentation tensored with M | `freeAugmentation` and `freeSumFormula` fix the free summation map. `tensorAugmentation` says for every free zero-chain z and m that augmenting the identified tensor gives `(freeAugmentation.f 0 z) • m`. Since the single complex has only its degree-zero term, this is exactly the augmented-chain-map equality after the canonical `R tensor M ≅ M`. The same conjunct also supplies the free augmentation homotopy equivalence. |
| Singleton differential, identity section, parity contraction | Fourth conjunct uses Mathlib `ChainComplex.alternatingConst.obj M`, whose differential is identity in positive even degrees and zero in odd degrees. It supplies t,j with `t.f 0 = 𝟙 M`, `j.f 0 = 𝟙 M`, `j ≫ t = 𝟙 _`, and `k : Homotopy (𝟙 _) (t ≫ j)` with `k.hom n (n+1) = if Odd n then 𝟙 M else 0`. Mathlib's orientation here reads `1-jt=dk+kd`, exactly the node's explicit contraction equation. |
| Tensoring singleton contractions and equivalences from any chosen finite zigzags preserves the identities | `tensorHomotopy` applies the actual additive tensor functor to any supplied homotopy. `tensorEquivalence` applies it to any supplied chain equivalence, preserving its forward/backward maps and both homotopy identities. These definitions reuse the existing Mathlib operations, so they cover every chosen zigzag equivalence, not a selected contraction only. |
| Direct sums over σ give each column augmentation equivalence | Second conjunct quantifies over every `P : Presentation F Q` and each p; `e.hom = P.column p` fixes the equivalence to the specified map. `columnFormula` sends every degree-zero generator `(c,f,x)` to `b p c x`; its other components have zero targets. The `aCoproduct`/`bCoproduct` and vertical formulas identify this with summing the coefficient augmentations over c. |
| eB forgets f at q=0 and is zero elsewhere | `Presentation.augmentationFormula` fixes its action on every q=0 total summand; `augmentationOffEdge` sets it to zero for every nonzero vertical degree. |
| That very eB is a quasi-isomorphism and invertible in D(R) | `QuasiIso P.augmentation ∧ IsIso (DerivedCategory.Q.map P.augmentation)`, for every presentation P. There is no replacement by an unrelated derived isomorphism. |
| Finite diagonals, since both indices are at most zero | `aPositive` gives the support bounds; the last conjunct explicitly states finiteness of `{(i,j) | i≤0 ∧ j≤0 ∧ i+j=n}` for each integer n. `Presentation.hasTotal` is supplied by the asserted existence, not assumed by the theorem. |

Dependency declarations read and used:

- `def-weil-size-convention`: its convention-only record is represented by the explicit universe parameters, rather than imported as a nonexistent object.
- `def-weil-pbc-simplicial-object`: `CategoryTheory.SimplicialObject`, `.δ`, `.σ`, in `Mathlib.AlgebraicTopology.SimplicialObject.Basic` (reexported by the simplicial-set imports).
- `def-weil-pbc-simplicial-set`: `SSet` in `Mathlib.AlgebraicTopology.SimplicialSet.Basic`. The other clauses of its Mathlib match, `degenerate`, `nonDegenerate`, `Subcomplex` and `SSet.Finite`, were read but are not used by this item.
- `def-sp-double-complex-total`: `HomologicalComplex₂`, `total`, `ιTotalOrZero`, `TotalComplexShape` and its cochain signs, via `WeilConjectures.CategoryTheory.DoubleComplexTotal`. Its first-quadrant filtration declarations are not needed for this nonpositive-quadrant statement.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Q`, in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- Proof-only `lem-weil-pbc-simplicial-homotopy-free-chain-homotopy`: `SSet.Homotopy.chainComplexMap`, in `Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance`, imported without `public`.
- Proof-only `lem-pc-bounded-above-double-complex-total-comparison`: `HomologicalComplex₂.total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE`, in `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`, imported without `public`.

Additional existing Mathlib operations are used directly: `ComposableArrows`,
`SimplexCategory.toCat`, `SSet.chainComplex`, `SSet.ιChainComplex`,
`ChainComplex.alternatingConst`, `tensoringRight`, `Functor.mapHomologicalComplex`,
`Functor.mapHomotopy`, `Functor.mapHomotopyEquiv`, and coproduct cocones/`IsColimit`.

Edge cases checked mathematically before writing: p=0 and q=0 have zero outgoing
chain differential, because the cochain target is positive; at p=0 the last-face
composition and first-face F map are both present in the degree-one formula.
In the singleton complex, degree zero gives 0=1-jt, degree one gives d2 k1=1,
and degree two gives k1 d2=1. The coefficient M may be zero or nonflat (for
example Z/2 over Z); tensoring actual homotopy identities is valid in both cases.
Characteristic two is allowed: the signed formulas reduce to the same alternating
identities. Empty string-indexed summations are coproducts of empty diagrams and
cause no failure. If D is empty there is no Q, so the original and formal statements
have no instance; no `Nonempty D` assumption is added. For n>0 there are no supported
total summands; for total degree -n there are n+1 possible pairs of nonnegative bar
degrees. No representable contraction requires fibrancy or a one-step homotopy.

Searches performed through the prescribed `msearch.py` wrapper:

- LeanFinder query: "The two sided categorical bar complex with contractible simplicial representable evaluations augments to the category bar complex by a chain homotopy equivalence on each column and a quasi isomorphism on total complexes". Eight results, including `SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv`, the group standard complex equivalence, `ChainComplex.alternatingConstHomotopyEquiv`, and `AlternatingFaceMapComplex.ε`. They provide constituent facts or require an extra degeneracy, and do not state this categorical two-sided-bar assertion.
- Loogle query: `"SimplicialObject", "replacement"`. Zero results.
- Mathlib grep query: `twoSidedBar|simplicialReplacement|barConstruction|barComplex`. Thirteen hits, all group bar/standard-resolution material in RepresentationTheory; no arbitrary-category two-sided complex.
- LeanSearch query: "The two sided categorical bar complex for a functor from a small category to modules has a vertical augmentation quasi isomorphism when all representable simplicial evaluations are contractible". Eight results: generic simplicial augmentation, quasi-isomorphisms and cochain augmentation APIs. No exact match.
- Local `rg` searches for `twoSidedBar|two.sided.bar|TwoSidedBar|simplicialReplacement|SimplicialReplacement` in both `lean/WeilConjectures`, `lean/Sheaf` and Mathlib found only the proof prose in `SimplicialDerivedColimitComputation`. Its full source was read: it specifies a different projective-resolution double complex and does not expose the two-sided complex or either map needed here. Its parent theorem depends on this argument, so it is not used to prove the present child. The `DerivedColimitBar` source was also read; its reversed, presheaf bar resolution is not a second definition of this covariant two-sided complex. The actual bar statement is absent.
- Local search for the item id in `lean/WeilConjectures` found no declaration. Searches for the proposed namespace and two-sided bar declarations in `lean/Sheaf` found no existing module giving this statement.

The sources opened were `sites-cohomology.tex`,
`lemma-compute-by-cosimplicial-resolution` (Tag 08Q9), especially its final free
representable argument; `simplicial.tex`, `remark-homotopy-better`,
`definition-homotopy-equivalent`, and `lemma-homotopy-s-N`; and `homology.tex`,
`lemma-first-quadrant-ss` (Tag 0132). The arbitrary-coefficient adaptation and all
six proof steps in the DAG are retained in the theorem's proof docstring.

No statement correction, disputed statement, or dependency fault was found.
The inherited stage-1 BLOCKED ending is superseded by this explicit stage-2
assignment and the standing stage-handoff instruction in `coord/brief-stage2.md` §0.

Validation uses `scompile.py` only, against the live published server library.
The delivery dry run and final delivery use `deliver2.py`; no direct Git command,
global build, or edit of the shared repository is performed.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
