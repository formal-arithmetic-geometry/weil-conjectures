## Worker report

The module `Sheaf.AlgebraicTopology.UniversalShuffleHomotopyInverse` states
`AlgebraicTopology.FreeBisimplex.universal_shuffle_homotopy_inverse`. Its only theorem
proof is `sorry`. The two concrete helper definitions are the counting-arrow pair
`shufflePathArrow` and the prescribed finite signed sum `shuffleGenerator`; these are
constructions already explicitly introduced in the item's statement. The repair adds a definition node owning the existing lattice-path and sign declarations;
no new Lean definition or dependency module is needed.

The source statement, proof, and proof dependencies are unchanged. The statement dependency
`def-sfb-simplex-lattice-path-sign` is added to own the already landed plain definitions
`LatticePath` and `pathSign` that occur in the signed sum. The theorem node
`lem-sfb-simplex-lattice-shuffle-boundary` is retained only as a proof dependency.

The statement's hypotheses and clauses correspond as follows.

| Node text | Lean rendering |
| --- | --- |
| Nonempty finite ordinals and monotone maps; `I = Δ × Δ` | `SimplexCategory × SimplexCategory`, with objects `⦋n⦌` and Mathlib simplex morphisms |
| `E = Fun(I, Ab)` | `SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{u}`; `u` is arbitrary |
| Free integral covariant representables and their basis arrows | The dependency's `representable.{u}` and `generator`, unchanged |
| `P_n = R_(n,n)` and `Q_n = ⨁_(a+b=n) R_(a,b)` | Binders `P Q`, `p : ∀ n, P.X n ≅ representable (⦋n⦌, ⦋n⦌)`, and `q : ∀ n, Q.X n ≅ totalTerm n` |
| Diagonal alternating-deletion boundary | `hP` specifies its value on every basis arrow using `∑ k : Fin (n+2), (-1)^k.val • generator ((δ k, δ k) ≫ α)` |
| Separately signed alternating-deletion boundary, omitting a zero degree direction | `hQ` uses the dependency's `totalBoundary a b j α`, including its zero-direction cases and vertical sign `(-1)^a` |
| The two vertex-sum augmentations to the constant integer diagram | `εP`, `εQ` target `(Functor.const _).obj (AddCommGrpCat.of (ULift.{u} ℤ))`; `hε` sends every degree-zero basis arrow of each complex to `ULift.up 1` |
| Partitions `μ ⊔ ν` and their counting maps `α_μ`, `α_ν` | The existing `SimplexLatticeShuffle.LatticePath a b` encodes each partition; `shufflePathArrow` has coordinate functions `(s.val k).1` and `(s.val k).2` |
| The sign of the permutation listing `μ` then `ν` | The existing `SimplexLatticeShuffle.pathSign`, counting vertical-before-horizontal inversions |
| Prescribed signed sum on the distinguished summand generator | `shuffleGenerator a b (⦋a⦌, ⦋b⦌) (𝟙 _)` |
| Extension by postcomposition and integral linearity at every object | `shuffleGenerator a b j α` postcomposes each counting arrow by `α`; the conclusion specifies this value for every summand basis arrow, and `e.hom` is a morphism of complexes of additive-group diagrams |
| This prescribed `σ` is a natural chain map | The conclusion's `e : HomotopyEquiv Q P` supplies `e.hom : Q ⟶ P`; its generator equality fixes precisely the prescribed shuffle, rather than an arbitrary comparison |
| `ε_P σ_0 = ε_Q` | `e.hom.f 0 ≫ εP = εQ` |
| A natural reverse chain map `τ` with `ε_Q τ_0 = ε_P` | `e.inv : P ⟶ Q` and `e.inv.f 0 ≫ εQ = εP` |
| Natural degree-raising `h_P` and `σ τ - 1_P = ∂h_P + h_P∂` | `e.homotopyInvHomId : Homotopy (e.inv ≫ e.hom) (𝟙 P)`; its `hom n (n+1)` is a natural transformation, and `Homotopy.comm` is this equation, with the nonexistent lower degree zero |
| Natural degree-raising `h_Q` and `τ σ - 1_Q = ∂h_Q + h_Q∂` | `e.homotopyHomInvId : Homotopy (e.hom ≫ e.inv) (𝟙 Q)` in the same diagram category |
| Chain degree `n` lies in cochain degree `-n` | Mathlib's `ComplexShape.embeddingDownNat`, whose map is `n ↦ -n`, and `HomologicalComplex.extend`, which is zero outside its image |
| The class of the prescribed shuffle is a derived isomorphism `Q ≅ P` | The existential `eD` is an isomorphism between `DerivedCategory.Q.obj` of those extended complexes, and `eD.hom = DerivedCategory.Q.map (HomologicalComplex.extendMap e.hom ComplexShape.embeddingDownNat)` fixes its forward arrow |
| Chosen derived-category morphism universe | `[HasDerivedCategory.{w} ...]` uses the recorded dependency's size convention, with arbitrary explicitly declared `w` |

The presentations `p,q` and equations `hP,hQ,hε` express exactly what the two complexes
are, rather than adding projectivity or exactness as hypotheses. Their boundaries and
augmentations determine them up to the displayed identifications. In particular, the
statement applies to any presentation of the canonical complexes. Projectivity and
augmented exactness are supplied by the existing resolution theorem when proving this
statement. The generator equation uniquely fixes each component of `e.hom`: basis
arrows generate the free summands, and the coproduct inclusions generate `Q_n`. The
existential formulation therefore specifies the same prescribed map as the node.

The following dependency declarations were read with their signatures and docstrings.

- `Sheaf.AlgebraicTopology.FreeBisimplexProjectiveResolutions`:
  `AlgebraicTopology.FreeBisimplex.representable`, `generator`, `totalTerm`,
  `totalGenerator`, `predecessorCoface`, `totalBoundary`, `liftComplex`,
  `evaluateComplex`, `diagram_projectivity`, and `projective_resolutions`.
  This is the recorded free-bisimplex dependency, used directly.
- `Sheaf.AlgebraicTopology.SimplexLatticeShuffleBoundary`:
  `AlgebraicTopology.SimplexLatticeShuffle.LatticePath`, `pathSign`, and
  `shuffle_boundary_augmentation_naturality`. The first two are reused in the formula;
  the last is the node's boundary and augmentation proof input. Its `shuffle` retains
  repeated vertices and is the corresponding evaluated map.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q`, the recorded abstract-derived-category
  dependency.
- `Mathlib.CategoryTheory.Abelian.Projective.Resolution`:
  `CategoryTheory.ProjectiveResolution.lift` and `lift_commutes_zero`, the recorded
  Mathlib match for `lem-sfb-abelian-projective-resolution-lift`. This is a plain proof
  import; no duplicate lifting theorem is written.
- `Sheaf.Algebra.Homology.AugmentedResolutionLiftHomotopy`:
  `ModuleCat.augmented_lift_homotopy`, a plain proof import for
  `new-t4-augmented-resolution-lift-homotopy`.
- `Mathlib.Algebra.Homology.Embedding.Extend`: `HomologicalComplex.extend` and
  `extendMap`, along `ComplexShape.embeddingDownNat`. These implement the node's
  explicit chain-to-cochain degree convention, using the existing Mathlib construction.

Edge cases checked before drafting: for `a=b=0` the sole path gives the identity basis
arrow with sign one, so both augmentations agree. For either factor degree zero there
is one path with sign one, and `totalBoundary` omits that factor's boundary. For
`a=b=1` the two paths have signs plus and minus, agreeing with the order `μ` then `ν`.
No normalization discards repeated vertices: every monotone arrow remains a free basis
element, including constant and other noninjective arrows. The category includes `[0]`,
but not the empty ordinal, exactly as specified. The homotopies live in the functor
category; the dependency's pointwise minimum-vertex cones are not asserted natural.
Universe `u=0` and arbitrary larger coefficient universes are included via the dependency's
existing lifts. The localization universe `w` is independent of `u`. There is no field,
characteristic, finiteness-of-target, or normalized-complex restriction.

Searches for an exact existing statement:

- `msearch.py`, LeanFinder: “The prescribed universal signed shuffle between free
  bisimplex diagram resolutions is an augmentation preserving chain homotopy equivalence”.
  Eight hits: extra-degeneracy, constant-chain, and Dold–Kan homotopy equivalences; none
  is the prescribed universal bisimplex shuffle.
- `msearch.py`, LeanSearch: “The signed shuffle between universal free bisimplex chain
  resolutions is a natural chain homotopy equivalence”. Eight hits concern generic
  homotopies, resolution lifts, Dold–Kan, and constant complexes; no exact match.
- `msearch.py`, Loogle: `"shuffle", "HomotopyEquiv"`. Zero hits.
- `msearch.py`, Mathlib grep: `shuffle|Eilenberg.Zilber|Alexander.Whitney` in
  `AlgebraicTopology`. Zero hits.
- `rg` in `lean/WeilConjectures`: `shuffle|Shuffle|Eilenberg.Zilber|Alexander.Whitney`.
  Only unrelated Koszul signs, an evaluation rearrangement, and Godement products.
  The exact node id has no occurrence there.
- `rg` in `lean/Sheaf`: universal-shuffle and free-bisimplex searches find the recorded
  lattice-shuffle/reindexing and free-resolution dependencies; none states this theorem.
- `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` finds no declaration named
  `universal_shuffle_homotopy_inverse`, `shufflePathArrow`, or `shuffleGenerator`.

The local Stacks source was read at `lemma-morphisms-lift-projective` (Tag 0649)
and `lemma-morphisms-equal-up-to-homotopy-projective` (Tag 064A). The current blueprint's
six-functor direct-image proof paragraph (3) supplies the inherited application;
the more detailed universal shuffle statement is the existing agent-formulated node.
No statement fault or mathematical dispute was found. No statement correction is made.

Validation: `scompile.py Q43 lem-sfb-universal-shuffle-homotopy-inverse` compiled this
single module against current server sources in 2.5 seconds with no Lean errors or
warnings. The first pass required making the finite underlying subtype explicit for
`Fintype.ofFinite`; the final definition uses real finite data throughout.


## Repair of returned delivery 1c07e4c420fb

H2: replaced the added statement dependency `lem-sfb-simplex-lattice-shuffle-boundary`
with the new definition node `def-sfb-simplex-lattice-path-sign`. Its `existing: true`
record owns exactly the already landed `AlgebraicTopology.SimplexLatticeShuffle.LatticePath`
and `pathSign`. Their bodies are unchanged, real constructions; the boundary theorem's
conclusion is not used by either definition. The item's mathematical statement, theorem
signature, helper definitions, proof and proof dependencies remain unchanged. Compared
with current main, only `lean` and the authorized added definition `stmt_deps` change.
Compared with the returned packet, the node dependency and its ownership record are repaired.

Advisory H9: the two proof-only imports are already ordinary `import`, without `public`:
`Mathlib.CategoryTheory.Abelian.Projective.Resolution` and
`Sheaf.Algebra.Homology.AugmentedResolutionLiftHomotopy`. They are the recorded proof
inputs and are retained as required by stages/2-statements.md §3.7. The lattice-shuffle
module remains a public import because it supplies the definitions now owned by the new
node, as well as the proof theorem. No additional import is introduced.

## New nodes

`def-sfb-simplex-lattice-path-sign` records `existing: true` on the two plain definitions
in `Sheaf.AlgebraicTopology.SimplexLatticeShuffleBoundary` at lines 45–57; it creates no
module and no duplicate declarations. Its source is the agent-formulated universal-shuffle
input to paragraph (3) of the current blueprint's direct-image proof. For each pair
`a b : ℕ`, `LatticePath a b` is exactly the subtype of functions on `Fin (a+b+1)` into
`Fin (a+1) × Fin (b+1)` with `Monotone` and coordinate sum equal to the index. These
conditions force endpoints `(0,0)`, `(a,b)` and a single horizontal or vertical increment
at each step, giving the node's partition. `pathSign` counts pairs of positions `r<s`
whose first step is vertical and second horizontal, and raises the integer `-1` to
that count. Those pairs are precisely the inversions of the μ-then-ν permutation.
At `a=b=0` the index of steps is empty and the sign is one. On either axis the only
path has sign one; at `(1,1)` the paths HV and VH have signs one and minus one.
There are no additional hypotheses or theorem assertions to postpone in this record.

The three new logged msearch queries are:
- LeanSearch: “Monotone lattice paths in a rectangle with coordinate sum equal to the
  vertex index and sign counting vertical before horizontal inversions”: eight hits,
  including Young diagrams, Dyck words, and generic permutation signs; no exact definition.
- LeanFinder: “Lattice paths encoding shuffle partitions and sign equal to minus one
  raised to vertical before horizontal inversions”: eight generic total-complex and
  permutation-sign hits; no exact path subtype.
- Mathlib grep: `LatticePath|pathSign|shuffle.*partition` in `AlgebraicTopology`: zero hits.

Direct `rg` of `lean/WeilConjectures` finds neither name; `lean/Sheaf/AlgebraicTopology`
locates the two existing definitions and their consumers. `rg` of `dag/nodes` finds no
separate owner for this subtype. The existing `def-sfb-shuffle-word-combinatorics` owns
lists of booleans with prefix counts and a different sign implementation, not these
declarations. `blueprint_refs.py search 'lattice path'` reports zero blueprint nodes;
`ancestor lem-sfb-universal-shuffle-homotopy-inverse` reports None, retained in the new
node's ancestry. The new node's mathlib_searches contain the actual logged results.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
