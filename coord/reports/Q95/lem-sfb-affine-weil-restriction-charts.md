## Worker report

The module `Sheaf.AlgebraicGeometry.AffineWeilRestrictionCharts` states
`AlgebraicGeometry.exists_affine_weil_restriction_charts`, with one `sorry` theorem
and no definitions. The node is unchanged except for its `lean` record. No new nodes,
dependency repairs or statement correction are needed.

Clause-by-clause correspondence:

- Schemes S, S', V, U are `{S S' V U : Scheme.{u}}`, with arbitrary universe u.
- The morphism p:S'→S is `(p : S' ⟶ S)`; its finite local freeness is the recorded
  `[p.IsFiniteLocallyFree]`, extending finite, flat and locally of finite presentation.
- An affine open subscheme of S is represented by `(i : V ⟶ S)` together with
  `[IsOpenImmersion i] [IsAffine V]`. An open immersion identifies V with its open image,
  so this permits exactly the open subschemes in the node, including the empty one.
- The map q:U→S' and affine source are `(q : U ⟶ S') [IsAffine U]`.
- Factorization of p∘q through V is `_hfactor : ∃ a : U ⟶ V, a ≫ i = q ≫ p`.
  This existential is a hypothesis, not a chosen replacement for the canonical pullback.
- Every V-scheme is `T : Over V`. Its map to S is `((Over.map i).obj T).hom = T.hom ≫ i`.
- Mathlib's `(Over.pullback p).obj ((Over.map i).obj T)` has underlying scheme
  `pullback (T.hom ≫ i) p` and structural map `pullback.snd (T.hom ≫ i) p` to S'.
  Thus its Hom to `Over.mk q` is exactly Hom over S' from T×[S]S' to U, with the
  equation to S' built into the over-category morphism. This does not discard the
  relative condition or substitute ordinary S-morphisms.
- The conclusion gives `∃ (R : Scheme.{u}) (r : R ⟶ V), IsAffine R ∧ ...`.
- `e : ∀ T : Over V, (T ⟶ Over.mk r) ≃ (...)` gives the required bijections.
- For every `a : T₁ ⟶ T₂` and `f : T₂ ⟶ Over.mk r`, the equation
  `e T₁ (a ≫ f) = (Over.pullback p).map ((Over.map i).map a) ≫ e T₂ f`
  is naturality under precomposition. `Over.pullback.map` is the actual induced
  morphism of pullbacks, with projections a and identity on S', not an arbitrary map.
- There is no finite-type or finite-presentation assumption on q, no degree parameter,
  and no positive-rank or constant-rank condition. All tests, not only affine tests,
  occur in the bijection and naturality equation.

Recorded statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, and `Spec.map`; affine schemes use the equivalent existing
  `AlgebraicGeometry.IsAffine` from `Mathlib.AlgebraicGeometry.AffineScheme`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (the finite/flat/lfp class).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, with scheme pullbacks provided by
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `CategoryTheory.Over.pullback` and
  `Over.map` (the latter is defined in `Comma.Over.Basic`), supplying the canonical
  test-object construction and its action on arrows.

The imports also include every recorded proof-dependency module, using plain imports
for proof-only inputs: finite/flat/lfp and qcqs permanence, affine-locality, rank loci,
principal basis charts, finite-free Hom, Yoneda, relative Zariski gluing, open inverse
images and morphism gluing. In particular the existing proof ingredients are
`AlgebraicGeometry.finiteLocallyFree_fiberDimension_isLocallyConstant`,
`AlgebraicGeometry.finiteLocallyFree_principalBasisCover`,
`AlgebraicGeometry.exists_affine_finite_free_hom`, and
`AlgebraicGeometry.Scheme.exists_scheme_of_zariski_cocycle`. Their sources and the
node's eight-step proof are described in the theorem docstring. The finite-free Hom
node uses a different ordinary relative Hom functor and is not this relative-to-S'
representability theorem.

Sources read: Stacks `more-morphisms.tex`, Tags 05Y6 and 0BL3 (labels confirmed in
`tags/tags`), and the current blueprint unit `sk-thm-sf-ctf-stability`, including its
proof. The relative-condition supplement is the node's explicit postcomposition
fibre argument; 0BL3 alone does not supply the S'-morphism condition.

Edge cases checked before writing:

- V empty forces U empty by the assumed factorization; the category of tests over V
  has only empty schemes, and R empty represents the singleton point sets.
- Rank-zero p has empty source and necessarily U empty. H(T) is a singleton for every
  test, and R=V represents it; neither source nonemptiness nor positive rank is bound.
- For p identity the result reduces to the affine U over V itself.
- For two disjoint copies over V, H is a product of relative Hom functors; affine fibre
  products give the expected representative. Different ranks on different clopen
  components are allowed by the unrestricted finite-locally-free class.
- Empty test schemes, arbitrary target algebras, nonaffine tests and nonaffine overlaps
  remain included. Scheme and test universes coincide with the ambient universe u;
  no independent smaller test universe can make the quantified assertion vacuous.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Weil restriction of arbitrary affine scheme along finite
  locally free morphism is represented by an affine scheme"`: 8 hits, finite/affine
  morphisms and affine space; no representing theorem.
- `msearch.py ... loogle '"WeilRestriction"'`: 0 hits.
- `msearch.py ... grep 'WeilRestriction|weil.?restriction|restriction of scalars'
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg` of the project's `lean/WeilConjectures` and `lean/Sheaf` for WeilRestriction,
  weilRestriction, affineWeil and the item id: no duplicate representing theorem;
  the similarly named constant-Weil scalar transport and Henselian-inertia result
  concern different notions. The broad phrase 'restriction of scalars' finds module
  and sheaf coefficient functors, not scheme restriction of scalars.
- `grep -rn 'lem-sfb-affine-weil-restriction-charts' lean/WeilConjectures`: no hits.
- `rg` of `dag/lean_names_upstream.json` and the Lean trees for the new declaration
  name: no existing declaration. No definition was introduced, so no new-notion
  node or blueprint-reference search is needed.

Validation: `scompile.py Q95 lem-sfb-affine-weil-restriction-charts` compiled this
file both as the sandbox probe and under its library module name, in 2.7 s and 1.6 s
respectively. No errors or warnings were emitted. Auto-implicit binding is disabled;
all object and universe variables are explicitly bound. The signature in the node
record is copied verbatim from the theorem keyword up to `:=`.

## Second reading by Q95

The dispatcher requires this worker to work alone and assigns the independent review
to the maintainer; no second agent was started. This section records a separate
self-audit of the finished Lean against the node, not a claimed independent review.

I reread the node and the final signature and checked each binder against the list
above. In particular `Over.pullback` has the required order T×[S]S', `Over.mk q`
enforces its S' structure map, and the naturality equation uses the map from the
first test pullback to the second before the represented morphism. The affine open
is a scheme with an open immersion, not an arbitrary affine map. The factorization
is assumed existentially exactly as in the prose. The affine conclusion concerns R
itself as the node requests. All tests and all morphisms over V are quantified;
zero/varying rank and unrestricted target presentation have no excluding binder.
No mismatch was found and no statement change was made. The proof docstring includes
all eight DAG steps, including the relative-condition fibre and all-test gluing.
