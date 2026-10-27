## Worker report

The module `Sheaf.AlgebraicGeometry.EqualizerPointChartDescent` states
`AlgebraicGeometry.equalizer_point_chart_descent`, with its entire proof `sorry`.
No definitions, auxiliary theorems, new nodes, dependency repairs, or statement
corrections are introduced. The source is the current main-20261015 blueprint's
`thm-trf-frobenius-fixed-points.proof.md`, Steps 0, 2 and 3; these were read along
with the node's seven expanded proof steps. The module docstring reproduces that
proof route, including descent over arbitrary open overlaps.

Hypothesis-by-hypothesis correspondence:

- The field is `(k : Type u) [Field k]`. A k-scheme is `(X : Scheme.{u})`
  with its structure morphism `s : X ⟶ Spec (.of k)`.
- The k-endomorphism is `h : X ⟶ X` with `hs : h ≫ s = s`.
- The graph is represented by `g : X ⟶ pullback s s` and the two equations
  `hg₁`, `hg₂`, giving its projections as identity and `h`. These equations
  uniquely specify the canonical graph by the existing pullback universal
  property: for every k-endomorphism such a graph exists. They impose no extra
  geometric condition. This avoids introducing a second graph definition.
- The finite affine cover has index `J : Type v` with `[Finite J]`, commutative
  k-algebras `B j`, and maps `c j : Spec (.of (B j)) ⟶ X`. The instances
  `[∀ j, IsOpenImmersion (c j)]` make them affine open charts, `hc` says that
  their images cover every point of X, and `hcs` makes each chart a k-morphism.
  There is no nonempty-chart, nonempty-index or separatedness assumption.
- The induced chart endomorphisms are `φ j : B j →ₐ[k] B j`; `hφ` identifies
  their spectra with the restriction of `h`, expressing preservation of each
  chart. Their difference ideals are `I j`, with `hI` specifying exactly
  `Ideal.span (Set.range (fun b ↦ φ j b - b))`. The node's inline ideal and
  quotient descriptions use Mathlib `Ideal.span` and `Ideal.Quotient`.
- The point labels are `P : Type u`, their family is `x`, `hxs` asserts that
  they are k-points, and `hx` asserts that h fixes every one.
- `Pj : J → Set P` and `hPj` specify exactly the labels whose morphisms factor
  through the j-th chart; `[∀ j, Finite (Pj j)]` is precisely local finiteness.
- `ε j : (B j ⧸ I j) ≃ₐ[k] ((Pj j) → k)` is the prescribed algebra
  isomorphism. `hε` says that each coordinate of ε composed with the quotient
  map, after taking Spec and the chart inclusion, is the labelled point.
  Thus ε is evaluation, rather than an arbitrary algebra isomorphism. The
  factorization is unique since the chart inclusion is an open immersion.

Conclusion-by-conclusion correspondence:

- `pullback g (pullback.diagonal s)` is exactly the node's graph-diagonal
  fibre product F; `pullback.fst g (pullback.diagonal s)` is its projection i.
- `Finite P` asserts global finiteness. The existential map q has source the
  actual categorical coproduct `∐ fun _ : P ↦ Spec (.of k)` and target F.
- The first equation on q identifies its composite with i on every summand
  with x_p; the quantified q' clause gives uniqueness with exactly this
  property; `IsIso q` asserts that this canonical map is an isomorphism.
- The family e identifies each quotient spectrum with the actual pullback of
  F over the chart. Its first equation fixes its projection to that chart as
  the quotient-spectrum map, making this the canonical chart identification.
- The next equation identifies the restriction of q to the P_j summands with
  `sigmaSpec` followed by `Spec.map (CommRingCat.ofHom (ε j).toRingHom)`,
  the canonical chart isomorphism e, and the projection to F. This is the
  spectrum of the prescribed evaluation isomorphism using Mathlib's canonical
  finite-product-spectrum map, in the direction coproduct → F.
- The last clause inside the existential e quantifies over arbitrary schemes
  T and two quotient-chart morphisms. Whenever their composites to X agree,
  their composites to F agree. This explicitly supplies compatibility on all
  open overlaps, including nonaffine overlaps, without any separatedness
  hypothesis or affine-overlap assumption.
- `IsFinite (i ≫ s)` and `Etale (i ≫ s)` assert precisely the two properties
  of the structure morphism of F, not of its inclusion in X.
- For every z in F, `IsIso` applies to the actual structural ring map:
  `(Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ s).appTop ≫ F.presheaf.Γgerm z`.
  This is k → Γ(Spec k) → Γ(F) → O_{F,z}, so the coefficient map itself,
  rather than just an unspecified field isomorphism, is an isomorphism.
  The remaining equation is `Module.length O_{F,z} O_{F,z} = 1`.

Dependency declarations and interfaces read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`
  and `.lift` in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  the existing scheme limits instance supplies their existence.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` (the integral property is not
  a conclusion of this node).
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-pbc-module-length`: Mathlib `Module.length` in
  `Mathlib.RingTheory.Length`, via its recorded mathlib_match.
- Proof interfaces: the scheme coproduct instances, coproduct open cover,
  and `sigmaSpec`/`ι_sigmaSpec` and its finite-index IsIso instance from
  `Mathlib.AlgebraicGeometry.Limits`; scheme open immersions from Mathlib;
  `Scheme.Cover.glueMorphisms` from `Mathlib.AlgebraicGeometry.Gluing`;
  `AlgebraicGeometry.etale_sigmaDesc_spec_of_finite_separable` from the recorded
  upstream module `WeilConjectures.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields`.
  These proof-only modules are imported without `public` where not already
  needed by the signature. No recorded dependency is replaced by a private copy.

Edge cases checked before finalizing:

- Empty X and empty P are allowed. With no charts the cover condition forces X
  empty, and no rational point of empty X exists, so P is empty as well.
- P empty with X nonempty is possible for a fixed-point-free endomorphism;
  each chart quotient is then the zero ring and the equalizer is empty.
  Quotient rings are not assumed nontrivial. The stalk conclusion is vacuous.
- Empty affine charts have zero coordinate rings and empty P_j, as expected.
- Repeated labels of the same point cannot satisfy evaluation surjectivity
  on a chart containing that point: their two coordinates would coincide.
  No additional injectivity assumption on x is needed.
- A single fixed point and identity on Spec k give the singleton case and
  local-ring length one. For identity on affine space with positive dimension,
  the finite-product evaluation hypothesis fails, so the statement does not
  incorrectly assert a finite equalizer.
- J has an independent universe because it indexes only a finite cover. P
  and the rings use the scheme universe, as in the existing scheme coproduct
  dependency; finite sets can always be represented there. No characteristic,
  algebraic-closure, reducedness, quasi-separatedness or separatedness
  condition is imposed on X or k.

Searches for an existing statement (the recovered sandbox search log was read):

- msearch grep, `equaliz.*(point|[Ee]tale)|point.*equaliz` in AlgebraicGeometry:
  zero hits.
- msearch Loogle, `"Scheme", "equalizer"`: two hits, the multicoequalizer
  gluing instance and compactness of a scheme equalizer under quasi-separatedness;
  neither is point-indexed equalizer descent.
- msearch LeanFinder, “A scheme endomorphism whose affine equalizers are
  products of the base field has equalizer canonically a finite disjoint union
  of rational points”: eight hits, on separatedness, limit factorization,
  diagonal open immersions and affine pullbacks; none is this statement.
- msearch LeanSearch, “A scheme equalizer covered by evaluation isomorphisms
  to finite products of a field is the canonical finite disjoint union of
  rational points”: eight hits including the scheme coproduct instances and
  `instIsIsoSchemeSigmaSpecOfFinite`. The latter is the finite-product-spectrum
  tool used here, not the complete descent statement.
- Direct rg in both project roots for `equalizer_point_chart_descent`,
  `lem-trf-equalizer-point-chart-descent`, `equaliz.*point`, `point.*equaliz`:
  no declaration or node-id match; incidental pointed-site equalization and
  unrelated quotient text do not state the result.

No node faults or disputed statements were found. The theorem compiled through
`scompile.py NR lem-trf-equalizer-point-chart-descent` with no errors or
unexpected warnings. The node's Lean signature was refreshed verbatim from the
compiled source after the interrupted turn's edits; all other node fields remain
unchanged. No delivery was in progress on resumption.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
