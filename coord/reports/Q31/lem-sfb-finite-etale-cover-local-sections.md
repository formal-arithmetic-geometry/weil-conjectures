## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleCoverLocalSections` states
`AlgebraicGeometry.AlgebraicSpace.finite_etale_cover_local_sections`, with its sole
proof `sorry`. It defines no new notions. The original node statement and every
field outside `lean` are preserved.

Source read: `literature/stacks-project/criteria.tex`, lines 1103–1159,
Tag 05XQ, `lemma-surjection-space-of-sections`. The source's hypotheses are a
finite scheme map and a surjective étale map from an algebraic space. Its conclusion
is exactly a surjective étale base change and a section. The node additionally
makes representability explicit; this is retained. The module docstring gives
the accepted DAG's eight-step argument, including its use of affine neighbourhoods
instead of assuming a globally separated source atlas.

Hypothesis and conclusion comparison:

- The base scheme and size convention are `{S : Scheme.{u}}` with explicit
  `universe u`. `Z U : Over S` are arbitrary schemes with structure maps to `S`.
  No finite-type, nonemptiness or separation condition on these schemes is imposed.
- The finite map of `S`-schemes is `p : Z ⟶ U` and `[IsFinite p.left]`.
  Morphisms in `Over S` retain their commutation with the structure maps.
- The algebraic space is `W : AlgebraicSpace S`, the existing full subcategory
  of fppf sheaves with representable diagonal and a surjective étale scheme atlas.
- The map to `Z` is `q : W ⟶ schemeSpace Z`. The recorded scheme-space
  construction retains the actual representable sheaf, rather than a replacement.
- Representability is `hq : IsRepresentable q.hom.hom`; étaleness is
  `he : IsEtale q.hom.hom`; surjectivity is `hs : IsSurjective q.hom.hom`.
  These are precisely the recorded scheme-test definitions. The `.hom.hom`
  projections forget only the full-subcategory and sheaf wrappers.
- The requested base change consists of `U' : Over S`, `v : U' ⟶ U`,
  `Etale v.left` and `Surjective v.left`.
- Write `Y = (Scheme.fppfTopology.over S).yoneda` when reading the signature
  (this is only prose, not new notation or a definition in the file).
  The domain of `σ` is `Limits.pullback (Y.map p) (Y.map v)`, the fppf-sheaf
  fibre product `h_Z ×_{h_U} h_{U'}`. Subcanonical Yoneda preserves the scheme
  pullback, so this is exactly the node's `Z ×_U U'`, viewed as a sheaf.
- The codomain of `σ` is `Limits.pullback (q.hom ≫ Y.map p) (Y.map v)`,
  exactly `W ×_U U'` as a sheaf. The recorded fibre-product theorem says
  this sheaf is an algebraic space. The full-subcategory encoding gives exactly
  the same morphisms; it does not add an unchosen isomorphism or a different object.
- The map `q_{U'}` is the actual `Limits.pullback.map` from this second pullback
  to the first, induced by `q.hom`, the identity on `h_{U'}`, and the identity on
  `h_U`. The final equation is `σ ≫ q_{U'} = 𝟙 _`, exactly the section equation.
  The two proof arguments to `pullback.map` are the category identity laws,
  not extra hypotheses. This equation also forces compatibility with the projection
  to `U'`, hence the requested relative morphism.
- No flatness assumption occurs on `p`; no separatedness or quasi-compactness
  occurs on `q`. No nonempty instances occur anywhere.

Statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`; read the structure signatures and
  locally-affine docstring in `Scheme.lean`.
- `def-weil-size-convention`: its record is a convention without a declaration;
  represented by the explicit scheme universe `u`, inherited by `Over S` and
  the existing space category. The category has objects in `Type (u+1)` and
  homs/representable section sets in `Type u`; no equality of independently
  specified universes is added.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.map`, signatures read at
  lines 95 and 270ff. The latter is the canonical induced morphism, with its
  specified maps on both projections.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `IsRepresentableWith`, `IsRepresentable`,
  `IsEtale`, `IsSurjective`, and `IsAlgebraicSpace`; read their full definitions.
- `def-trf-scheme-algebraic-space`:
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`,
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace` and
  `schemeSheaf_isAlgebraicSpace`, read at lines 72–85. The data are literally
  the subcanonical Yoneda sheaf, with a separate algebraic-space proof.
- `def-weil-finite-integral-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`;
  read the affine-preimage and finite-module class at lines 35–40.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`, read the affine-local class at lines 40–49.
  This current name is used rather than the deprecated `IsEtale` alias for schemes.
- `lem-trf-space-fibre-products-etale-covers`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; read each signature and proof docstring.
  The first identifies sheaf pullbacks as algebraic spaces, and the last
  gives the scheme representability of the pulled-back cover in this situation.

The public imports supply statement dependencies. The plain imports supply every
currently recorded proof module: finite ring maps, unramified/quasi-finite maps,
composition, local finite type, quasi-finiteness at points, the finite-unramified
singleton theorem, finite/proper morphisms, coproducts, pullback points,
faithfully flat spectra, flat monomorphisms and purely inseparable fields.
`lem-sfb-etale-splits-isolated-purely-inseparable` has no usable recorded module
in this checkout and is a proof prerequisite, not an object required to state this
item; there is no module to import for it. No import cycle is introduced.

Edge cases checked before writing:

- If `U` is empty then `Z` and `W` over it are empty. The empty base change and
  the unique empty-source map satisfy the asserted section equation.
- If `Z` is empty and `U` is arbitrary, take the identity of `U`. Both fibre
  products involving `Z` and `W` are empty, so the unique section suffices.
- For `p = id`, take the scheme represented by `W` as the base cover;
  its diagonal gives the section. This checks the direction of the final equation.
- A finite nonflat map, such as `Spec k → Spec k[t]` at the origin, is allowed:
  the sole map hypothesis is `IsFinite p.left`.
- A surjective étale doubled-origin map, and an infinite disjoint union of
  copies of `Z`, are allowed as covers: separation and quasi-compactness were
  not added. The latter example confirms that finiteness applies to `p`, not `q`.
- The identity cover on a nonempty scheme satisfies all hypotheses; there is
  no accidental implication that a chosen finite map is flat or étale.

Searches actually performed (2026-10-24):

1. `msearch.py ... leanfinder` with query
   `A surjective etale cover of a finite scheme over a base admits a section after surjective etale base change of the base`:
   eight hits, including `Scheme.Hom.cover_I₀`, `Scheme.JointlySurjective.exists_eq`,
   `Algebra.IsStandardEtale.of_surjective`, and étale composition. None states the
   simultaneous section result over a finite source.
2. `msearch.py ... loogle` with query
   `"AlgebraicGeometry.IsFinite", "AlgebraicGeometry.Etale"`: zero hits.
3. `msearch.py ... grep` in `AlgebraicGeometry` with query
   `spaceOfSections|surjection.space.of.sections|finite.*etale.*section|etale.*cover.*section`:
   zero Mathlib hits.
4. `msearch.py ... leansearch` with query
   `A surjective etale morphism to a finite scheme admits a section after surjective etale base change of the base`:
   eight hits, including étale categories, surjective and finite base change,
   and a formally étale ring quotient criterion. None is this statement.
5. `rg` over both `lean/WeilConjectures` and `lean/Sheaf` with the node id,
   `spaceOfSections`, and the finite/étale/section patterns found no matching
   statement. It found related Gabber finite étale closed-subscheme sections and
   trace-section descent. Read `FiniteEtaleClosedSubschemeSection.lean`: its base
   is affine integral normal with separably closed function field, unlike this
   arbitrary-base statement. `FiniteEtaleTraceSectionDescent.lean` concerns sums
   in abelian sheaves, not existence of sections of arbitrary étale scheme covers.
6. `rg` over Mathlib, upstream and project sources for
   `finite_etale_cover_local_sections|finiteEtaleCoverBaseChange|surjection_space_of_sections`:
   no declaration conflicts.

No node faults, statement correction, disputed statement, new nodes or dependency
repairs were needed. Every binder is explicit (`set_option autoImplicit false`).
Server `scompile.py` compiled the module in sandbox and library mode, with exit
status zero and no errors or warnings. The first elaboration attempt exposed the
namespace's existing module pullback shadowing the categorical name; qualifying
both fibre products and the induced map with `Limits` repaired that naming issue.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
