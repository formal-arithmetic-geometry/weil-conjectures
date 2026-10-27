## Worker report

States `AlgebraicGeometry.AlgebraicSpace.etale_unique_affine_thickening_lift` in
`Sheaf.AlgebraicGeometry.EtaleSpaceInfinitesimalLifting`, with its proof `sorry`.
No definitions or auxiliary theorems are introduced. The natural-language statement
and proof are unchanged. The only additional statement dependency is the landed
`def-sfb-space-morphism-properties`, to reuse its chart-test predicate.

Read the source in `literature/stacks-project/spaces-more-morphisms.tex`:
Tag 0616, lemma-etale-formally-etale; Tag 04GC, definition-formally-etale;
and definition-formally-smooth-etale-unramified. These specify unique lifts against
closed immersions of affine schemes with square-zero defining ideals. Also read
Tag 04GD, lemma-formally-etale, which gives locality on compatible étale charts.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Base scheme: `{S : Scheme.{u}}`.
- Algebraic spaces over that base: `{E Y : AlgebraicSpace S}`; the existing
  definition bundles fppf sheaves with representable diagonal and an étale
  surjective scheme atlas. Morphisms are natural transformations.
- The given morphism: `(p : E ⟶ Y)`.
- Étaleness in the node's chartwise sense: `(hp : MapIsLocally (@Etale) p)`.
  Unfolding this existing definition quantifies over every `U V : Over S`,
  maps `a : yoneda.obj U ⟶ E.obj.obj`, `c : yoneda.obj V ⟶ Y.obj.obj`, and
  `h : U ⟶ V`; if `IsEtale a`, `IsEtale c`, and
  `a ≫ p.hom.hom = yoneda.map h ≫ c`, then `Etale h.left`.
  Here `AlgebraicSpace.IsEtale` includes representability of the two chart maps;
  no representability assumption is imposed on `p`.
- Affine test schemes over S: `(T₀ T : Over S)` with
  `[IsAffine T₀.left] [IsAffine T.left]`.
- The thickening over S: `(i : T₀ ⟶ T)` is an over-category morphism and
  `(hi : IsFirstOrderThickening i.left)` uses precisely the existing predicate
  `IsClosedImmersion i.left ∧ i.left.ker ^ 2 = ⊥`.
- The two given maps are `(b : yoneda.obj T ⟶ Y.obj.obj)` and
  `(e₀ : yoneda.obj T₀ ⟶ E.obj.obj)`. These are maps of presheaves on `Over S`,
  hence morphisms over S from the corresponding representable test schemes.
- The square `p e₀ = b i` is
  `(w : e₀ ≫ p.hom.hom = yoneda.map i ≫ b)`.
- Existence and uniqueness are `∃! e : yoneda.obj T ⟶ E.obj.obj`.
- The restriction equation `e i = e₀` is `yoneda.map i ≫ e = e₀`.
- The equation over Y, `p e = b`, is `e ≫ p.hom.hom = b`.
  The conjunction inside `∃!` requires both, and uniqueness concerns all maps
  satisfying both equations, exactly as in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  obtained through the public algebraic-space and thickening imports.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicSpace.IsEtale`, reached through the chart-properties module.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.AlgebraicGeometry.Thickening`:
  `AlgebraicGeometry.IsFirstOrderThickening`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`.
- Proof-only import `WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale`:
  `AlgebraicGeometry.flat_unramified_formally_etale`, whose full signature and
  proof docstring were read. The other proof dependency,
  `lem-sfb-formally-etale-space-chart-locality`, has no Lean attachment in the
  current node and no corresponding source module was found, so there is no
  module to import for it. Its mathematical use remains explicit in the docstring.
  No missing notion is needed to type the present statement.

Edge cases checked before writing: identity thickenings (zero defining ideal),
empty affine test schemes, empty algebraic spaces, and nonrepresentable or
nonseparated étale maps are not excluded. The chart assumption is the node's
all-compatible-chart assumption, with no surjectivity requirement on individual
chart maps. A single explicitly bound universe u matches the recorded space API
and its convention of Scheme.{u} and Type u-valued sheaves; the tests have the same
scheme universe as S, rather than an independent possibly smaller universe.
No characteristic, finiteness, nonemptiness, or quasi-compactness restriction is
added. All variables are bound and `autoImplicit` is false.

Searches for an existing statement (2026-10-24):

- `msearch.py leanfinder`, query "An etale morphism of algebraic spaces has a
  unique lift across a square zero thickening of affine schemes": eight hits,
  including scheme `IsEtale.instFormallyUnramified` and ring
  `Algebra.Etale.formallyEtale`; no algebraic-space lifting theorem.
- `msearch.py loogle`, query `"FormallyEtale"`: twelve ring-theoretic hits,
  including `Algebra.FormallyEtale.iff_comp_bijective`; no space statement.
- `msearch.py leansearch`, query "An etale morphism of algebraic spaces admits
  unique lifts over affine square zero closed immersions": eight hits, including
  `StandardEtalePair.existsUnique_hasMap_of_hasMap_quotient_of_sq_eq_bot`,
  `RingHom.FormallyEtale`, and scheme lifting results; none states this theorem.
- `msearch.py grep`, regex `AlgebraicSpace|formallyEtale|formally_etale`,
  Mathlib subdirectory `AlgebraicGeometry`: zero hits.
- Local `rg` over `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for infinitesimal lifting, formal étaleness,
  and thickening lifts found the scheme flat-unramified theorem, several
  references to this node, and the converse `SpaceLfpFormallyEtaleCriterion`.
  The converse is not this theorem. It confirms the same presheaf encoding
  of the lifting property. The item-id search in WeilConjectures gave no hits.
- Local name search in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json` for `etale_unique_affine_thickening_lift`
  and `etale_space_infinitesimal_lifting`: no declaration collision.

No statement correction, disputed statement, new node, or dependency repair.
The file was compiled with the prescribed scompile.py wrapper, in module mode.
The theorem docstring records all three proof steps and their named dependencies.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
