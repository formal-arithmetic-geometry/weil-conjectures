## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite` states
`AlgebraicGeometry.AlgebraicSpace.chartwise_isLocallyQuasiFinite_of_etale`, with
`sorry` as its whole proof. No definition, extra node, dependency repair, or
statement correction is needed. The delivered node differs only in `lean`.

The statement follows the node clause by clause:

- The base scheme is `{S : Scheme.{u}}`. The arbitrary explicit universe `u`
  is the universe already used by the algebraic-space dependency.
- The algebraic space over that base is `(E : AlgebraicSpace S)`, the recorded
  full subcategory of fppf sheaves with representable diagonal and an étale
  surjective scheme atlas.
- The scheme over the base is `(T : Over S)`: its underlying scheme is `T.left`
  and its structure morphism is `T.hom`.
- The morphism to that scheme is `(f : E.obj.obj ⟶ yoneda.obj T)`. Morphisms of
  algebraic spaces are natural transformations. Since the target is a scheme,
  its presheaf is the representable `yoneda.obj T`; a separate proof that this
  representable is an algebraic space is unnecessary for this signature.
- Every scheme chart is quantified as `(V : Over S)` and
  `(v : yoneda.obj V ⟶ E.obj.obj)`. The premise `IsEtale v` is precisely the
  recorded notion of a representable étale map: its definition quantifies over
  scheme base changes and supplies representing pullback squares whose
  projection is étale. Representability is included, so no independent
  representability assumption is omitted.
- The composite is `v ≫ f`. Yoneda's existing equivalence `yonedaEquiv`
  identifies this natural transformation between representables with the
  unique scheme morphism over `S`; `.left` forgets only the structure over `S`.
  Thus the chartwise hypothesis is
  `hf : ∀ (V : Over S) (v : yoneda.obj V ⟶ E.obj.obj),
    IsEtale v → Etale (yonedaEquiv (v ≫ f)).left`.
- The conclusion quantifies over exactly the same `V`, `v`, and `IsEtale v`,
  and asserts `Scheme.Hom.IsLocallyQuasiFinite (yonedaEquiv (v ≫ f)).left`.
  This is the recorded Stacks predicate, including local finite type, and
  unfolds to quasi-finiteness at every point. The similarly named Mathlib
  predicate alone would omit that requirement and is deliberately not used.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (`def-pc-scheme`). This is also exposed by
  the public import of the algebraic-space module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicGeometry.AlgebraicSpace.IsEtale` (`def-trf-algebraic-space`).
  Their complete definitions and docstrings were read locally.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (`def-weil-etale-morphism`), read with its affine-local ring-map signature.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, and its defining
  `IsQuasiFiniteAtPoint` (`pqf-def-quasifinite`).
- Proof-only import `Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite`:
  `AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_of_unramified`
  (`lem-weil-pbc-unramified-quasi-finite-at-points`). Its signature asks for
  local finite type and an open-immersion diagonal and concludes the exact
  Stacks local quasi-finiteness predicate. Its docstring and proof were read.
- `CategoryTheory.yonedaEquiv` in `Mathlib.CategoryTheory.Yoneda` is the
  existing Yoneda equivalence; its definition evaluates a transformation at
  the identity of its representing object. No arbitrary representing map
  or choice of composite is introduced.

Source and proof plan: read Stacks `spaces-morphisms.tex`, Tag 03XU, and
`morphisms.tex`, Tag 03WS. The former reduces to étale scheme charts; the
latter deduces unramifiedness and then applies Tag 02V5. The declaration
has the node's three proof steps in its docstring: fix a chart, apply the
unramified-to-locally-quasi-finite theorem to its composite, universally
quantify the result. Surjectivity and quasi-compactness of charts are not
required. The source documents are present locally; no external fetch was
needed.

Edge cases checked before writing: the empty algebraic space and empty
scheme chart remain allowed; local quasi-finiteness on an empty chart is
pointwise vacuous. When E is represented by a scheme this is the ordinary
chartwise scheme theorem. Infinite disjoint unions remain allowed: there is
no quasi-compactness, finite-fibre bound, or finite-type-in-the-large clause.
No separation, Noetherianity, characteristic or field hypothesis is added.
Every scheme in `Over S` is quantified, not just affine or surjective charts.
All variables and the universe are explicitly bound.

Searches for an existing declaration (all on 2026-10-18):

- `msearch.py leanfinder`, query "An etale morphism of algebraic spaces is
  locally quasi-finite on all etale scheme charts": eight hits, all about
  scheme étaleness, immersions or finite morphisms; no algebraic-space
  chartwise theorem.
- `msearch.py loogle`, query `"LocallyQuasiFinite", "IsEtale"`: zero hits.
- `msearch.py leansearch`, query "An etale morphism of algebraic spaces is
  locally quasi finite on scheme charts": eight hits consisting of the
  scheme predicates, constructors and instances; no matching statement.
- `msearch.py grep`, regex
  `locally.?[Qq]uasi.?[Ff]inite|LocallyQuasiFinite`, scope
  `AlgebraicGeometry/Morphisms/Etale.lean`: zero hits.
- Direct `rg` of `AlgebraicSpace|isLocallyQuasiFinite_of_etale` and the item
  id in the upstream `WeilConjectures`, project `lean/Sheaf` and
  `dag/lean_names_upstream.json`: algebraic-space definitions and unrelated
  results only in the project; no upstream algebraic-space theorem and no
  exact item tag. Follow-up searches for `etale.*quasi|quasi.*etale` and
  `IsLocallyQuasiFinite` found the scheme-level unramified theorem already
  listed as a proof dependency, plus unrelated scheme and cohomology results.
- Direct `rg` for the proposed declaration name
  `chartwise_isLocallyQuasiFinite_of_etale` in Mathlib, upstream sources,
  project sources and the upstream name index found no collision.

Validation: `scompile.py NC lem-a1-etale-space-locally-quasi-finite` compiled
both the wrapper's sandbox and the library-module form successfully, with
no errors or warnings. No node fault or statement dispute was found.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
