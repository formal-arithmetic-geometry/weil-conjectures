## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint` states
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_fibreProduct_point`, with `sorry`
as its whole proof. It introduces no definitions, new nodes or dependency repairs,
and changes only the item's `lean` field.

Source checked: `literature/stacks-project/spaces-properties.tex`, section Points
of algebraic spaces, the field-valued equivalence relation preceding
`definition-points` (Tag 03BU), `lemma-scheme-points`, and
`lemma-points-cartesian` (Tag 03H4), including its proof. The final assertion uses
the scheme surjectivity definition of Tag 01RZ. The statement is the source's
scheme-input case, including representability by the representable diagonal.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `E : AlgebraicSpace S` is precisely the
  existing category of algebraic spaces over that base.
- Schemes `C` and `U` over `S` are `(C U : Over S)`. Their underlying schemes are
  `C.left` and `U.left`; their structure morphisms are retained in the objects.
- The given morphisms into `E` are `c : yoneda.obj C ⟶ E.obj.obj` and
  `f : yoneda.obj U ⟶ E.obj.obj`. As in the recorded algebraic-space definition,
  these are natural transformations of presheaves on schemes over `S`.
- The sheaf fibre product being represented by a scheme, with its projections,
  is `∃ (P : Over S) (p : P ⟶ C) (q : P ⟶ U), IsPullback (yoneda.map p)
  (yoneda.map q) c f ∧ ...`. The pullback square of presheaves says that the
  Yoneda presheaf of `P` is the fibre product. Since the objects in the square
  are sheaves, this is also the sheaf fibre product. This square specifies the
  object in the node rather than adding a separate conclusion about another
  pullback. No scheme structure on `E` is assumed.
- The two underlying points are `(x : C.left)` and `(y : U.left)`.
- Their equality of image point classes is the displayed existential over
  `K : Type u`, its `Field K` structure, `s : Spec (CommRingCat.of K) ⟶ S`, maps
  `a : Over.mk s ⟶ C`, `b : Over.mk s ⟶ U`, and a point `t` of `Spec K`, with
  `a.left t = x`, `b.left t = y`, and
  `c.app (op (Over.mk s)) a = f.app (op (Over.mk s)) b`.
  This is exactly the common-field formulation from Tag 03BU: representatives
  over fields `K₀` and `L₀` with equal image classes restrict to compatible maps
  over their common extension `K`, giving these `a,b,t`. Conversely such
  `a,b` represent `x,y` and have identical composites to `E`, hence their image
  classes coincide. The scheme-points lemma identifies the scheme point with
  its field-valued class. Thus the existential neither chooses an unrelated
  map nor imposes a stronger hypothesis. The common `s` retains the required
  compatibility over `S`. A field spectrum has exactly one point, so the
  explicit `t` excludes no field or point-class case.
- Pointwise nonemptiness with the specified projections is exactly
  `∃ z : P.left, p.left z = x ∧ q.left z = y`.
- The condition that every point in the image of `c` lies in the image of `f`
  is `∀ x : C.left, ∃ (y : U.left) ...` with precisely the same common-field
  point-class condition. Its conclusion is `Surjective p.left`, the recorded
  scheme-morphism surjectivity class. The implication is a separate conjunct,
  so the pointwise lifting assertion does not depend on global image inclusion.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; their full
  signatures and docstrings were read in the pinned Mathlib.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, declarations
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsAlgebraicSpace`, and
  `AlgebraicSpace.IsRepresentable`. The complete module and its docstrings were
  read. In particular `E.obj.obj` is its underlying set-valued presheaf, and the
  diagonal is representable by the existing definition.
- `def-weil-field`: Mathlib `Field`, the full class signature and docstring in
  `Mathlib.Algebra.Field.Defs` were read. It is used directly in the existential
  binders. The test field has the same universe as the big site, as in the
  recorded dependency interfaces.
- `def-trf-algebraic-space-jointly-surjective-family`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`, declaration
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`. The full module was
  read. Its field-extension/common-representative encoding is used in expanded
  form for the binary equality-of-images condition, rather than introducing a
  second definition or a quotient type. This module is publicly imported.
- `def-weil-surjective-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  declaration `AlgebraicGeometry.Surjective` with field
  `surj : Function.Surjective f`; the signature and docstring were read.
- Proof dependency `def-pc-fibre-product`: the recorded
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` module is imported
  without `public`. Its `pullback`, `pullback.fst`, `pullback.snd`, and universal
  property signatures/docstrings were read. The other recorded proof
  dependencies are already public imports or Mathlib definitions supplied by
  those imports. The theorem docstring contains the node's two proof steps
  and names all their dependencies.

Edge cases checked before writing:

- Empty `C`: the pointwise assertion and image-inclusion condition are vacuous;
  the represented fibre product is empty and its projection to empty `C` is
  surjective. No nonemptiness instance is imposed.
- Empty `U`, nonempty `C`: no compatible pair exists and image inclusion fails;
  the theorem does not incorrectly claim surjectivity in that case.
- Both empty, or empty base: the same formulation remains valid.
- `E` a scheme: the point-lifting clause specializes to the usual scheme
  pullback point theorem, without requiring a unique point over a pair.
- Fields need not be algebraically closed or have a prescribed characteristic.
  The common field is existential, and the original fields need not coincide.
- No affineness, finite type, separation, étaleness or surjectivity hypothesis is
  imposed on either given map. Schemes and fields use the universe of the
  existing big-site algebraic-space interface; no independent smaller test
  universe or equality between distinct site universes is imposed.

Searches for an existing declaration (all run through the prescribed tools or
read-only source searches):

- `msearch.py leanfinder`, query `Points of a fibre product of schemes over an
  algebraic space with equal field-valued point classes lift after a common
  field extension`: eight hits, including
  `Scheme.Pullback.exists_preimage_pullback`,
  `Scheme.exists_preimage_of_isPullback`, and
  `Scheme.Pullback.Triplet.exists_preimage`. These are for scheme bases, not
  algebraic-space bases; no exact match.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback,
  AlgebraicGeometry.Scheme.exists_preimage_of_isPullback`: zero hits.
- `msearch.py grep`, query
  `AlgebraicSpace|algebraic.space|fibre.product.*point|fiber.product.*point`,
  subdirectory `AlgebraicGeometry`: zero hits in Mathlib.
- Read-only `rg` on the upstream `WeilConjectures` source for
  `AlgebraicSpace|algebraic.space` and the item id: no hits. The project upstream
  name index likewise has no algebraic-space point declaration.
- Read-only `rg` of the project's algebraic-space modules found
  `AlgebraicSpaceFibreProductsEtaleCovers`; its full signatures and docstrings
  were read. Its point-related theorem is stability of jointly surjective
  étale covers, and its scheme representability clause assumes an étale leg.
  Neither states this arbitrary-map compatible-pair assertion.
- Read-only `rg` of Mathlib, upstream and project Lean for
  `exists_scheme_fibreProduct_point|fibreProduct_point|fibre_product_point`:
  no existing declaration.

Validation: the prescribed `scompile.py` compiled the delivered module cleanly
against the published library, with no errors or warnings. No node fault or
statement dispute was found. Delivery dry-run results are recorded below.

Delivery dry run: `deliver2.py N4 lem-a1-space-fibre-product-point --no-push`
reported `OK (dry run)`; the packet passed preflight and compilation.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
