## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQcOpenFinitePresentation` states
`AlgebraicGeometry.AlgebraicSpace.finitePresentation_of_quasiCompact_openImmersion`.
Its only proof is `sorry`; it adds no definitions. The mathematical statement, proof,
and source fields of the item are unchanged. Two already landed definition nodes are
added to `stmt_deps` to account for the existing predicates explicitly used.

Hypotheses and clauses, checked against the node:

- The arbitrary base scheme is `{S : Scheme.{u}}`, with explicit `universe u` and
  `set_option autoImplicit false`. `U X : AlgebraicSpace S` are the actual full
  subcategory of fppf sheaves on schemes over `S`, not schemes or arbitrary sets.
  `j : U ⟶ X` is their natural transformation.
- The open immersion assumption is
  `hj : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`.
  Unfolding the recorded scheme-test predicate gives a representing scheme and
  pullback square for every scheme test, with an open-immersion projection.
  This is the same interface used by the recorded `OpenSubspace` definition;
  it does not require identifying the domain with a chosen subfunctor.
- Quasi-compactness is `hqc : IsQuasiCompactPresheafMap j.hom.hom`.
  For every affine scheme test this supplies a quasi-compact scheme with an
  étale surjective map to the actual presheaf fibre product. Thus it says exactly
  that the test source has the atlas required in the node, without assuming
  the domain or target itself is quasi-compact.
- The first conclusion `IsQuasiCompactPresheafMap j.hom.hom` is the
  quasi-compactness clause of finite presentation.
- The second conclusion
  `IsQuasiCompactPresheafMap (pullback.diagonal j.hom.hom)` is precisely
  quasi-separatedness: the relative diagonal to `U ×_X U` is quasi-compact.
  The relative diagonal is not replaced by the absolute diagonal over `S`.
- The third conclusion `MapIsLocallyOfFinitePresentation j` unfolds to
  `MapIsLocally (@LocallyOfFinitePresentation) j`: every compatible pair of
  representable étale scheme charts has a locally finitely presented scheme
  map. This is the node's specified chart convention.
- Together these are exactly finite presentation, as explicitly defined in the
  node and Stacks `spaces-morphisms.tex`, definition-locally-finite-presentation.
  There is no target quasi-compactness, quasi-separatedness, separation,
  Noetherian, or nonempty hypothesis. The node's descriptions of absolute
  quasi-separatedness, affine maps and local finite type fix ambient conventions;
  they are not additional hypotheses or conclusions of this lemma.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme` (the existing sheaf pullback interface).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`, read
  through its full subtype and scheme-test definition, using the same open
  immersion predicate in the theorem hypothesis.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`, `locallyOfFinitePresentation_of_isOpenImmersion`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`:
  `IsQuasiCompactPresheafMap`, owned by the already landed definition node
  `def-sfb-space-quasi-compact-presheaf-map`, now cited by the item.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocally`, `MapIsLocallyOfFinitePresentation`, owned by the already
  landed `def-sfb-space-morphism-properties`, now cited by the item.
- Proof-only Mathlib declarations: `Scheme.isBasis_affineOpens` and
  `Scheme.compactSpace_of_isAffine` in `Mathlib.AlgebraicGeometry.AffineScheme`;
  `IsOpenImmersion` in `Mathlib.AlgebraicGeometry.OpenImmersion`;
  `quasiSeparatedSpace_of_isAffine` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-size-convention` is explicitly a metatheoretic convention with
  no declaration: the existing universe-polymorphic algebraic-space interface
  and its full category of `Over S` test schemes are retained.

Edge cases checked before writing:

- Empty `U`, including empty `X`: local finite presentation is vacuous on empty
  charts, and an affine test of the diagonal has an identity quasi-compact atlas.
  The empty representing scheme is permitted; there is no nonempty binder.
- Identity and isomorphism open immersions over arbitrary spaces: scheme tests
  are identities, so quasi-compactness of the morphism does not impose
  quasi-compactness of the space. The conclusion remains valid for an infinite
  disjoint union and other non-quasi-compact targets.
- Non-quasi-separated or non-Noetherian targets: relative, rather than absolute,
  diagonal quasi-compactness is asserted, so the identity example remains covered.
- A general open immersion need not be quasi-compact; the affine-test atlas
  hypothesis is retained. It has not been replaced by quasi-compactness of an
  identity morphism or another automatically inhabited proposition.
- All schemes and coefficient-free sheaf tests stay in the dependency interface's
  universe `u`. No independent smaller test universe or equality of universes
  is imposed; arbitrary `u` is bound explicitly.

Source checked: local copy of Stacks `spaces-morphisms.tex`,
lemma-open-immersion-locally-finite-presentation (Tag 06CN), and
its definition-locally-finite-presentation. The node's four-step proof is carried
in the theorem docstring, with the affine-local identity presentation and the
monomorphism/diagonal argument spelled out. No statement fault or dispute found.

Searches (all prescribed remote searches used group Q55 and this item):

- `msearch.py leanfinder "Every quasi compact open immersion of algebraic spaces
  is of finite presentation"`: eight hits, headed by the scheme-only
  `locallyOfFinitePresentation_of_isOpenImmersion`; none states the space result.
- `msearch.py loogle '"IsOpenImmersion", "LocallyOfFinitePresentation"'`:
  one hit, that same scheme theorem, whose full signature has `X Y : Scheme`.
- `msearch.py grep "AlgebraicSpace|[Ii]sOpenImmersion.*[Ff]initePresentation"
  AlgebraicGeometry`: one scheme-only smoothness hit; no algebraic-space theorem.
- `msearch.py leansearch "A quasi compact open immersion of algebraic spaces is
  of finite presentation"`: eight scheme hits, again no algebraic-space result.
- `rg` over `lean/WeilConjectures` for `AlgebraicSpace` and the item id:
  no algebraic-space framework or item theorem. Related open-immersion
  finiteness searches return only scheme compactification lemmas and consumers.
- `rg` over `lean/Sheaf` for algebraic-space morphism, quasi-compactness,
  finite-presentation, and open-immersion declarations: found and read the
  reusable predicates listed above; no theorem already states this result.
- `rg` over `dag/nodes` located the already landed owning definition nodes.
  `dag/lean_names_upstream.json` contains no collision for the new theorem name.
  No notion is duplicated and no new node or dependency repair is needed.

## Second reading by Q55

A separate self-review pass compared the node, all reused predicate bodies and
this module. No other agent was started, as the dispatch brief prohibits it.
The readback checked each binder and each of the three conclusion clauses:
`Scheme.{u}`/`AlgebraicSpace S`, arbitrary morphism `j`, representable open
scheme tests, the atlas affine-test quasi-compactness assumption, relative
presheaf diagonal quasi-compactness and the all-compatible-chart local finite
presentation condition. It found no mathematical mismatch. In particular,
absolute quasi-separatedness is not accidentally assumed, and no arbitrary
map replaces the canonical relative diagonal. The existing owning definition
nodes were added to `stmt_deps`; no mathematical statement was changed.
The report does not claim an independent review; that review is performed by
the maintainer as specified in the dispatcher brief.

## Validation

All compilation is through `scompile.py`; the delivery is checked through
`deliver2.py --no-push` before pushing with `deliver2.py`.

Results: `scompile.py` compiled the sandbox and final library module with no
errors or warnings. `deliver2.py --no-push` returned
`OK (dry run): commit 0d22efd455a passes the preflight and compiles; nothing pushed`.
The final source has no lines over 100 characters, one theorem with one `sorry`,
and a node signature matching the source verbatim. Only `lean` and the two
landed-definition additions to `stmt_deps` differ from the item on the base.
