## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceUnramifiedDiagonalOpen` states
`AlgebraicGeometry.AlgebraicSpace.diagonal_isRepresentableOpenImmersion_of_unramified`.
Its sole theorem has proof `sorry`; it introduces no definitions. The node is unchanged
except for its `lean` record. No new nodes or dependency repairs are needed.

Source read: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-diagonal-unramified-morphism`, Tag 05W1(1), including its diagram and proof.
The source assumes arbitrary algebraic spaces over an arbitrary scheme, exactly as
in this node. Open subspaces use the recorded Tag 02YU subfunctor definition.

Hypothesis and clause correspondence:

- The base scheme and size convention are `{S : Scheme.{u}}` and the explicitly
  declared `universe u`. This is the same universe as the recorded algebraic-space
  interface, with schemes in `Scheme.{u}` and sheaf values in `Type u`.
- The two arbitrary algebraic spaces are `{X Y : AlgebraicSpace S}`; their morphism
  is `(g : X ⟶ Y)`. No scheme representations of X or Y are required.
- Unramifiedness on every compatible representable étale scheme chart is exactly
  `(hg : MapIsLocally (@IsUnramified) g)`. The recorded `MapIsLocally` quantifies
  over all `U V : Over S`, representable étale maps into X and Y and commuting
  scheme maps. `IsUnramified` is exactly locally finite type plus open diagonal.
- The relative self-product is the actual sheaf limit
  `Limits.pullback g.hom g.hom`; the diagonal is `pullback.diagonal g.hom`.
  Its `.hom` is the underlying natural transformation, not an arbitrary map.
- Representable open immersion and the clause about all scheme base changes are
  the first conjunct `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
  (pullback.diagonal g.hom).hom`. By the recorded definition this quantifies over
  every scheme test and supplies a representing pullback square whose scheme
  projection is an open immersion. Any other representative is uniquely isomorphic
  to this one, so the predicate expresses the usual all-base-changes property.
- Identification with an open subspace is stated explicitly in the second conjunct:
  there exist `hP`, `J : OpenSubspace ⟨Limits.pullback g.hom g.hom, hP⟩`, and an
  isomorphism `e : X.obj.obj ≅ J.val.toFunctor`, satisfying
  `e.hom ≫ J.val.ι = (pullback.diagonal g.hom).hom`.
  The witness `hP` certifies that this very sheaf pullback is an algebraic space,
  as provided by the recorded fibre-product node; it imposes no extra hypothesis.
  The equation ensures that the inclusion corresponds to the actual diagonal.
  In particular J is necessarily its image subfunctor. Using the underlying
  presheaf isomorphism loses no sheaf information: its source is already a sheaf,
  hence J is one too.
- No separatedness, quasi-compactness, Noetherian condition, nonemptiness, or
  representability of X or Y appears among the hypotheses. All scheme structures
  are retained; the result is not restricted to geometric points.

Recorded statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-size-convention` is metatheoretic (its recorded convention has no Lean
  declaration); explicit universes render it here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, and `IsEtale`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace` (the canonical
  sheaf pullback's algebraic-space property) and the same sheaf limits it uses.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`:
  `AlgebraicGeometry.AlgebraicSpace.OpenSubspace`, including its subfunctor inclusion.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.

Proof dependencies imported privately where recorded:

- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`:
  `AlgebraicGeometry.AlgebraicSpace.representable_etale_scheme_tests`.
- `Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover`:
  `AlgebraicGeometry.Etale.of_comp_of_surjective_etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  `Etale.etale_comp`, `Etale.of_comp`, and the open-immersion étale instance.
- `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`:
  `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`.
- `lem-sfb-unramified-etale-compatible-charts` has no recorded Lean module at
  inspection time, so there is no proof-only module to import yet. Its full node
  was read and its role is included in step 2 of the theorem's proof docstring.
  It is not needed to elaborate this statement.

The public imports supply all statement dependencies; scheme and open-immersion
modules are already public dependencies of the imported recorded interfaces.
The docstring carries the node's six proof steps and their inputs.

Edge cases checked mathematically before drafting:

- Empty X gives the empty open subfunctor of the relative square; no witness of a
  point is required. Empty Y also forces X empty, and empty S is permitted.
- The identity has an isomorphic diagonal and gives the whole relative square as J.
- An open immersion is a monomorphism, so its relative diagonal is an isomorphism.
- A degree-two étale cover need not be a monomorphism: its diagonal gives a proper
  open subspace of its relative square, not all of it. No surjectivity of that
  diagonal has been imposed.
- Nonseparated étale maps are permitted; their open diagonal need not be closed.
- Nonreduced test schemes remain in the universal scheme test, so scheme-theoretic
  equality of sections, rather than just equality of underlying points, is used.

Searches actually run using `msearch.py NA lem-sfb-space-unramified-diagonal-open`:

- LeanFinder: "The diagonal of an unramified morphism of algebraic spaces is a
  representable open immersion". Eight hits, headed by
  `AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal`; all relevant
  diagonal hits are about schemes, not arbitrary algebraic spaces.
- Loogle: `"FormallyUnramified", "diagonal"`. Two hits: the scheme diagonal
  theorem and its converse instance. Their full types restrict X and Y to Scheme.
- grep: `unramified.*diagonal|isOpenImmersion_diagonal|AlgebraicSpace`, restricted
  to Mathlib `AlgebraicGeometry`. Two hits in `Morphisms/FormallyUnramified.lean`.
  Read the actual declaration at line 126: it is the scheme-only instance.
- LeanSearch: "The diagonal of an unramified morphism of algebraic spaces is an
  open immersion". Eight hits; scheme diagonal, immersion and separatedness facts,
  with no general algebraic-space result.
- `rg -n` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `unramified.*diagonal|diagonal.*unramified|Unramified.*[Dd]iagonal|MapIsLocally.*IsUnramified`:
  scheme diagonal statements and proof references to algebraic-space diagonal
  results, but no declaration of this theorem. The sibling scheme-target and
  converse nodes are not the general arbitrary-space statement of this item.
- `grep -rn` for the item id in `lean/WeilConjectures`: no matches.
- `rg` in `dag/lean_names_upstream.json` for unramified/diagonal combinations:
  no match. Searches for the chosen declaration name found no collision.

Validation: `scompile.py` compiled both its sandbox probe and its library module
successfully (15.3 s and 5.6 s), with no errors or warnings. Every universe and
variable is explicitly bound. No statement discrepancy or disputed claim found.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
