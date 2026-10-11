## Worker report

The module `Sheaf.Topology.ClosedImmersionPushforwardExact` states
`TopCat.Sheaf.shortExact_map_pushforward_closedSubset`, with proof `by sorry`.
There are no new definitions or additional theorem statements. The original node's
statement and dependencies are unchanged.

Source checked: [Stacks Project, Lemma 17.6.1, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX),
exactness assertion. The local literature checkout lacks `modules.tex`, so the tag was
read on the Stacks website. Its closed-subset exactness assertion agrees with the node;
its additional fully faithful and essential-image assertions are outside this node.

Hypothesis and clause correspondence:

- An arbitrary topological space is `(X : TopCat.{u})`; there is no separation,
  finiteness, scheme, or nonemptiness assumption.
- A closed subset is `(Z : Set X) (hZ : IsClosed Z)`.
  `TopCat.of Z` uses the canonical subtype topology, including empty subsets.
- The inclusion `i : Z → X` is the explicit continuous morphism
  `(TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X)`.
  It is not an arbitrary continuous map with an unspecified image.
- Abelian sheaves on `Z` are `(TopCat.of Z).Sheaf AddCommGrpCat.{u}`;
  abelian sheaves on `X` are `X.Sheaf AddCommGrpCat.{u}`. These are definitionally
  `CategoryTheory.Sheaf (Opens.grothendieckTopology ...) AddCommGrpCat.{u}`,
  the open-cover site specialization of the recorded dependency.
- The functor defined by `(i_*F)(U) = F(U ∩ Z)` is exactly Mathlib's
  `TopCat.Sheaf.pushforward AddCommGrpCat.{u} i`, not a new definition.
  `pushforward_obj_val` identifies its underlying presheaf with
  `TopCat.Presheaf.pushforward`, whose definition is precomposition with
  `(Opens.map i).op`. Its value at `U` is therefore `F(i⁻¹(U))`.
  Here `i⁻¹(U)` is the relative open of `Z` consisting of points in `U ∩ Z`.
  `pushforward_map` and `Presheaf.pushforward_map_app'` give the same rule on maps.
  The theorem docstring records this interpretation; no redundant formula is added
  to the conclusion.
- Preserving every short exact sequence is expressed by arbitrary
  `(S : ShortComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u})) (hS : S.ShortExact)`
  and conclusion `(S.map (pushforward AddCommGrpCat.{u} i)).ShortExact`.
  A `ShortComplex` contains the three sheaves, both maps and their zero composite.
  `ShortExact` means middle exactness, a monic first map and an epic second map,
  exactly the two zero endpoints and middle exactness of the node's sequence.

Dependency declarations read and used:
`def-sc-topological-abelian-cohomology` records
`CategoryTheory.Sheaf.H'` in `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
Its full signature and docstring were read. Its category is
`CategoryTheory.Sheaf J AddCommGrpCat`, specializing `J` to the open-cover topology.
That module is imported, and the same existing sheaf category is used via its
`TopCat.Sheaf` presentation. No cohomology value is required in the present theorem,
so `H'` is not artificially invoked. The sheaf-abbreviation dependency is usable;
no replacement dependency module is needed. The only other constructions used are
Mathlib's `TopCat.Sheaf.pushforward`, `TopCat.ofHom`, `ShortComplex.map` and
`ShortComplex.ShortExact`; their definitions/signatures were read in source.

The declaration docstring gives all three node proof steps: identify the stalk
sequence on `Z` including its maps; use zero stalks off `Z` and stalkwise exactness
on `Z`; apply stalkwise detection on `X`. The cited proof nodes are
`lem-sc-closed-pushforward-abelian-stalks` and
`lem-sc-abelian-sheaf-short-exact-stalkwise`. They are proof dependencies, not imports
needed to state this theorem; their unlanded statements are not duplicated.

Edge cases checked mathematically: `Z = ∅` gives the zero direct image and hence a
short exact zero sequence; `Z = Set.univ` gives the identity under the canonical
subspace identification; a singleton closed subset gives the skyscraper case.
`X = ∅`, zero sheaves and zero short exact sequences are admitted. No characteristic
or ring is involved. The space and group carriers are in an arbitrary common
universe `u`, as in the existing abelian-sheaf infrastructure; raising this common
universe accommodates any given space and group sizes. No smallness or nonempty
hypothesis is added.

Searches made with `msearch.py` (recorded in `searches.jsonl`):

- LeanSearch: `The pushforward functor on abelian sheaves along a closed subspace inclusion preserves short exact sequences`.
  Service unavailable (Internal Server Error); no verdict inferred from that failure.
- LeanFinder: `The direct image functor of abelian sheaves along inclusion of a closed subset of a topological space preserves short exact sequences`.
  Eight hits, including Mayer-Vietoris short complexes, `CategoryTheory.sheafIsAbelian`,
  sheaf exact-limit/colimit infrastructure and
  `CategoryTheory.ShortComplex.exact_iff_exact_map_forget₂`; none states closed-subset
  pushforward exactness.
- Loogle: `TopCat.Sheaf.pushforward, ShortComplex.ShortExact` returned an unknown-identifier
  diagnostic for `ShortComplex.ShortExact`; this was not treated as a negative search.
  The subsequent query `"pushforward"` returned twelve presheaf-of-modules pushforward
  primitives, not the desired exactness theorem.
- Mathlib grep: `pushforward.*(exact|Exact)|[Cc]losed.*pushforward` in `Topology/Sheaves`
  returned zero hits. Source inspection found the existing direct-image functor in
  `Topology/Sheaves/Functors.lean` and the stalkwise middle-exactness criterion in
  `Topology/Sheaves/Abelian.lean`, which is a proof ingredient rather than this node.
- `rg -n 'closed.*pushforward|pushforward.*[Ee]xact|lem-sc-closed-immersion-pushforward-exact'`
  in the source project's `WeilConjectures` and this project's `lean/Sheaf` found
  related scheme/module and étale results, docstring citations, the clopen-scheme
  theorem in `AlgebraicGeometry/Cohomology/Clopen.lean`, and the basiswise-surjectivity
  theorem in `Topology/Sheaves/PushforwardCohomology.lean`. Their full signatures and
  docstrings were read: the clopen theorem only concerns an open subscheme, and
  `TopCat.Sheaf.shortExact_map_pushforward` requires surjectivity on sections over
  a basis. Neither is the arbitrary closed-subset theorem of this node.
- An exact name search for `shortExact_map_pushforward_closedSubset` in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no duplicate.

Local single-file compilation passed without warnings. All binders and the universe
are explicit (`set_option autoImplicit false`). Only the named theorem has `sorry`.
No statement dispute or correction was necessary.

## Second reading by T1

Independent statement reading against `dag/nodes/sec-curve-estimates/lem-sc-closed-immersion-pushforward-exact.json` and the source place Stacks Project, Modules Lemma 01AX (Tag 01AX, exactness assertion):

- The node's object `X`, an arbitrary topological space, is rendered by
  `(X : TopCat.{u})`; no separation, finiteness, scheme, or nonemptiness assumption is added.
- The node's closed subset `Z ⊆ X` is `(Z : Set X)` with `(hZ : IsClosed Z)`. Empty and
  universal subsets remain allowed.
- The node's inclusion `i : Z → X` is the canonical continuous subtype map
  `(TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X)`, so it is
  the inclusion of the given subspace, rather than an arbitrary map or a different category.
- The node's abelian sheaves on `Z` and `X` are respectively
  `(TopCat.of Z).Sheaf AddCommGrpCat.{u}` and `X.Sheaf AddCommGrpCat.{u}`. These are the
  open-cover topological sheaf categories in the dependency definition
  `def-sc-topological-abelian-cohomology`; no ringed-space or scheme hypotheses occur.
- The node's formula `(i_*F)(U)=F(U ∩ Z)` is rendered by Mathlib's existing
  `TopCat.Sheaf.pushforward AddCommGrpCat.{u}` along the displayed inclusion. Its
  underlying presheaf is precomposition with `(Opens.map i).op`, hence evaluates at
  `i ⁻¹' U`, the relative open corresponding to `U ∩ Z`; no private pushforward
  definition was introduced.
- The node's conclusion that `i_*` preserves short exact sequences is rendered as
  `(S : ShortComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u})) (hS : S.ShortExact) ⟹
  (S.map (pushforward ... i)).ShortExact`. `S` contains the three sheaves, both maps,
  and the zero composite, and `ShortExact` includes monicity, middle exactness, and
  epicality, so no clause is omitted or strengthened. Quantification is over every
  short complex and its short-exactness proof.

The source itself states exactness (alongside fully faithfulness, essential image, and a
left inverse); the node deliberately records only the exactness assertion, as its source
place specifies. The Lean assumptions match that assertion exactly. The proof docstring
in the declaration follows the node's three proof steps: on-image stalk identification,
off-image zero stalks plus stalkwise exactness, and stalkwise detection on `X`; it cites
`lem-sc-closed-pushforward-abelian-stalks` and `lem-sc-abelian-sheaf-short-exact-stalkwise`.
The theorem proof remains `sorry`, as required for a stage-2 statement module.

Edge cases checked: `Z = ∅` (all pushforward stalks and sheaves are zero), `Z = Set.univ`
(the identity inclusion case), `X = ∅`, singleton closed subsets, zero sheaves, and zero
short exact complexes. The arbitrary common universe `u` does not exclude these cases;
there is no characteristic, Noetherian, finiteness, or nonempty assumption.

Existing-definition searches were repeated: `msearch.py` LeanFinder search for closed-subset
pushforward exactness (generic short-exact/object-property hits only); Loogle searches for
`TopCat.Sheaf.pushforward` and short exactness (pushforward primitives only); grep over
Mathlib `Topology/Sheaves`, the slopmaster2 `WeilConjectures` tree, and this project's
`lean/Sheaf` tree (no exact closed-subset pushforward theorem); and exact-name search for
`shortExact_map_pushforward_closedSubset` (no duplicate). Mathlib's existing
`TopCat.Sheaf.pushforward` is used directly.

No mismatch was found and no source, node, or Lean statement was changed. The only
assumption that is not syntactically used in the displayed term is `hZ`; it is nevertheless
present exactly as the node's closed-subset hypothesis and is required by the theorem's
mathematical claim. No new definition or dependency module is needed.
