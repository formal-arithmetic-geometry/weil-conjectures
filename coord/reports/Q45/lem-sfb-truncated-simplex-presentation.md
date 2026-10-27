## Worker report

Item: `lem-sfb-truncated-simplex-presentation`. Module:
`Sheaf.AlgebraicTopology.TruncatedSimplexPresentation`; declaration:
`CategoryTheory.SimplicialObject.Truncated.truncated_simplex_presentation`.
This single theorem has proof `sorry` and states all four conclusions of the node.
There are no new definitions, new nodes, dependency repairs, or statement corrections.

Source read: `literature/stacks-project/simplicial.tex`, lemma-face-degeneracy
(Tag 0166), lemma-relations-face-degeneracy (0167), lemma-face-degeneracy-category
(0168), lemma-characterize-simplicial-object (016B), and
 definition-truncated-simplicial-object (0180). The bounded presentation proof is
exactly the supplied DAG argument, reproduced step by step in the theorem docstring.
The node's source is the bounded-degree specialization of these statements.

Hypotheses, clause by clause:

- `N : ℕ` expresses every nonnegative truncation bound, including zero.
- `{C : Type u} [Category.{v} C]` is an arbitrary category, with independent
  object and morphism universes and no limit, colimit, nonemptiness, or smallness assumptions.
- `SimplexCategory.Truncated N` is the full subcategory on the ordinals of
  degrees at most N. `U : (SimplexCategory.Truncated N)ᵒᵖ → C` specifies precisely
  the objects U_0,...,U_N. These are the actual ordinal objects, rather than an
  additional object model: every simplex is uniquely its `mk len`, and the bound
  witnesses are proof irrelevant. No degree greater than N is supplied.
- `d n hn i` has source U_(n+1), target U_n, and `i : Fin (n+2)`;
  `hn : n+1 ≤ N` is exactly 1 ≤ r ≤ N for r=n+1.
- `s n hn i` has source U_n, target U_(n+1), and `i : Fin (n+1)`;
  its same degree bound is exactly 0 ≤ r < N for r=n.
- `hdd`: the larger face index is `j.succ`, so `i ≤ j` is exactly
  i < j+1. The equation is d_i d_(j+1) = d_j d_i in the node's right-to-left
  convention. `hn : n+2 ≤ N` retains precisely the three required degrees.
- `hds_lt`: the degeneracy index is `j.succ`; `i ≤ j.castSucc` is precisely
  i < j+1. It states d_i s_(j+1) = s_j d_i, with middle degrees n,n+1,n+2.
- `hds_self` and `hds_succ`: s_i followed by d_i, respectively d_(i+1), is
  the identity, including degree zero and the maximal allowed degree pair.
- `hds_gt`: the face index is `i.succ` and the degeneracy index is j;
  `j.castSucc < i` is exactly i+1 > j+1. The equation is
  d_(i+1) s_j = s_j d_i. The three degrees are again bounded by `n+2 ≤ N`.
- `hss`: `i ≤ j` and the equation s_j followed by s_i equals s_i followed
  by s_(j+1), exactly s_i s_j = s_(j+1) s_i in right-to-left notation.
  It has precisely the required three-degree bound.

Conclusions, clause by clause:

- `∃! F : SimplicialObject.Truncated C N, ...` is existence and uniqueness
  as an actual functor, not merely uniqueness up to isomorphism. `F.obj = U`
  fixes its objects. The two following universal clauses fix the images of
  `SimplexCategory.Truncated.δ` and `.σ` on every retained degree and index.
  `HEq` here is dependent equality of morphisms; with the stated object-function
  equality it is exactly equality after its necessary endpoint transports.
- The first `MorphismProperty.multiplicativeClosure ... f` says every arrow is
  a finite composite of the indicated coface or codegeneracy arrows. Membership
  in each generating family is equality of `Arrow.mk` objects, which includes
  both endpoints and the map, not merely equality of underlying untyped maps.
  Mathlib's closure has constructors `of`, `id`, `comp_of`; thus it means a
  finite composable word, including the empty word. Its ambient category is
  `SimplexCategory.Truncated N`, so every intermediate degree is at most N.
- The second closure clause assumes exactly
  `Function.Surjective f.hom.toOrderHom` and allows only codegeneracies as
  generators. It retains identities and the same bound on all intermediate objects.
- For arbitrary truncated functors `F G` and component family `η`, the left
  side of the final equivalence is the complete naturality equation for every
  arrow of the opposite category. This is exactly the `NatTrans.naturality`
  field; `η` itself supplies the component field. The right side consists of
  its equations on every coface and every codegeneracy, with the endpoints
  reversed correctly. This characterizes natural transformations without
  postulating an arbitrary comparison morphism or omitting either generator type.

Dependency declarations and imports:

- The sole statement dependency `def-weil-pbc-simplicial-coskeleton` is a Mathlib
  leaf. Its `mathlib_match` records
  `CategoryTheory.SimplicialObject.Truncated` from
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`: precisely the functor
  category used by this statement. Read its full abbreviation and the adjacent
  truncation/coskeleton interfaces; no coskeleton or Kan extension is needed here.
- `SimplexCategory.Truncated`, its inclusion and its ordinal-object encoding
  are read in `Mathlib.AlgebraicTopology.SimplexCategory.Defs`.
- `SimplexCategory.Truncated.δ` and `.σ` are read in
  `Mathlib.AlgebraicTopology.SimplexCategory.Truncated` and imported through
  `Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty`. In particular,
  their bound arguments occur in opposite orders; the delivered code uses each
  signature correctly. `MorphismProperty.multiplicativeClosure` is reused from
  `Mathlib.CategoryTheory.MorphismProperty.Composition`.
- The recorded proof dependency `lem-sfb-pure-coface-word-relations` is imported
  privately as `Sheaf.AlgebraicTopology.PureCofaceWordRelations`, whose full
  `SimplexCategory.CofaceWord.related_of_eval_eq` signature and proof docstring
  were read. The other proof dependency,
  `lem-sfb-pure-codegeneracy-word-relations`, has no recorded declaration at the
  time of reading and is not imported. Its proof step remains in the docstring;
  it is not needed to elaborate a statement with proof `sorry`.

Edge cases checked before and after writing:

- N=0: no d or s exists, all identity hypotheses are vacuous, and the sole
  ordinal endomorphism is the identity. The closure permits its empty word.
  The theorem gives the unique functor on its specified object, and every
  component family is natural. No `NeZero N` or extra positive bound is imposed.
- N=1: both faces U_1 → U_0 and the single degeneracy U_0 → U_1 exist.
  Both retraction identities remain; the three-degree identities are vacuous.
- A face index at its last allowed position and the two mixed cancellation
  cases are included by `Fin.castSucc` and `Fin.succ`; these are not restricted
  to interior indices. The shifted presentations are exactly Mathlib's
  general simplicial identities, read in SimplicialObject.Basic, lines 113--203.
- Empty C does not acquire an object or nonemptiness assumption: there can be
  no object family U since [0] exists, so the conditional statement is vacuous.
  No extra algebraic condition is imposed on C.
- Surjective identity maps are allowed at every degree, including [0].
- Functor object equality and proof-irrelevant bound witnesses permit all
  categories, including ones with distinct isomorphic objects; the theorem
  fixes equality of objects and never replaces it by an arbitrary isomorphism.

Searches for an existing exact statement (2026-10-24):

- `msearch.py leanfinder`: "A truncated simplicial object is uniquely determined
  by face and degeneracy operators satisfying simplicial identities in retained
  degrees". Eight hits: truncated functor definitions, coskeletality, extensionality,
  truncation; none reconstructs from generators with the bounded relations.
- `msearch.py loogle`: "SimplexCategory.Truncated, SimplicialObject.Truncated".
  Zero hits, with unknown unqualified `SimplicialObject.Truncated`; the fully
  qualified definition was found and read directly and through LeanSearch.
- `msearch.py leansearch`: "Construct truncated simplicial object from face maps
  degeneracy maps identities". Eight hits: truncated definitions and special
  already-simplicial identities, not the combined recognition/presentation statement.
- `msearch.py grep`: "Truncated|presentation|multiplicativeClosure" in
  AlgebraicTopology/SimplexCategory. Twenty-two hits. Read GeneratorsRelations/Basic,
  EpiMono, Truncated, and MorphismProperty. The existing
  `SimplexCategory.Truncated.morphismProperty_eq_top` supplies the ordinary
  generator induction principle, but neither reconstruction from bounded
  identities nor surjection-only generation nor the full node's statement.
  The new theorem includes the ordinary generation clause using Mathlib's
  closure definition, rather than creating a second word datatype.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf/AlgebraicTopology` for
  `Truncated`, truncated presentations, and face/degeneracy descriptions:
  coskeleton applications, horn filling, finite-coface complexes, but no exact
  bounded reconstruction theorem. `grep -rn` for this item id in
  `lean/WeilConjectures` found nothing. A full-name/module-name search in
  `dag/lean_names_upstream.json`, Mathlib, WeilConjectures, and Sheaf found no
  existing `truncated_simplex_presentation` or `TruncatedSimplexPresentation`.

No `STATEMENT-DISPUTED` flag or source-based node correction is necessary.
Only the item's `lean` field changes. No statement, dependencies, proof plan,
or other node metadata is edited. There is one named postponed theorem and
no postponed data.

Validation: compiled via prescribed `scompile.py`, including module mode,
`autoImplicit false`, explicit universes, and public statement/private proof
imports. Local compilation ran out of device space, and the wrapper's normal
server confirmation compiled the module successfully within 60 seconds.
The final delivery dry run and push are recorded by `deliver2.py`.

## Second reading by Q45

This is the author's separate second pass with both the JSON node and final
Lean source open. The dispatcher forbids starting additional agents; the
maintainer provides the independent review after delivery.

Rechecked each binder and conclusion against the source and the node. All six
identity hypotheses (the two cancellation equations are separate hypotheses)
cover precisely the stated indices and degrees. In particular hdd changes the
larger index from j to j+1, hds_lt changes the degeneracy index to j+1, and
hds_gt changes the face index to i+1; the remaining finite-index inequalities
are equivalent to the printed strict inequalities, not additional assumptions.
The sigma bound arguments were reversed in the initial draft and were corrected
against the actual Mathlib signature before the clean compile. Object-bound
proofs now explicitly reduce ordinal length to the natural-number degree.

The finite-generation predicates were also tightened from heterogeneous map
equality to equality of bundled `Arrow.mk` objects. This makes source and target
equality explicit in generator membership. The recognition conclusion keeps
heterogeneous equality only where `F.obj = U` already supplies those endpoint
equalities. Naturality has both generator families and both sides are oriented
as the definition of a natural transformation requires. Rechecked N=0, N=1,
empty C, all endpoint indices, and identity surjections. The source/node statement
requires no correction; the final module states all its clauses.
