## Worker report

The module `Sheaf.RingTheory.DirectedRingCoconeRecognition` states
`CommRingCat.directed_cocone_recognition`, with its proof entirely `sorry`.
There are no new definitions, dependency modules, or statement corrections.
The item's existing statement and accepted five-step proof are unchanged.

Sources read: `literature/stacks-project/categories.tex`, Tag 04AX,
`section-directed-colimits` (the representative and eventual-equality description),
and Tag 002F, `definition-colimit` (the universal property and uniqueness up to
unique isomorphism). Also read `more-groupoids.tex`,
`equation-sections-of-intersection`, which motivates the algebraic recognition
criterion. The theorem docstring carries all five proof steps, including the
common-stage argument and the naturality calculation, with its blueprint id.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The small nonempty directed index is `{I : Type u} [Preorder I]
  [Nonempty I] [IsDirected I (· ≤ ·)]`. This follows the project's DIRECTED SETS
  convention (Stacks 00D3); no antisymmetry is used in the node or its proof.
  All posets in the node are included. Index and ring universes are the same,
  following the project's index-universe convention; `u` is explicitly bound.
- The ring diagram is `F : I ⥤ CommRingCat.{u}`. Its values are precisely
  commutative rings and its arrows unital ring maps. `Functor.map_id` and
  `Functor.map_comp` are the two transition laws. The preorder category has
  one arrow `homOfLE h` for a comparison `h : i ≤ j`.
- The supplied ring and maps are `c : Cocone F`: `c.pt` is R and `c.ι.app i`
  is q_i. The cocone naturality law is q_j f_ij = q_i. Bundling does not
  introduce a property beyond the stated compatibility.
- Every r has a representative: `hrep` is exactly
  `∀ r : c.pt, ∃ (i : I) (a : F.obj i), c.ι.app i a = r`.
- Same-stage equality becomes eventual equality: `heq` quantifies over i,a,b,
  assumes equality of their images, and supplies k and `hik : i ≤ k` with
  equality under `F.map (homOfLE hik)`.
- The ring colimit conclusion is the witness `hR : IsColimit c`.
  The additive conclusion is `hA : IsColimit` of the cocone mapped by
  `forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat`. This is the
  actual composite of Mathlib's forgetful functors, since there is no direct
  `HasForget₂ CommRingCat AddCommGrpCat` instance in the imported interface.
  The set conclusion is `hS : IsColimit ((forget CommRingCat).mapCocone c)`.
- The explicit existence and uniqueness for every compatible family of ring
  maps, additive maps, or functions is precisely `IsColimit.desc`, `.fac`,
  and `.uniq` for hR, hA, hS. A compatible family t_i into B is a cocone s;
  `.desc s` is the requested t, `.fac s i` says t(q_i(a)) = t_i(a), and
  `.uniq s` says every other such map equals t. This uses the existing
  definition without copying it or adding a redundant reformulation.
- The second diagram and supplied cocone are `F'` and `c'`. The next two
  quantified assumptions repeat hrep and heq verbatim for that cocone.
- The compatible component ring maps are `τ : F' ⟶ F`; naturality is exactly
  f_ij u_i = u_j f'_ij. The ring map R' to R is `u : c'.pt ⟶ c.pt`, with
  `∀ i, c'.ι.app i ≫ u = τ.app i ≫ c.ι.app i`, the required equation.
- The witnesses hR', hA', hS' identify the second cocones as colimits.
  Each of the three final conjuncts quantifies over any chosen colimit cocones
  d,d' in the respective category with witnesses hd,hd'. Thus the conclusion
  applies to any choices of colimits, without assuming a chosen colimit exists
  as an extra hypothesis. `hd'.coconePointUniqueUpToIso hR'` (respectively hA'
  or hS') is the canonical identification from the chosen source colimit to R'.
  `hd'.map d τ` is the induced colimit map; in the additive and set cases,
  `Functor.whiskerRight` sends τ through the relevant forgetful functor.
  The equation in each conjunct is α' ≫ u = v ≫ α, that is u α' = α v in
  the node's composition order. Both the comparisons and the induced map are
  canonical Mathlib constructions, not arbitrary maps with missing equations.
- Zero rings are allowed by `CommRingCat`, and there is no `Nontrivial` or
  injectivity hypothesis on any ring or map.

Dependency used: `def-weil-pbc-category-colimit`, a Mathlib leaf recorded as
`Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.colimit`,
with additional recorded declarations `Cocone`, `IsColimit`, `colimit.desc`
and `IsFiltered`. Read its complete node and the source signatures/docstrings:
`HasLimits.lean` for the chosen colimit, coprojections and canonical desc;
`IsLimit.lean` for `IsColimit` and its three fields, `IsColimit.map`, and
`coconePointUniqueUpToIso`. The latter two give the induced maps and canonical
identifications for arbitrary chosen colimit cocones. The dependency is used
directly through those recorded universal-property notions. It is both the
statement dependency and the only proof dependency, so its import is public.
Other public imports provide ring/additive forgetful functors, the preorder
category and `homOfLE`, `IsDirected`, and natural-transformation whiskering.
No proof-only module remains to import.

Edge cases checked before drafting: an empty index is explicitly excluded by
the node and `[Nonempty I]`; a singleton index gives an isomorphism onto the
supplied ring by the two assumptions, in all three categories. The constant
zero-ring diagram and its zero-ring cocone are admitted. Noninjective maps are
allowed (e.g. a two-stage diagram Z to Z/2 with its final-stage cocone). A
nonzero ring mapping to a zero-ring colimit is allowed if same-stage equality
becomes equal later. Taking identity maps of diagrams and cocones gives the
identity naturality square. Arbitrary choices d,d' impose no extra global
`HasColimit` instance. No universe below the objects is used for test objects.

Searches actually run:

- `msearch.py ... leanfinder`: "A cocone of commutative rings indexed by a
  directed nonempty poset is a colimit in rings abelian groups and sets if
  every element is represented and equality holds at a later stage".
  Eight hits, including `CommRingCat.Colimits.colimitIsColimit`,
  `CommRingCat.FilteredColimits.colimitCoconeIsColimit`, and `Ring.DirectLimit`;
  none states the entire supplied-cocone criterion and its naturality.
- `msearch.py ... loogle`: `CommRingCat, CategoryTheory.Limits.IsColimit`.
  Twelve hits, including constructions of ring colimits, filtered local-ring
  facts, coproduct and pushout colimits; no exact statement.
- `msearch.py ... grep`: `isColimitOf|isColimit.*(surjective|injective)` in
  `Algebra/Category/Ring`. Seven hits, mostly colimit reflection; none is the
  three-category statement with comparison-map functoriality.
- `msearch.py ... leansearch`: "Recognize a supplied directed ring colimit
  cocone from representatives and eventual equality, with natural comparison
  maps in rings groups and sets". Eight hits constructing ring colimits and
  direct limits, not this recognition theorem.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf`, and a search
  by item id in `dag/lean_names_upstream.json`: no declaration for the item.
  Concept searches found the private `RingHom.colimit_of_rep_zero` in
  `WeilConjectures.RingTheory.DirectedTensorCoconesColimit`; read it in full.
  It proves only a ring recognition statement with extra preservation/existence
  assumptions, no additive/set conclusions or naturality, so is not an exact
  reusable attachment. Other hits concern sheaf or scheme colimits.
- Read `Mathlib/CategoryTheory/Limits/Types/Filtered.lean`, especially
  `Types.FilteredColimit.isColimitOf'`: the set criterion matches one part,
  but not the ring/additive clauses or comparison naturality. Read the ring
  colimit construction in `Algebra/Category/Ring/FilteredColimits.lean` too.

Validation uses only `scompile.py` and the prescribed `deliver2.py` dry run
and delivery; no direct build or git operation is run in the shared checkout.

## Second reading by Q129

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
