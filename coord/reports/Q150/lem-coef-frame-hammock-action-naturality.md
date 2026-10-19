## Worker report

The module `Sheaf.CategoryTheory.FrameHammockActionNaturality` states
`CategoryTheory.frameHammockActionNaturality`, with one postponed theorem and real
helper data. The node's natural-language statement, source, proof, and proof dependencies
are unchanged. Its statement dependencies gain the two landed nodes
`lem-coef-special-resolution-zigzag-nerve` and
`lem-coef-hammock-graph-colimit-presentation`, whose existing index category and grid
inspection operations are used in the signature. There are no new nodes or dependency
repairs.

Source read: [Low, Revisiting function complexes and simplicial localisation](https://arxiv.org/pdf/1409.8062),
Definition 3.1, Lemma 3.4 and Proposition 3.7(ii), printed pages 12–15. Low's special-resolution
comparison uses a model category. This item is the already-reviewed agent extension to
weak augmentations in the node, with its seven explicit proof steps; the formal statement
retains that extension and adds no model-category hypotheses. The module's theorem
docstring gives those seven steps, including both padded-row homotopies and the passage
to the localization of simplicial sets at weak homotopy equivalences.

Hypothesis and clause correspondence:

- The category is `{C : Type u} [Category.{v} C]`, with independent object and morphism
  universes. The wide subcategory is `(W : MorphismProperty C) [W.IsMultiplicative]`;
  this records identities and closure under composition. Two-out-of-three is
  `[W.HasTwoOutOfThreeProperty]`.
- The specified hammock localization is `(H : HammockLocalization W)`, using the
  dependency's actual reduced-hammock mapping simplicial sets and enriched operations.
  This parameter retains the chosen realization of the hammock construction, rather
  than introducing another localization.
- Endpoints are `{x y : C}`, the diagrams are `(P : SimplexCategory ⥤ C)` and
  `(Q : SimplexCategoryᵒᵖ ⥤ C)`, and the augmentation/coaugmentation are `p` and `i`.
  The hypotheses `hp` and `hi` mark every component, including degree zero.
- `ResolutionIndex (specialResolutionHomDiagram P Q)` is precisely the existing
  category with objects `(m,n,h)`. The existing `ResolutionIndexHom` has `α` and `β`
  in the specified directions. Unfolding its `comm` and the Hom diagram gives
  `h ≫ Q.map β.op = P.map α ≫ h'`; its composition is the specified index composition.
  These declarations require no model structure.
- Universe enlargement is `FiniteReedy.largeNerve.{v, 0, max u v}`. This is the actual
  ordinary nerve followed by a degreewise ULift; `s.down` is the original chain.
  Mapping simplicial sets of `H` have the same `max u v` universe. No objects or
  morphisms are discarded or identified by this lift.
- The existence of the simplicial map γ is `∃ G : FrameHammockComparison H p i hp hi`.
  Its `map` has exactly the enlarged index nerve and the hammock mapping object as
  source and target. Its `grid` field specifies, for every degree and every chain,
  an unreduced path with exactly three horizontal entries in each row: backward `p`,
  forward `h`, backward `i`. The additional vertical-list equality specifies all
  comparable pairs of rows, not just the vertices or adjacent rows: endpoint identities,
  `P.map α`, and `Q.map β.op`. The chains in that path are `HammockChain W k`, so
  their vertical arrows lie in W. `HammockReduces` then identifies the image simplex
  with the reduction of this very grid. Thus the comparison is characterized in every
  degree, including its degeneracies; it is not an arbitrary map with the right type.
- Strict functor naturality is the first conjunct. `F`, `V`, and `hF` are the functor
  of pairs, the target wide subcategory, and preservation of W. `pD`, `iD` with `_ep`
  and `_ei` express exactly the image augmentations componentwise; `hpD` and `hiD`
  are their marking witnesses (obtained from `hF` in an application). The functor
  `resolutionIndexMap (frameHammockHomFunctorMap F P Q)` sends `h` to `F.map h` and
  retains α,β. `G'` denotes the same grid comparison in D. `E` with `_hE :
  IsHammockMap H K F hF E` is the dependency's actual entrywise enriched hammock
  functor. `HEq (G.map ≫ E.map x y) (NI(F) ≫ G'.map)` expresses strict equality
  with only the endpoint-object transport supplied by `IsHammockMap`; it is not a
  homotopy-category equality. It applies to every comparison with the displayed
  all-simplex formula, so does not depend on arbitrary choices of comparison data.
- The second conjunct binds the new endpoints `x',y'`, endpoint arrows `c,d`, new
  diagrams `P',Q'`, augmentations `p',i'`, and their component hypotheses `hp',hi'`.
  `a : P' ⟶ P`, `b : Q ⟶ Q'` have exactly the requested directions, and `_ha`, `_hb`
  mark every component. `_hc` is `a ≫ p = p' ≫ const(c)` and `_hd` is
  `i ≫ b = const(d) ≫ i'`, exactly the covering equations in functional notation.
- The map of index nerves is the existing
  `resolutionIndexMap (specialResolutionHomMap a b)`; on the middle arrow this is
  `a.app _ ≫ h ≫ b.app _`, i.e. `b h a` in functional order. It retains α and β.
  `G'` again has the exact grid formula, now for the primed diagrams.
- The canonical endpoint action is `∃ A : FrameHammockEndpointAction H c d`.
  Its `formula` characterizes every image simplex by concatenating the actual-arrow
  path of `c`, the original reduced hammock, and the actual-arrow path of `d`, then
  reducing. This is precisely enriched precomposition and postcomposition, as specified
  by `H.composition` and `hammockActualPath`, and does not allow an unconstrained map.
  The final equality applies `SSet.KanQuillen.weakEquivalenceStructure.weakEquivalences.Q`
  to both composites. This Q is localization at weak homotopy equivalences, so the
  equality is exactly in the requested homotopy category of simplicial sets.
- The theorem has no Reedy, lifting, model-category, cofibrancy, or fibrancy assumptions.
  No conclusion states that γ is a weak equivalence. The padded-row comparisons with
  vertical arrows a,b are the construction described in proof steps 5 and 6; their
  common endpoint yields the asserted homotopy-category equality in step 7.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.HammockInfinityLocalization`: `HammockLocalization`,
  `HammockChain`, `HammockStep`, `hammockEndpoint`, `HammockReduces`,
  `hammockActualPath`, `HammockObjects`, `IsHammockMap`; also the recorded theorem
  `hammockLocalization_universal` and its full docstring were read.
- Mathlib `AlgebraicTopology.SimplicialSet.Basic`: `SSet`, the contravariant simplex
  functor. The other clauses of the Mathlib leaf were checked at `SSet.degenerate`,
  `SSet.nonDegenerate`, `SSet.Subcomplex`, `SSet.Finite`; those clauses are not needed
  in this statement and no extra imports for them are introduced.
- `Sheaf.CategoryTheory.SpecialResolutionZigzagNerve`: `ResolutionIndex`,
  `ResolutionIndexHom`, `resolutionIndexCategory`, `specialResolutionHomDiagram`,
  `resolutionIndexMap`, `specialResolutionHomMap`, `resolutionLargeNerveMap`.
  The signatures/docstrings and concrete implementations were read. Only their
  model-free declarations are used; the specialized theorem is not assumed.
- `Sheaf.CategoryTheory.FiniteReedyLocalization`: `FiniteReedy.largeNerve`, the
  recorded degreewise ULift of the ordinary nerve, transitively available above.
- `Sheaf.CategoryTheory.HammockGraphColimitPresentation`: `SSet.Hammock.pathRowData`
  and `SSet.Hammock.pathChains` specify the grid; the proof uses the recorded
  `hammock_graph_colimit_presentation` for simplicial reduction, including identities.
- `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak` is a proof-only import:
  `SSet.Enhanced.simplicial_homotopy_equivalence_weak` justifies the interval projection
  without Kan or nonemptiness assumptions.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`, transitively available through the
  index module: `SSet.KanQuillen.weakEquivalenceStructure` is explicitly the weak
  homotopy equivalence predicate, and its `weakEquivalences.Q` is the localization.

Edge cases checked: degree zero gives the single three-arrow row; repeated vertices
and identity index arrows are retained by the unreduced grid; columns entirely equal
to identities are permitted before reduction; when endpoints agree, reduction may give
the empty hammock. An empty index category has an empty nerve and the formulas impose
no nonexistent simplex. Identity a,b,c,d and coinciding endpoints are included; W can
consist of identities. A relative functor may create new identities, since `_hE` uses
entrywise application followed by reduction. No nonemptiness or Kan assumption occurs.
Independent u,v are retained; any two categories of a functor can be placed in a common
enlarged pair of universes, as the node explicitly permits.

Searches made with `msearch.py`, Q150 and this item:

- LeanFinder: “Weakly augmented cosimplicial and simplicial diagrams define natural maps
  from their index nerve to hammock localization mapping spaces”: eight hits, ordinary
  nerve maps and truncated nerve adjunctions; none states the comparison or naturality.
- Loogle: `CategoryTheory.nerveMap, CategoryTheory.ResolutionIndex`: zero hits;
  ResolutionIndex is not a Mathlib identifier.
- Mathlib grep: `hammock|weakly.augmented|ResolutionIndex` in AlgebraicTopology:
  zero hits.
- LeanSearch: “Weak augmentation diagrams give maps from their index nerve to hammock
  localization natural under endpoint changes”: eight hits about Čech nerves, augmented
  whiskering and the nerve adjunction; no match.
- `rg` in the upstream WeilConjectures tree for `hammock|weakly.augmented|ResolutionIndex`
  and for the exact item id: no hits. `rg` in project `lean/Sheaf` found the existing
  index category and its helpers in SpecialResolutionZigzagNerve, which are reused.
- Exact name duplicate search for all four new declarations in Mathlib, upstream
  WeilConjectures, project `lean/Sheaf` and `dag/lean_names_upstream.json`: no hits.

Validation: the prescribed `scompile.py` compiled the sandbox and final module separately
with no errors or warnings, within the 60-second per-file limit. The one theorem has
proof `by sorry`. No statement dispute or source correction is needed.

## Second reading by Q150

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
