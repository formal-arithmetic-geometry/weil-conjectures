## Worker report

The module `Sheaf.CategoryTheory.CellularTreePresentableApproximations` states
`CategoryTheory.CellularTree.exists_presentableApproximations`, with its only theorem
proof `sorry`. Its two data structures package exactly the tree maps and witnesses in
the conclusion; they do not replace `CellularTree`, add an independent mathematical
notion, or choose data from a postponed existence theorem. Their fields have real types
and every witness is quantified by `Nonempty` in the theorem's conclusion.

The source was read online in Lurie's *Higher Topos Theory*, Lemma A.1.5.11 and its
proof, printed pp. 806-807, and Lemma A.2.6.9, observation (ii), printed p. 822:
https://people.math.harvard.edu/~lurie/papers/HTT.pdf . This is the auxiliary statement
specified by the node, expanding compact-root descent; it is not asserted to be a
separately numbered statement in HTT. The current blueprint's
`sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`
was also read for the ancestor context. No statement correction is made.

Hypotheses and clauses, in the node's order:

- The small universe is `v`; `A : Type u` has `Category.{v} A`, so small Hom sets,
  small trees, supports and colimit indices use the same universe. No equality of the
  object and Hom universes is imposed.
- `κ : Cardinal.{v}`, `[Fact κ.IsRegular]`, and `hκ : Cardinal.aleph0 < κ` express
  the uncountable regular cardinal. `[IsCardinalLocallyPresentable A κ]` is Mathlib's
  cocompleteness plus a small cardinal-filtered generating family of presentable objects.
- `L : MorphismProperty A`, `X : A`, `T : Type v`, `[PartialOrder T]`,
  `[WellFoundedLT T]`, `tree : CellularTree L X T`, and `hgood : tree.IsGood κ`
  supply the fixed good labeled tree. In particular the root is unrestricted. No
  weak-equivalence class, cofibration hypothesis, or generation hypothesis is added.
- `PresentableApproximations.P`, `order`, and `filtered` give a small cardinal-filtered
  poset. `support`, `lower`, `small`, and `increasing` give the increasing lower subsets
  of size strictly below κ. Repeated supports are allowed.
- `arrows : P ⥤ Arrow A` is the diagram of arrows, and `presentable` requires both
  endpoints at each stage to be κ-presentable.
- `trees p : CellularTree L (arrows.obj p).left (support p)` supplies the tree at each
  stage. `totalIso p` identifies its undercategory colimit with the stage arrow, hence
  fixes the root identification as well as its endpoint.
- `cocone`, `apex`, and `colimiting` give a colimiting arrow cocone with apex precisely
  the original root-to-total arrow. The original total is `subsetObj tree.diagram Set.univ`,
  the colimit of the whole tree reindexed by its full subset. `eqToHom` only transports
  along the equality of the cocone apex with this arrow; it introduces no arbitrary map.
- `toOriginal p` is a `LabeledMap`. Its `vertex`, `root_vertex`, and `naturality`
  describe a map of diagrams along the inclusion of the support. `predecessor`,
  `root_predecessor`, `predecessor_ι`, and `predecessor_vertex` characterize the canonical
  predecessor-colimit maps, including empty predecessor diagrams. `source_eq`,
  `target_eq`, and `cell_eq` identify each cell with the specified original arrow;
  `attach_comm` and `target_comm` require the identity on both cell objects in the
  attaching squares. Thus a tree with some other cells is not a witness.
- `pushout_vertex` expresses the objectwise pushout identifications along the root map.
  A pushout square induces the canonical isomorphism from the chosen pushout object;
  the diagram naturality and the cell-leg equalities make these isomorphisms maps of
  the original labeled trees, rather than unrelated isomorphisms of objects.
- `toSupport`, `support_root`, and `support_vertex` characterize the canonical map
  from each stage total to the original restricted total. `support_apex` identifies
  its composite to the full total with the given arrow cocone component.
- `transition p q h` gives the map of trees on common cells for every `p ≤ q`, using
  the left component of `arrows.map (homOfLE h)` as root map. `transition_total`
  identifies its induced total map with the right component. `transition_original`
  and `predecessor_original` express compatibility with the pushout identifications;
  `transition_id`, `transition_comp`, `predecessor_id`, and `predecessor_comp` give
  identity and composition laws. Root identity, composition, and compatibility are
  already the functor and cocone laws of `arrows` and `cocone`. Equality of the label
  maps uses the same source/target identifications throughout.
- `cofinal_supports` quantifies over every small subset `E`, whether downward closed
  or not, and gives a stage containing it.
- `filtered_unions` quantifies over every `Q : Set P` with `[IsFiltered Q]`, using
  the inherited order. This includes nonemptiness. There is no small-cardinality or
  κ-filtered requirement on Q. The union is written `{t | ∃ q : Q, t ∈ support q.val}`.
- In this clause `c` is a colimiting cocone on the restriction of `arrows` to Q.
  The two additional `IsColimit` witnesses for its images under `Arrow.leftFunc`
  and `Arrow.rightFunc` explicitly say its endpoints are the respective objectwise
  colimits `M_Q` and `N_Q`. This uses the universal-property definition of colimit,
  and imposes no choice of representative for a colimit object.
- `d` is a cellular tree on that union with root `c.pt.left`; `e` identifies its
  total arrow with `c.pt.hom`. Its `comparison : LabeledMap d tree ... r` retains
  exactly the original cell arrows. The first equation characterizes `r` by its
  composites with all root coprojections. The next equation characterizes `b` on
  the descended tree vertices; the following equation characterizes it directly on
  every stage endpoint via `toSupport` and the canonical inclusion of supports.
  Thus the square uses the canonical comparison, even when maps into the full tree
  total fail to be monomorphisms.
- `IsPushout c.pt.hom r b ...` is exactly the asserted square to the original union
  restriction. The final quantification over all classes `W` containing L, isomorphisms,
  and closed under cobase change, small transfinite composition, and arrow retracts
  expresses membership in the weakly saturated closure of L. It uses precisely the
  convention of the tree-presentation dependency.

Dependencies used and read:

- `Sheaf.CategoryTheory.WeakSaturationTreePresentation`,
  `CategoryTheory.weakSaturation_good_tree_presentation`: full signature and proof
  docstring read. The module supplies the exact cardinal, locally presentable and
  weak-saturation conventions; its tree transition assertion is the proof input for
  weak-saturation membership in the final clause.
- Its definition dependency `Sheaf.CategoryTheory.CellularTree`: the full module,
  `CategoryTheory.CellularTree`, `CellularTree.IsGood`, `subsetDiagram`, `subsetObj`,
  `subsetMap`, and `predecessorMap` were read and reused. The original node already
  makes these available through the tree-presentation dependency.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, and their canonical coprojections; the recorded declaration's
  source and docstring were read. `IsFiltered` was read in `Filtered.Basic`.
- Mathlib's `IsCardinalPresentable`, `IsCardinalLocallyPresentable`, and
  `IsCardinalFiltered` were read at their definitions. The structure maps use Mathlib
  `Arrow`, `Under`, `IsPushout`, `HasCardinalLT`, and `IsLowerSet` directly.

Edge cases checked: empty T is allowed (all cellular requirements become empty,
while the statement still presents the arbitrary root); empty supports are allowed,
with the undercategory colimit supplying the root; minimal cells have an empty
predecessor diagram; Q is nonempty because `IsFiltered` includes that condition;
Q may be a singleton or have arbitrarily large small cardinality; the union need
not have size less than κ and its endpoints need not be presentable. Cofinal supports
include empty E and non-lower E. Root maps and tree maps are not assumed monic or
invertible. A zero/initial root, repeated cells, and repeated supports are not excluded.
No STATEMENT-DISPUTED or dependency interface fault was found.

Searches performed on 2026-10-17:

- `msearch.py ... leanfinder "A fixed good cellular tree is a cardinal filtered colimit
  of compatible presentable root trees with fixed labeled cells and downward closed
  supports"`: eight hits, on `SmallObject.relativeCellComplexιObj`,
  `RelativeCellComplex`, and their cell/attachment interfaces; none states fixed-tree
  presentable approximations with these support and subcolimit clauses.
- `msearch.py ... loogle '"IsCardinalPresentable", "RelativeCellComplex"'`: zero hits.
- `msearch.py ... grep 'tree|presentable|filtered' AlgebraicTopology/RelativeCellComplex`:
  zero hits.
- `msearch.py ... leansearch "Compatible presentable root approximations of a fixed
  cellular tree with small supports"`: eight unrelated polynomial-functor approximation
  and root-pairing hits, no match.
- `rg` on the upstream `WeilConjectures` for the item id and
  `CellularTree|cellularTree|GoodTree|LTree|presentable.approxim` found no declaration.
  `rg` in `lean/Sheaf` found only the tree definition, its presentation theorem, and
  a natural-language reference in `AccessibleIntersectionGenerators`; none is this
  statement. Searches for the proposed full helper names in the upstream name index,
  upstream source and side source found no collision.

Validation: compiled the delivered module through `scompile.py`, with all variables
and universes explicitly bound and `autoImplicit false`. Only the item node's `lean`
field is changed; no new node or dependency module is needed. The required dry run is
run after this report and the record are in place. The independent second reader is
responsible for its separate report section and delivery.

## Second reading by Q33

I read the item node, its source place, the recorded `CellularTree` and
`weakSaturation_good_tree_presentation` declarations, and the delivered module line by
line. The source is HTT Definition A.1.5.1 and Lemma A.1.5.11 (pp. 799--808), with
Lemma A.2.6.9 observation (ii) (p. 822); the node explicitly records this as an
agent-formulated auxiliary expansion.

The node's objects and hypotheses match the Lean signature as follows.

- The category is `A : Type u` with `Category.{v} A`; the inherited
  `HasColimitsOfSize.{v, v} A` is supplied by `IsCardinalLocallyPresentable A κ`.
  Thus the object and Hom universes remain independent, and all colimits are small.
- `κ : Cardinal.{v}`, `[Fact κ.IsRegular]`, and `hκ : Cardinal.aleph0 < κ` are
  exactly uncountable regularity. `IsCardinalLocallyPresentable A κ` is Mathlib's
  cocomplete, small-generator formulation of ordinary local presentability.
- `L : MorphismProperty A`, `X : A`, `T : Type v`, `[PartialOrder T]`,
  `[WellFoundedLT T]`, `tree : CellularTree L X T`, and `hgood : tree.IsGood κ`
  are the fixed arrow class, root, small well-founded indexing poset, specified cell
  data, and goodness assumptions. No weak-equivalence class or extra generation
  hypothesis is introduced.
- The structure `PresentableApproximations` introduces the small poset `P` and its
  `PartialOrder`, the cardinal-filtered witness `filtered`, supports `support`, their
  lower-set and `<κ`-cardinality fields `lower` and `small`, and the inclusion law
  `increasing`. These render the increasing downward-closed small supports exactly.
- `arrows : P ⥤ Arrow A` and `presentable` render the arrow diagram and the
  `<κ`-presentable endpoints `M_p` and `N_p`. `trees`, `totalIso`, and the fixed
  cell equalities in `LabeledMap` render an `L`-tree on each support whose total
  arrow is `h_p` and whose cells are the specified `P_t → Q_t`.
- `cocone`, `apex`, and `colimiting` render the colimiting cocone to the original
  arrow `X → Y_T`; `apex` identifies its apex with
  `Arrow.mk (subsetObj tree.diagram Set.univ).hom`, so no unrelated bottom arrow is
  chosen.
- `toOriginal` is the compatible map of trees on each support. Its vertex,
  predecessor, naturality, root, source, target, cell, attaching, and target-leg
  fields render the root maps, predecessor-colimit maps, order compatibility, and
  identity on every specified cell. `pushout_vertex` renders the objectwise pushout
  identification with the original restricted tree.
- `toSupport`, `support_root`, `support_vertex`, and `support_apex` render the
  canonical map from a stage total to the original restricted total and its
  compatibility with the full-tree inclusion. `transition` is the map on common
  cells for every `p ≤ q`, using the arrow diagram's left map as root map;
  `transition_total`, `transition_original`, and `predecessor_original` render its
  total and pushout compatibility. The vertex and predecessor identity/composition
  fields render the stated transition laws; root laws follow from functoriality of
  `arrows` and the cocone.
- `cofinal_supports` quantifies over every `E : Set T` of cardinality `<κ`, with no
  downward-closure restriction, exactly as the node requires.
- `filtered_unions` quantifies over every `Q : Set P` with inherited
  `[IsFiltered Q]`, which includes nonemptiness. Its cocone `c` and the three
  `IsColimit` witnesses render the arrow and endpoint colimits `M_Q`, `N_Q`; `d`,
  `e`, and `comparison` render the cellular tree on the union support with the same
  labels. The equations for `r`, the vertex comparison, and `b` give the canonical
  comparison to the original union restriction, and `IsPushout c.pt.hom r b ...`
  is precisely the node's canonical pushout square. The final quantification over
  every `W` containing `L` and closed under isomorphisms, cobase change, transfinite
  composition, and retracts is the recorded weak-saturation convention, so it says
  that `h_Q` lies in the weakly saturated closure of `L`.

No hypothesis is added, dropped, or strengthened beyond the explicit packaging of
the node's canonical maps and colimit universal properties. The theorem is
statement-only and its proof is `sorry`.

Edge cases checked: `T` and supports may be empty; empty predecessor diagrams use
the undercategory colimit; `E` may be empty or non-lower; supports may repeat; `Q`
may be a singleton or have arbitrary small cardinality; the union support need not
be `<κ`; roots and tree maps need not be zero, monic, or invertible; and the root
need not be presentable. The cardinal and scheme/category universes exclude none of
these cases.

Searches on 2026-10-17: semantic LeanFinder search returned only
`RelativeCellComplex`/small-object declarations; a Loogle search for
`IsCardinalPresentable` returned no declaration; and `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf` found no presentable-approximation or labeled-map
declaration. The only related project declarations are the recorded `CellularTree`
and weak-saturation presentation dependencies. Therefore H4 does not apply and no
new definition or dependency module is needed.

No mismatch was found, so no repair or statement correction was made. The module
passes `scompile.py` with no errors or warnings other than the permitted theorem
`sorry`; all variables and universes are explicitly bound and no line exceeds 100
characters.
