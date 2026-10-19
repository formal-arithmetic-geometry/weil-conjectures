## Worker report

The delivery states `SSet.Hammock.hammock_graph_colimit_presentation` in
`Sheaf.CategoryTheory.HammockGraphColimitPresentation`. Its only theorem has
proof `sorry`. All helper definitions and inductive relations have actual data;
no existence theorem is used to choose unspecified objects or maps. The
existential `PresentationData` packages a construction characterized on every
actual grid, including its specified operators and reduction maps.

I re-read the complete current node (all five proof steps), both statement
dependency nodes and their recorded modules, the existing reduced-hammock
helpers, and Dwyer--Kan, *Calculating simplicial localizations*, Definitions
2.1, 4.1, 4.4, 5.1, 5.3, Propositions 5.4--5.5 and Section 3.4, printed
pp. 19 and 21--24. Source:
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf .
The word convention is the node's left-to-right convention.

Each hypothesis and clause is rendered as follows:

- The small ordinary category is `{C : Type u} [Category.{v} C]`, with both
  universes explicit and simplices in `Type (max u v)`. The wide subcategory is
  `(T : MorphismProperty C) [T.IsMultiplicative]`: it contains identities and
  is closed under composition. `(x y : C)` are arbitrary endpoints. There is
  no two-out-of-three, saturation, or homotopy-calculus assumption.
- The index is the dependency's `SSet.SignedWord`, including length zero.
  `letters` maps its true signs to `RelativeZigzag.Letter.forward` and false
  signs to `.backward`, preserving the order of all positions.
- `PresentationData.G : SignedWord ⥤ SSet.{max u v}` is the required functor.
  `fixedWord w` identifies its value, as a simplicial set, with the dependency's
  `zigzagNerve T (letters w) x y`, not with an unrelated set of equal cardinality.
  Thus its q-simplices are strings of q morphisms in the recorded diagram
  category: exactly q+1 rows, marked downward vertical arrows, endpoint
  identities, unrestricted rightward arrows, and marked leftward arrows.
  Identity columns and adjacent equal signs remain permitted in this nerve.
- `paths` and `represents` specify the transpose of each nerve simplex as an
  actual path of `HammockStep` columns between constant endpoint chains.
  `GridRepresents` compares the complete horizontal arrow data in every row
  and the vertical data at every comparable pair of rows, including composites
  and identities. `vertices` includes both endpoints. It therefore retains all
  squares and vertical arrows, including those adjacent to an identity column.
- Faces and degeneracies on `G.obj w` are the ordinary nerve operators, because
  `fixedWord` is a simplicial isomorphism. They delete/repeat rows and compose
  intervening vertical arrows. `represents` also applies to every resulting
  simplex, so the path description has these same row operators.
- `wordMaps` requires `WordImage f` on every simplex. `WordImage` lists the
  target positions in order, with their signs and exact source-fiber sizes.
  `BlockImages` divides the original path into precisely these consecutive
  blocks. `ColumnComposite` composes a positive block forward and a negative
  block in the opposite arrow order. Its two nil constructors insert the
  respective identity column for an empty fiber. Composites are equalities of
  natural transformations of vertical chains, retaining all vertical data.
  Functoriality and commutation with all row operators are part of `G`.
- `proper : SignedWord.IsProper G` is exactly the dependency's two clauses:
  degreewise injectivity for word injections and the image-intersection formula,
  also when the intersection subword is empty.
- `H : SSet.{max u v}` and `simplices q : H _[q] ≃ ReducedHammock T x y q`
  specify precisely the reduced diagrams. The reused `ReducedHammock` is a
  column path with no `HammockReduction`: neither an identity column nor an
  adjacent equally directed pair remains. `HammockReduces` is the finite
  reflexive-transitive closure of exactly those two reductions in any context.
  Paths of length zero exist exactly when the endpoint objects agree; their
  single vertical chain is the constant identity chain.
- `rowOperators` requires every H-operator to apply `hammockRows` to the
  representative and then reduce it. This includes all faces and degeneracies;
  the simplicial identities are supplied by the actual simplicial set `H`.
- `reductionMap` is a cocone on `G` with value `H`; `reductionFormula` says
  every leg sends each actual grid path to its terminal reduct, rather than
  merely giving an arbitrary cocone. `reduction : colimit G ≅ H` is the claimed
  simplicial isomorphism, and `reductionLegs` identifies its composites with
  every canonical colimit injection with the specified reduction legs.
- `NaturalFor` quantifies over every pair functor `F : C ⥤ D` satisfying the
  explicit marking-preservation hypothesis `hF`. It supplies the target
  presentation `Q`, the natural transformation `g : P.G ⟶ Q.G`, and the
  simplicial map `h : P.H ⟶ Q.H`. The first conjunct says that `g` applies
  `hammockMapPath` entrywise, retaining every column and all vertical arrows.
  The second says that `h` applies that same functor and then reduces. The
  final equation is precisely
  `colimMap g ≫ Q.reduction.hom = P.reduction.hom ≫ h`.
  All these are simplicial maps, so their formulas include every nerve row
  operator. For simplicially varying pairs on a fixed object set, take `F` to
  be each simplicial structure functor. Entrywise action and terminal reduction
  determine the maps, so their identity/composition and mixed-operator laws
  are those explained in proof step 5 (R F R = R F and R F R alpha = R alpha R F).

Dependency declarations used:

- `Sheaf.CategoryTheory.ProperWordColimitInvariance`: `SSet.SignedWord`,
  `SignedWord.Hom`, `SignedWord.instCategory`, `SignedWord.IsProper`.
- `Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus`:
  `CategoryTheory.RelativeZigzag.Letter`, `Horizontal`, `Diagram`, `Vertex`,
  `objectAt`, `Hom`, `diagramCategory`, and `zigzagNerve`. Their complete
  signatures and docstrings, including the empty word, were read.
- `Sheaf.CategoryTheory.HammockInfinityLocalization`:
  `CategoryTheory.HammockChain`, `HammockStep`, `hammockEndpoint`,
  `HammockReduction`, `HammockReduces`, `ReducedHammock`, `hammockRows`,
  `hammockMapColumns`, and `hammockMapPath`. These already defined notions
  are reused, not copied. Its localization theorem is not invoked or used to
  choose any data. No new dependency on that downstream theorem is introduced.
- Mathlib's ordinary nerve, `Quiver.Path`, `CategoryTheory.Limits.colimit`,
  `colimit.ι`, `colimMap`, natural transformations, isomorphisms and
  `MorphismProperty.IsMultiplicative`.

Edge cases checked before accepting the statement:

- Empty word with x=y gives one constant grid in every degree; with x≠y it
  gives none. There is no map of positions from a nonempty word to the empty
  word. The unique empty-to-word map has only empty fibers, inserting all
  identity columns; both positive and negative empty blocks are covered.
- q=0 has one row and identity vertical arrows. Repeated rows evaluate identity
  maps in the nerve. Skipped rows evaluate the original vertical composites.
- A one-letter word and words with a single repeated sign are retained in G;
  the corresponding repeated sign block is composed in H.
- Entirely identity columns are deleted. Same-direction groupoid arrows can
  compose to identities and then be deleted. Oppositely directed arrows are
  never cancelled by these reduction relations.
- A pair functor can identify endpoints or send nonidentity columns to
  identities (for example the functor to the terminal category). This is why
  its reduced action is explicitly apply-then-reduce. An identity pair functor
  retains a reduced representative. No faithfulness assumption is imposed.
- Independent object and morphism universes u and v are retained; the
  construction uses max u v, without imposing a universe equality.

Searches made through `msearch.py` on 2026-10-16 (UTC dates are retained in
`searches.jsonl`):

- LeanSearch: "The nerves of fixed signed-word zigzag categories form a proper
  diagram with colimit the reduced hammock mapping simplicial set". Eight
  generic nerve/coherent-nerve hits; no proper hammock colimit presentation.
- LeanFinder: "Fixed word hammock diagram nerves form a proper diagram with
  colimit the reduced hammock simplicial set". Eight generic nerve, coherent
  nerve, Segal, and Cech-nerve hits; no matching theorem.
- Loogle: `"hammock"`. Zero hits.
- Mathlib grep: `hammock|Dwyer|zigzag.*colimit`. Four hits about ordinary
  colimit zigzags in `Limits.IsConnected` and `Limits.Final`; none about
  hammock grids. Read `nerve`, `nerveMap`, and `nerveFunctor` signatures and
  the ordinary `zigzag_of_eqvGen_colimitTypeRel` statement: none supplies this
  result or a specialization of it.
- Source-project `rg` for `hammock|Hammock` and `grep -rn` for the item id:
  no source-project declaration of this presentation.
- Side-project `rg` for hammock declarations and for
  `HammockGraphColimitPresentation|hammock_graph_colimit_presentation|GridRepresents`:
  no existing presentation module or theorem. Read the related
  `FixedHammockGraphHomotopyInvariance` module: it gives fixed-word
  bisimplicial grids and a weak equivalence on diagonals, not word-category
  maps, properness, or a colimit/reduction isomorphism. Its Bool-list word
  encoding has a different input type from this module's signed-word adapter.
  Reused the existing reduced-hammock and zigzag notions listed above.

The module was checked using `scompile.py NU
lem-coef-hammock-graph-colimit-presentation <module>` and compiled cleanly
in sandbox and library modes (1.4 s and 1.7 s respectively in the completed
check). There are no warnings, auto-bound variables, or overlong Lean lines.
The declaration list and verbatim main signature in the node record now match
all declarations of the actual module. No statement correction, new node,
dependency repair, or STATEMENT-DISPUTED flag is needed.

The previous report described an older, weaker interface and contained an
obsolete second-reading section. It has been replaced; an independent second
reader must review this actual version before delivery.

## Second reading by NU

I opened the current node, its Dwyer--Kan source place, the two statement
dependencies, and the complete module. The item has two hypotheses: a small
ordinary category `P`, rendered by `{C : Type u} [Category.{v} C]`, and a wide
subcategory `T`, rendered by `(T : MorphismProperty C) [T.IsMultiplicative]`;
the latter supplies identities and closure under composition. The arbitrary
objects `x,y` are the explicit `(x y : C)` binders. No calculus-of-fractions,
two-out-of-three, saturation, Noetherian, finiteness, or characteristic
hypothesis is added.

The conclusion is checked clause by clause. `SignedWord` is the dependency's
small signed-word category, including length zero, and `letters` converts its
signs to the dependency's forward/backward letters in left-to-right order.
`PresentationData.G` is the required functor to simplicial sets, while
`fixedWord` identifies each value with the recorded fixed-word zigzag nerve.
`paths`, `GridRepresents`, and `represents` retain every row arrow, every
vertical arrow, all squares, composites, and identities. `wordMaps` and
`WordImage` give the ordered consecutive fiber compositions, with both empty
positive and empty negative fibers inserting the corresponding identity.
`proper` is exactly the two clauses of `SignedWord.IsProper`, including an
empty intersection. `H`, `simplices`, and `rowOperators` give precisely the
reduced hammock simplices and row deletion/repetition followed by reduction;
`ReducedHammock` excludes identity columns and adjacent equal directions.
`reductionMap`, `reductionFormula`, `reduction`, and `reductionLegs` state the
cocone, terminal-reduct formula, colimit isomorphism, and every canonical leg.

`NaturalFor` quantifies over every target category, wide marked property,
marking-preserving functor, and its explicit preservation hypothesis. It
supplies the target presentation, entrywise simplicial map on fixed-word
diagrams, reduced map on hammocks, and the exact colimit/reduction naturality
equation. Since `g` and `h` are natural transformations of simplicial sets,
their formulas include every nerve row operator. Applying the same clause to
each structure functor gives the source's simplicially varying fixed-object
case; no extra enriched or degreewise hypothesis is introduced.

Edge cases were checked: the empty word and the empty intersection; `q = 0`,
repeated and skipped rows; one-letter and repeated-sign words; all-identity
columns; groupoid composites that become identities; functors collapsing
arrows or endpoints; and independent object and morphism universes `u,v`.
The empty hammock occurs exactly when the endpoints agree, as required.

I searched the side project, slopmaster2 source, Mathlib, and the DAG by the
module/declaration names and by `hammock`, `Dwyer`, `zigzag`, `fixed-word`,
`colimit`, and simplicial-pair naturality. I also ran LeanSearch, LeanFinder,
and Loogle through `msearch.py`. The hits were generic nerve, localization,
and colimit results; none states this fixed-word hammock presentation. The
existing `HammockInfinityLocalization` helpers and the two recorded
dependencies were read and reused. The nearby `SimplicialHammockPair` is an
enriched degreewise framework, not this ordinary fixed-word colimit statement,
so it is not a duplicate and is not added as a dependency.

No mismatch was found. In particular, the apparent omission of a separate
formal simplicial-pair structure is not a weakening: the source clause is
naturality of the ordinary pair construction under each simplicial structure
functor, and the SSet natural transformations already enforce all row
operators. No source-based statement correction, dependency repair, new node,
or `STATEMENT-DISPUTED` flag is needed. The module was recompiled with
`scompile.py`; it is clean with only the permitted postponed theorem proof.
