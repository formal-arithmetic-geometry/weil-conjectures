## Worker report

The module `Sheaf.AlgebraicTopology.BluntSharpJoinEquivalence` states
`SSet.Enhanced.blunt_sharp_join_equivalence`, with `sorry` as its whole proof.
Its two helper definitions contain real data: a monotone ordinal selection and its
application to an existing convolution generator. No other DAG node is stated,
no definition obtains data from a postponed theorem, and no theorem is proved.

The statement is presented as existence of the canonical simplicial map with its
complete component characterization, followed by the assertion about that very
map. This includes the well-definedness asserted in the node's construction of
`c`. It does not take an arbitrary comparison as a hypothesis. There is no choice
of a map from the existence theorem. The component equations determine the map
uniquely because the two pure inclusions and the cylinder map jointly generate
the two endpoint pushouts, in every degree.

Clause-by-clause rendering:

- Small simplicial sets in one fixed universe are `(X Y : SSet.{u})`; there is no
  quasicategory, nonempty or finite hypothesis on either object.
- The sharp join is the existing `orderedJoinFunctor.obj (X, Y)`. Its definition
  in `PushoutJoinSaturation` is Day convolution of terminal augmentations along
  ordered ordinal concatenation. Its generators have exactly the pure `X_n`,
  pure `Y_n`, and mixed `X_a × Y_b`, `a+b+1=n`, normal forms. Kan-extension
  relations restrict the two ordered blocks, including the unique empty block.
- The blunt join is the existing `bluntJoin X Y`: first attach the zero end of
  `(X ⊗ Δ[1]) ⊗ Y` to `X` via `bluntJoinLeftProjection`, then attach the one end
  to `Y` via `bluntJoinRightProjection`. Presheaf colimits are degreewise set
  colimits, so these are exactly the endpoint quotient relations in the node.
- A cylinder simplex is explicitly `((x,t),y)` in the theorem's third conjunct,
  with `x : X.obj (op n)`, `t : Δ[1].obj (op n)` and `y : Y.obj (op n)`.
- `bluntSharpOrdinal n t` sends vertex `i` to vertex `i` of the first block if
  `t(i)=0`, and to vertex `n.len+1+i` of the second block otherwise. Since the
  interval has two vertices and is monotone, these are precisely the initial
  zero block and final one block, in the prescribed order.
- `bluntSharpCylinderSimplex X Y n x t y` first forms the convolution generator
  of the two full `n`-simplices and then applies the sharp join's simplicial
  operator for that selection. Convolution's defining relations identify this
  with the generator of the restrictions of `x` and `y` to those two blocks.
  Thus this formula also handles constant `t`, where one block is empty.
- `∃ c : bluntJoin X Y ⟶ orderedJoinFunctor.obj (X,Y)` asserts that these
  specified values give an actual natural transformation of simplicial sets.
  Its third conjunct evaluates the composite of the two cylinder pushout
  inclusions with `c`, on every simplex, and equates it to that exact formula.
- The first conjunct `bluntJoinBaseIncl X Y ≫ c = orderedJoinInl X Y` identifies
  the entire distinguished left copy. The second conjunct with `pushout.inr`
  and `orderedJoinInr` identifies the entire distinguished right copy.
  These are equations of simplicial maps, not just equations on vertices.
- Every target quasicategory in any containing universe is quantified by
  `∀ (E : SSet.{max u v}) (_ : Quasicategory E)`. The universe variable `v` is
  explicit and arbitrary, including `v=0` for the same-universe case.
  `SSet.uliftFunctor.{v}.map c` canonically puts the small comparison in that
  universe without imposing an equality of universes.
- The actual precomposition simplicial map is
  `(MonoidalClosed.pre (SSet.uliftFunctor.{v}.map c)).app E`. The conclusion
  uses the dependency's `IsFunctorEquivalence`, which supplies a quasi-inverse
  and two `AreNaturallyEquivalent` witnesses. Each witness is an equivalence
  edge of the internal hom with both inverse-triangle witnesses, exactly the
  node's coherent convention, rather than an ordinary homotopy-category test.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsFunctorEquivalence`,
  `AreNaturallyEquivalent`, `IsEquivalenceEdge`, `diagramVertex`; this module
  imports the Mathlib `SSet`, `Quasicategory` and internal-hom constructions.
- `Sheaf.AlgebraicTopology.PushoutJoinSaturation`: `SSet.Enhanced.joinAugmentation`
  and `orderedJoinFunctor`. Its already stated node is added to `stmt_deps` to
  cite the existing sharp join; its theorem is not used as a new assertion.
- `Sheaf.AlgebraicTopology.BluntJoinComparison`: `SSet.Enhanced.bluntJoin`,
  `bluntJoinEndpoint`, both endpoint projections and `bluntJoinBaseIncl`.
  Its already stated node is added to `stmt_deps` to cite the existing blunt
  join. Its right-anodyne comparison theorem is not the theorem stated here.
- `Sheaf.CategoryTheory.JoinSliceRightFibration`: only the existing helper
  definitions `joinGenerator`, `orderedJoinInl`, `orderedJoinInr` are used.
  They construct generators and pure inclusions for the sharp join already
  supplied by `lem-coef-infinity-pushout-join-saturation`. Its slice/fibration
  theorem is not used or asserted. In particular that theorem node is not
  added as a prerequisite: its proof is downstream of the present theorem.
  The helper definitions themselves use only Kan extensions and do not depend
  on that slice theorem or any postponed theorem.
- Proof-only imports: `Sheaf.CategoryTheory.EquivalenceOuterHornFilling`,
  `Sheaf.CategoryTheory.InvertiblePrismExtension`, and Mathlib's
  `AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`
  (the last supplies the internal-hom quasicategory instance). The Mathlib
  simplicial-set leaf is already available through these imports.
- `lem-coef-infinity-cellular-natural-equivalence` has no recorded Lean
  statement yet (`status: unsplit`), so there is no corresponding proof import.
  It remains a named dependency in the unchanged proof and in the docstring;
  it is not needed to elaborate this theorem's signature.

Edge cases checked before writing: either factor empty, both factors empty,
constant zero and constant one interval maps in every degree, degree zero,
non-quasicategorical factors, infinite factors, and same or larger target
universes. Endpoint restrictions still determine `c` when a cylinder is empty.
In degree zero the ordinal selection chooses just one pure vertex, agreeing
with the absence of mixed zero-simplices. No inhabitedness, finite dimension,
finite set of simplices, or quasicategory structure on the factors is assumed.

Searches for existing declarations:

- `msearch.py ... leanfinder "The blunt to sharp join comparison of simplicial
  sets induces an equivalence of functor quasicategories"`: eight results,
  headed by `SSet.Truncated.HomotopyCategory.functorEquiv`,
  `SSet.hoFunctor.unitHomEquiv`, and `SSet.hoFunctor.terminalIso`; the others
  concern the nerve adjunction and the quasicategory bicategory. None states
  the arbitrary blunt-to-sharp comparison.
- `msearch.py ... loogle "SSet.join, SSet.Join, SSet.bluntJoin"`: zero hits;
  Loogle reports unknown identifier `SSet.join`.
- `msearch.py ... grep "blunt|sharpJoin|bluntJoin|def join" AlgebraicTopology`:
  zero Mathlib hits.
- Direct ripgrep of Mathlib and upstream `WeilConjectures` for
  `blunt|sharpjoin|bluntjoin|simplicial.*join|join.*simplicial` found no
  simplicial join construction or this comparison theorem. Ordinary-category
  joins and unrelated adjoint references do not supply this statement.
- Direct ripgrep of `lean/Sheaf` found the existing blunt join in
  `BluntJoinComparison`, ordered join in `PushoutJoinSaturation`, and its
  generator/pure inclusions in `JoinSliceRightFibration`. These are reused.
  `ConeMonoRightAnodyne` also exposes an equivalent convolution presentation;
  the delivery imports the already used `orderedJoinFunctor` presentation.
  `SliceArrowEquivalence` names this DAG theorem only in its proof docstring.
- Direct upstream search for the item id and direct searches for the three
  new declaration names found no existing declaration.

Sources opened online: Kerodon [01HR](https://kerodon.net/tag/01HR),
[01HV](https://kerodon.net/tag/01HV), and [05YH](https://kerodon.net/tag/05YH).
Their endpoint pushout, comparison and functor-category equivalence agree with
this statement. There is no statement correction or mathematical dispute.

Validation: prescribed `scompile.py Q23` compiled the sandbox file and its
library module cleanly under the standard per-file limit. The only postponed
proof in the delivery is `SSet.Enhanced.blunt_sharp_join_equivalence`.

## Second reading by Q23

I independently read the node, its Kerodon source places (Notation the project server,
Theorem the project server, and Example the project server), the dependency records, and
`Sheaf/AlgebraicTopology/BluntSharpJoinEquivalence.lean`.

The node's objects and hypotheses match the file as follows. The two arbitrary
small simplicial sets in one fixed universe are `(X Y : SSet.{u})`; the file
adds no finiteness, nonemptiness, quasicategory, characteristic, or other
structure hypothesis. The sharp join is
`orderedJoinFunctor.obj (X, Y)`, supplied by
`lem-coef-infinity-pushout-join-saturation`, and the blunt join is
`bluntJoin X Y`, the two endpoint pushouts supplied by
`lem-coef-infinity-blunt-join-comparison`. The canonical comparison is rendered
by the existential `c : bluntJoin X Y ⟶ orderedJoinFunctor.obj (X, Y)` together
with its three defining restrictions: the left pure inclusion is
`bluntJoinBaseIncl X Y ≫ c = orderedJoinInl X Y`, the right pure inclusion is
`pushout.inr _ (bluntJoinRightProjection X Y) ≫ c = orderedJoinInr X Y`, and
the cylinder value is the displayed universal equation for
`bluntSharpCylinderSimplex`. The helper `bluntSharpOrdinal` sends the initial
zero block to the first ordered block and the final one block to the second;
`bluntSharpCylinderSimplex` applies that operator to the existing convolution
generator, exactly rendering the node's restriction-and-concatenation clause.
Finally, the target is quantified as every `E : SSet.{max u v}` with
`Quasicategory E`, and the conclusion is precisely
`IsFunctorEquivalence ((MonoidalClosed.pre (SSet.uliftFunctor.{v}.map c)).app E)`.
The explicit `v` permits both equal and larger target universes.

I found no mismatch between these clauses and the node. The existential is the
Lean form of the node's canonical construction: its three equations expose
the defining pushout restrictions rather than choosing an unrelated map. The
source's statement that precomposition is an equivalence is rendered by the
recorded `IsFunctorEquivalence`, whose definition includes a quasi-inverse and
both coherent inverse-triangle witnesses. No node statement, hypothesis, or
quantifier was changed.

Edge cases checked again were `X = ∅`, `Y = ∅`, both empty, constant zero and
constant one interval coordinates, degree `n = 0`, and `m = 0` or `n = 0` in
the standard-simplex proof. The endpoint equations reduce to the pure maps in
the constant cases; empty factors reduce both joins and `c` to the identity.
The universe `v = 0` and larger `v` are both covered. There is no scheme, ring,
or characteristic parameter in this simplicial statement, so those edge cases
are inapplicable rather than silently excluded.

For the independent one-definition search I reran ripgrep over Mathlib,
`WeilConjectures/`, and `lean/Sheaf/` for `bluntJoin`, `sharpJoin`, and
`blunt_sharp_join_equivalence`, and reran LeanSearch, Loogle, and LeanFinder
with queries for a fat/blunt-to-sharp simplicial join comparison into a
quasicategory. The only local matches are the already recorded blunt join,
ordered join, and generator/pure-inclusion declarations; no declaration states
this comparison. The cited `JoinSliceRightFibration` module is used only for
those existing sharp-join helper definitions and does not duplicate the
theorem. The node's three statement dependencies are therefore sufficient.

Independent search details (2026-10-17): LeanFinder query
`Exponentiation into a quasicategory sends the fat join comparison to an
equivalence of functor simplicial sets` returned eight hits concerning the
homotopy-category product comparison and ordinary nerve adjunction; none has
the required comparison in its signature. Loogle query
`SSet.Quasicategory, "join"` succeeded with zero hits. LeanSearch query
`The fat join comparison of simplicial sets is a categorical equivalence`
returned eight hits, including `CategoryTheory.Join.isEquivalenceMapPair` and
`mapPairEquiv`; I opened their signatures in Mathlib, which concern equivalences
of ordinary-category joins, not blunt simplicial joins. Direct ripgrep found
only the existing project blunt-join definitions and no upstream comparison.

The prescribed `scompile.py Q23` run was clean for both the sandbox and library
compilations, with no diagnostics beyond the intentional theorem `sorry`.
No repair was needed; the worker module and node copy are unchanged.

## Maintainer review fix (2026-10-17)

The delivered module publicly imported `Sheaf.CategoryTheory.JoinSliceRightFibration` for
`joinGenerator`, `orderedJoinInl` and `orderedJoinInr`. That module belongs to
`lem-coef-infinity-slice-right-fibration`, which reaches this item in the DAG
(slice-right-fibration -> anodyne-cocones -> pinch-comparison -> slice-arrow-equivalence ->
this item), and it also imports `AnodyneCocones` and so `RightPinchComparison`. The proof-plan
imports RightPinchComparison -> SliceArrowEquivalence -> BluntSharpJoinEquivalence would then
close an import cycle. Also, the statement depended on declarations of a node that is not
in, and cannot be in, its `stmt_deps`. The fix drops that import and imports
`PushoutJoinSaturation` (the recorded sharp join) directly. It writes the convolution generator as the
Kan-extension unit that `joinGenerator` abbreviates. The two pure-summand clauses become
elementwise equations with the generator of `(x, e)`, resp. `(e, y)`, for every simplex `e`
of the empty ordinal. That type is the limit of an empty diagram and has exactly one element.
A scratch check compiled the fixed module with the old helpers and proved: the empty-ordinal value is a
subsingleton; each new pure clause is equivalent to the delivered `orderedJoinInl` /
`orderedJoinInr` equation; and the cylinder formula is unchanged (`rfl`). So the statement is
the same. The proof-plan import of the now-recorded
`Sheaf.AlgebraicTopology.CellularNaturalEquivalence` was added. Docstring step 4 now reads `h=kf` as in the node.
