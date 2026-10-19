## Worker report

The module `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus` states
`SSet.Marked.Over.relative_marked_anodyne_calculus`, with its sole proof `sorry`.
It defines the canonical `SSet.Marked.cartesianNatural`,
`SSet.Marked.cartesianNaturalOver`, and `SSet.Marked.Over.mapSharpToFlat`.
The definitions contain real data and elementary structure-law proofs only.
No mathematical theorem is proved. No new node, dependency replacement, or statement
correction is needed; the item changes only in `lean`.

The incoming stale-assignment diagnosis confused stage 1 with stage 2. N7's reviewed
completion is a DAG split, not a Lean statement: the current node has no `lean`
record, and the stage-2 queue still lists the item. This delivery states that split.

The source was opened at https://www.math.ias.edu/~lurie/papers/HTT.pdf:
Remark the project server (printed p. 151), Remark the project server (p. 154),
Lemma the project server (p. 157), Proposition the project server (p. 121), and
Remark the project server (p. 126). The last remark supports the local-to-global
reflection argument in proof steps 3--5. The Joyal conclusion is the node's
Proposition the project server/Corollary the project server consequence, rendered using the existing
normalized Joyal model interface. The theorem docstring carries all sixteen
DAG proof steps and every step's explicit dependency names.

Clause and hypothesis matching:

1. All input simplicial sets lie in arbitrary `SSet.{u}`; `S` has no
   quasicategory or nonemptiness hypothesis. The existing `SSet.Marked` has
   a set of marked edges containing the degeneracies, and its maps preserve
   markings. The existing `Over S` is literally `CategoryTheory.Over (sharp S)`.
   `Over.relativeFibration false q` is an inner fibration and supplies a
   final-horn-cartesian lift of every base edge with prescribed target. Its
   definition has no quasicategory assumption on source or base. It uses
   `Enhanced.IsCartesianEdge`, the dependency's final-horn predicate for all
   dimensions at least two. Thus the quasicategory-only binder of the older
   `Enhanced.cartesianFibration` is not inadvertently imposed.
2. `Over.mapFlat U V` and `Over.mapSharp U V` are the existing simplicial
   objects whose degree-n elements are marked maps over `S` from
   `U × (Δ[n])^flat` and `U × (Δ[n])^sharp`. Their `productLeft` base map
   is the first projection followed by `U.hom`; it ignores the parameter.
   Their simplicial operators use precomposition by the simplex maps.
3. `cartesianNatural q` has underlying simplicial set exactly `Z` and marks
   the final-horn-cartesian edges together with the explicitly degenerate
   edges. Its canonical map to the sharp base is `cartesianNaturalOver q`.
   The first theorem conjunct says that whenever `relativeFibration false q`
   holds, this object is `Over.IsNaturallyFibrant false`. Unfolding that
   existing predicate identifies its marking with exactly the cartesian
   edges, so the included degeneracies do not enlarge the natural marking.
   This conjunct supplies the natural marked object for every cartesian
   fibration, rather than assuming its marked total space as extra input.
4. The second conjunct, `markedAnodyne.rlp V.hom ↔ IsNaturallyFibrant false V`,
   is the right-lifting iff naturally marked cartesian-fibration criterion.
   `V` ranges over every marked object over `S`. The lifting property is
   Mathlib's right-lifting class, with arbitrary commutative squares.
5. The third conjunct applies to every marked `U` and naturally marked
   cartesian `Z` over `S`. It asserts `Quasicategory (mapFlat U Z)` and
   `KanComplex (mapSharp U Z)`. The concrete `mapSharpToFlat` precomposes a
   sharp-parameter map with the identity from the flat parameter marking.
   Its component is injective, and its image is exactly the degree-n subset
   `Enhanced.core (mapFlat U Z)`. Injectivity and this exact image, for every
   degree, identify the sharp mapping object with the core by the canonical
   inclusion, rather than an arbitrary isomorphism.
6. In the fourth conjunct `j : U ⟶ V` is an actual map over `S`, and
   `Marked.cof j.left` means injection on underlying simplices in every
   degree. With exactly the naturally marked cartesian target hypothesis,
   `modelCategoryQuillen.J.rlp (mapSharpPre j Z)` is the Kan fibration
   conclusion. If `markedAnodyne j.left`, the conclusion is
   `modelCategoryQuillen.I.rlp`, the trivial Kan fibration condition.
   `I` consists of all boundary inclusions including dimension zero;
   `J` consists of all positive-dimensional horn inclusions. The phrase
   marked anodyne over `S` is represented by applying `markedAnodyne` to
   `j.left`, not by assuming that arbitrary pullbacks of this class are
   anodyne. No such stability assertion occurs.
7. The fifth conjunct quantifies over every `T`, every map `a : T ⟶ S`,
   and every naturally marked cartesian `Z`. The existing `pullObject a Z`
   has underlying pullback `T ×_S Z`, map `pullback.fst`, and marking pulled
   back by `pullback.snd`. It is naturally marked cartesian by the first
   part of this conjunct. The final-horn edge condition is furthermore
   equivalent in both directions to the condition for its image under
   `pullback.snd`, for every edge `e : Δ[1] ⟶ pullback a Z.hom.val`.
   This is the asserted reflection as well as preservation, and identifies
   the pulled-back marking with the natural marking.
8. Only the sixth conjunct assumes `Quasicategory S`. It concludes that
   `Z.left.underlying` is a quasicategory and that `Z.hom.val` is a fibration
   in every Joyal model `M`. The two normalizations on `M` are exactly the
   cofibration and `hFun` weak-equivalence formulas in
   `SSet.exists_joyal_model_structure`; they select the named Joyal model,
   not an extra geometric hypothesis or a relative marked model.
   Its existence is already the recorded Joyal dependency. The weak
   equivalence tests range over `SSet.{max u v}` with independent `v` and
   use `hoFunctor.map` on restriction after `uliftFunctor.{v,u}`.
9. Universe relativity is literal polymorphism in arbitrary `u`; the Joyal
   tests also allow arbitrary enlargement `v`. No equality or lower bound
   between independent input universes is imposed, and all helper data
   and relative mapping simplices stay in the input universe.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, `Hom`, `flat`, `sharp`, `product`, `productMap`,
  `flatSimplex`, `sharpSimplex`, and `cof`; its theorem records the
  full point-model and internal-Hom conventions.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`:
  `SSet.Marked.markedAnodyne`, `flatToMarked`, and
  `marked_anodyne_lifting_calculus` (the generators, saturation,
  small generation, product and absolute mapping assertions).
- `Sheaf.CategoryTheory.InfinityFibrations`:
  `SSet.Enhanced.IsCartesianEdge` (unrestricted final-horn predicate),
  together with Mathlib `SSet.InnerFibration`. The recorded
  `cartesianFibration` was read: its quasicategory assumptions make it
  inappropriate for the arbitrary-base clause, so the already existing
  general predicate below is used, with the same edge definition.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`; Mathlib `SSet.hoFunctor`,
  `SSet.uliftFunctor`, `MonoidalClosed.pre`, and `ModelCategory`.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`:
  `SSet.Marked.Over`, `Over.productLeft`, `mapFlat`, `mapSharp`,
  `mapSharpPre`, `relativeFibration`, `IsDistinguishedEdge`,
  `IsNaturallyFibrant`, and `pullObject`. These are concrete definitions
  already provided by that module; none is chosen from its model theorem.
  Reusing them prevents a second definition of the slice, mapping objects,
  or arbitrary-base fibration. This module's node has the present item as
  a proof dependency; the import of the present module back into it must
  therefore be omitted under stages/2-statements.md section 3 rule 7's
  import-cycle exception. No DAG edge to the downstream theorem was added,
  and the present proof never invokes that theorem. This is a source
  organization issue, not a circular mathematical assumption.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.core` and `IsEquivalenceEdge`. Existing Mathlib
  `modelCategoryQuillen.I` and `J` render boundary and horn lifting.

Every currently recorded proof dependency module is imported explicitly,
without `public` where used only in the proof plan. In addition to the
statement-dependency modules above these are EnhancedDiagramsCones,
EnhancedFunctorConeCalculus, EquivalenceOuterHornFilling,
InnerFibrationEquivalenceOuterHornLift, RightFibrationSpaceFiber,
JoyalQuasicategoryCharacterizations, KanQuillenRightProper,
MarkedTriangleCancellation and HomotopyCategoryTriangleCalculus (the last
added by the maintainer's review: `lem-coef-homotopy-category-triangle-calculus`
is stated as `Sheaf.AlgebraicTopology.HomotopyCategoryTriangleCalculus` on the
delivery base). The proof node
`lem-coef-infinity-cocartesian-composition-initiality` has no recorded
Lean module and therefore has no available module to import yet.

Edge cases checked before writing:

- Empty `S` forces every object over it to have empty underlying set;
  no nonemptiness binder is present. Empty `Z` over a nonempty base is
  allowed, with lift existence vacuous at its absent targets.
- Empty `U` gives the terminal mapping simplicial set. Mapping objects
  may also be empty; both quasicategory and Kan conditions allow that.
- `S = Δ[0]` recovers the absolute naturally marked/quasicategory case.
  A non-quasicategory base, such as `Λ[2,1]`, is allowed throughout the
  first five conjuncts; no total-space quasicategory is asserted there.
- The final-horn edge definition starts at `n = 2`, but cartesian lift
  existence covers the one-horn case. Restriction's `I.rlp` includes
  `n = 0`, hence vertex extension for anodyne `j`; it is not merely a
  positive-dimensional boundary condition.
- Identity, constant, non-surjective and degenerate base-change maps
  are included; no global marking is imposed on unselected base edges.
- `u = 0`, `v = 0`, and arbitrary larger testing universes are allowed.

Searches (raw msearch outputs are retained in `searches.jsonl`):

- LeanFinder query: “Relative marked anodyne lifting criterion cartesian
  fibration sharp mapping complex Kan fibration”. Eight hits, all generic
  horn-lifting/Kan-Quillen or abstract model-category lemmas; no match.
- LeanSearch query: “Relative sharp mapping simplicial sets into a
  cartesian fibration are Kan and restrictions are Kan fibrations”.
  Eight hits, including RelativeMorphism.map, KanComplex, generic model
  fibrations and ordinary fibered categories; no relative marked theorem.
- Loogle query: `"SSet", "Cartesian"`. Zero hits (run twice).
- msearch grep: `relativeMarked|relative_marked|cartesianFibration|IsCartesianEdge`
  in Mathlib/AlgebraicTopology. Zero hits (run twice).
- `rg` on WeilConjectures for that same pattern and for this node id:
  no hits. Mathlib and upstream-name-index searches for
  `relative_marked_anodyne_calculus|cartesianNatural|mapSharpToFlat`:
  no matching relative declaration.
- `rg` on `lean/Sheaf` found the already recorded InfinityFibrations and
  relative-model primitives, plus quasicategory-only consumers. The
  absolute `SSet.Marked.mapSharpToFlat` was found and read; it has absolute
  source and target, whereas the new `Over.mapSharpToFlat` preserves the
  base map and is constructed by the same canonical precomposition.
  No full relative lifting/mapping/base-change/Joyal theorem exists there.

No STATEMENT-DISPUTED fault was found. The earlier stage-1 completion is
not grounds to abandon this still-unstated stage-2 item.

Validation: scompile.py compiled the module through the server overlay
at both its sandbox and library module paths, cleanly, within the
per-file 60-second limit. The prescribed deliver2.py dry run is the final
check; no delivery is pushed by this worker.

## Second reading by Q122

I independently opened the base DAG node, the delivered node and module, all four
statement-dependency nodes and their source declarations, and the concrete slice
constructions in `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`. There are
no new nodes, dependency replacement modules, or `statement_change` in this
delivery. No repair note exists for this item. The base node has no Lean binding.

Source check: I downloaded and read [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf)
in `scratchpad/HTT-second-reader.pdf`, with extracted text alongside it. I read
Definitions the project server and the project server, Remark the project server, Proposition the project server,
Proposition the project server, Remark the project server, Corollary the project server, Definition the project server,
Proposition the project server, Definition the project server, Remarks the project server and the project server,
and Lemma the project server, including the surrounding hypotheses. This node's source
is HTT, not a Stacks tag. Cartesian fibrations in these source passages have
arbitrary simplicial bases; the quasicategory restriction belongs only to the
Joyal conclusion. The lifting criterion uses the sharp marking of the base.
The reflection assertion requires the existence of global cartesian lifts;
Remark the project server supplies the local-to-global reduction, as the node's proof
spells out. No relative model structure is needed for these conclusions.

My object/hypothesis/conclusion checklist, matched against the Lean:

1. **Small simplicial sets and arbitrary base.** `universe u v` and
   `(S : SSet.{u})` introduce the base. Every total space, marked object,
   map and base-change object is in `u`. There is no `Quasicategory S`
   hypothesis in the first five conjuncts. Verdict: exact.
2. **Marked objects, products, maps and markings.** The first dependency's
   `SSet.Marked` has `underlying`, a set `marking` of edges, and `degenerate`.
   Its `Hom` is a simplicial map preserving marked edges; `flat`, `sharp`
   and `product` give degeneracy-only, all-edge and coordinatewise markings.
   I read these definitions, not just the main model theorem. The existing
   `Over S` is `CategoryTheory.Over (sharp S)`. Verdict: the same objects,
   with no model structure or extra instance assumed.
3. **Cartesian edges and cartesian fibrations over any base.** The actual
   `Enhanced.IsCartesianEdge q e` quantifies over final horns in every
   dimension `n` with `2 ≤ n`, fixes their final edge and base simplex,
   and requests a filler with both exact equations. Existing
   `Over.relativeFibration false q` is `InnerFibration q` together with
   a cartesian lift of every base edge at every prescribed target (`δ 0`).
   Its signatures do not require either space to be a quasicategory.
   The older `Enhanced.cartesianFibration` does require quasicategory
   instances and is correctly not used. Verdict: exact arbitrary-base notion.
4. **The natural marking is exactly the cartesian edges.**
   `cartesianNatural q` has underlying object `Z` and explicitly marks
   cartesian edges or degeneracies; `cartesianNaturalOver q` retains `q`.
   The first conjunct proves `IsNaturallyFibrant false` for this construction
   under exactly `relativeFibration false q`. Unfolding the existing
   `IsNaturallyFibrant` says both that `q` is cartesian and that membership
   in this marking is equivalent to `IsCartesianEdge`. Thus the theorem
   includes the degeneracy assertion needed to construct `Z^natural`,
   without asking the caller to supply another marked space. Verdict: exact.
5. **Relative flat and sharp mapping objects and their simplicial operators.**
   Existing `mapFlat U V` and `mapSharp U V` are the respective Yoneda Hom
   simplicial sets on `flatSimplex`/`sharpSimplex` followed by `productLeft U`.
   That functor's object map uses `fst ≫ U.hom.val`, ignoring the parameter,
   and its arrow map is `productMap (𝟙 U.left)`. This gives the node's Hom
   over `S` in every degree, with precomposition as the operators.
   Verdict: exact, using the already recorded constructions.
6. **Relative lifting recognition in both directions.** The second conjunct
   is `∀ V : Over S, markedAnodyne.rlp V.hom ↔ IsNaturallyFibrant false V`.
   I read `markedAnodyne`, its four generator families and weak saturation,
   and Mathlib's `MorphismProperty.rlp`. The latter quantifies over all
   marked left maps in the class and all lifting squares. The right side
   gives both cartesian fibrancy and exactly its natural marking, not merely
   a subset of cartesian markings. Verdict: both directions and all objects
   are present; no assertion of pullback stability of anodyne maps occurs.
7. **Flat mapping quasicategory and sharp core/Kan complex.** The third
   conjunct quantifies over arbitrary `U Z : Over S`, assuming only
   `IsNaturallyFibrant false Z`. It gives `Quasicategory (mapFlat U Z)`,
   `KanComplex (mapSharp U Z)`, and in every degree injectivity of the
   canonical `mapSharpToFlat` with image exactly `Enhanced.core`.
   I read `core`: every edge of a retained simplex must have two inverse
   triangles. The new map precomposes with the identity from the flat to
   sharp parameter, keeping the base equation. This is the specified core
   identification, not an arbitrary equivalence or inclusion. Verdict: exact.
8. **Sharp restriction along monomorphisms and marked-anodyne maps.** The
   fourth conjunct uses `j : U ⟶ V` over `S`, a naturally marked cartesian
   target `Z`, and `Marked.cof j.left`, which is precisely degreewise
   injectivity of the underlying map. `mapSharpPre j Z` is precomposition
   by that over-base map. `J.rlp` gives Kan fibrancy of restriction and
   `markedAnodyne j.left → I.rlp ...` gives trivial Kan fibrancy.
   Mathlib's `J` includes every positive-dimensional horn; its `I` includes
   every boundary starting at zero. Verdict: exact hypotheses and both
   conclusions, with the same restriction map.
9. **Arbitrary base change, including reflection of edges and marking.**
   The fifth conjunct quantifies over every `T : SSet.{u}`, `a : T ⟶ S`
   and naturally marked cartesian `Z`. I read `pullObject`: underlying
   `pullback a Z.hom.val`, structure map `pullback.fst`, marking pulled
   back by `pullback.snd`. The conclusion gives natural fibrancy of this
   very object and, for every edge `e`, the iff between cartesianness for
   `pullback.fst` and cartesianness of `e ≫ pullback.snd` for `Z.hom.val`.
   Verdict: preservation, reflection, and the natural pulled-back marking
   are all explicit, with no assumption on `a` or on `T`.
10. **Joyal clause and its sole extra geometric hypothesis.** The sixth
    conjunct assumes `IsNaturallyFibrant false Z` and `Quasicategory S`.
    It concludes `Quasicategory Z.left.underlying` and fibrancy of
    `Z.hom.val` in every `ModelCategory SSet.{u}` whose cofibrations and
    weak equivalences have the exact formulas of the recorded
    `exists_joyal_model_structure`. I compared both normalizations verbatim
    with that declaration: the weak-equivalence tests use `hoFunctor`,
    restriction by `MonoidalClosed.pre`, and `uliftFunctor.{v,u}` into
    `SSet.{max u v}`. The existing theorem supplies such a model, so these
    are normalization conditions on the Joyal model, not a missing
    existence assertion or an extra geometric hypothesis. Verdict: exact.

Edge cases: empty base and empty total spaces are permitted, with lift
existence vacuous at absent targets. Empty mapping source gives one mapping
simplex per degree. There is no nonemptiness assumption on mapping spaces
or fibers. The terminal base recovers the absolute case. The identity on a
non-quasicategory base remains covered, without concluding that its total
space is a quasicategory. The test base `Λ[2,1]` has two composable edges
and no filling two-simplex, so it really tests this distinction. The final
horn predicate begins at dimension two, while the fibration definition
supplies dimension-one target lifts. Trivial Kan fibrancy includes the
zero-dimensional boundary. Identity, constant, degenerate and non-surjective
base-change maps are all allowed. There are no schemes, coefficient rings,
characteristic assumptions, or additive zero objects in this item.
The arbitrary universe `u` includes `0`; `v` is independent, and `max u v`
only enlarges Joyal testing objects. No variable or universe is unbound.

Independent duplicate searches (recorded by msearch in `searches.jsonl`):

- LeanFinder: “Marked simplicial sets over a base Cartesian edges relative
  function complexes restriction fibrations”. Eight hits: the ordinary
  `SSet.RelativeMorphism` API, Kan-Quillen `I`/`J`, and their lifting lemmas;
  none is the marked relative calculus.
- LeanSearch: “For a marked simplicial set over any base, right lifting
  against marked anodyne inclusions characterizes naturally marked Cartesian
  fibrations”. Eight generic lifting/Kan-fibration hits, plus ordinary
  fibered categories; no match.
- Loogle: `"SSet", "marked"`: zero hits.
- `rg` on Mathlib, the upstream `WeilConjectures/`, `dag/lean_names_upstream.json`
  and this project's `lean/Sheaf/`, using `cartesianNatural`, `mapSharpToFlat`,
  `relative_marked_anodyne`, and combinations of marked/relative and
  cartesian/natural: no existing full theorem or natural-marking constructor.
  I also searched Mathlib's quasicategory and upstream category-theory trees
  using marked/cartesian terminology. The absolute `Marked.mapSharpToFlat`
  exists and was read: its objects are not over a base; the new
  `Over.mapSharpToFlat` supplies the base-preserving map. The existing
  relative primitives from `MarkedRelativeCartesianModel` are reused.

Definition/data/docstring audit: the three new helpers have actual data;
only elementary marking/base/naturality structure laws are proved. The sole
postponed mathematical theorem is the named item theorem. Its docstring
contains all sixteen numbered DAG proof steps and their dependency names.
Each declaration has the source and blueprint tag. All presently recorded
proof modules are imported (the maintainer's review added the missing
HomotopyCategoryTriangleCalculus import); the proof node without a Lean module
remains as documented by the worker. The downstream model theorem is not used, and
adding this module as its proof import would close the existing import cycle,
so the rule-7 exception applies. No new notion, private copy, dependency
repair, extra hypothesis or source-based node correction was needed.

Mismatches repaired: the theorem docstring said “first four clauses” although
its first five conjuncts allow arbitrary bases; I changed “four” to “five”.
The worker report incorrectly offered `Λ[2,0]` as a non-quasicategory base;
that outer two-horn is the nerve of a fork category. I changed this example
to the inner two-horn `Λ[2,1]`. No Lean signature or mathematical node field
needed changing. The worker report remains in place.

Validation: the required `scompile.py` compiled the delivered module at both
its sandbox and library paths, cleanly (1.3 s and 1.5 s respectively), with
no errors or warnings. I checked that `lean.statement` is verbatim the
signature, every line is at most 100 characters, only the `lean` field differs
from the base node, and the module has exactly one postponed theorem.

## Maintainer review correction

Independent review (cc review service) at 8c9d4e15a9bb: the statement was read
against the node, HTT and every dependency declaration and is unchanged. One
mechanical correction: `lem-coef-homotopy-category-triangle-calculus` (a proof
dependency, steps 14-15) already had its module
`Sheaf.AlgebraicTopology.HomotopyCategoryTriangleCalculus` on the delivery base,
so stages/2-statements.md section 3 rule 7 requires its non-public import. It was
added; it closes no import cycle (that module imports only EnhancedDiagramsCones
and Mathlib). The corrected module compiles cleanly through nt_compile.py.
