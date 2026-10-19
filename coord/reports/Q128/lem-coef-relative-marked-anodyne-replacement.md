## Worker report

The module `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneReplacement` states
`SSet.Marked.Over.relative_marked_anodyne_replacement`, with `sorry` as its only theorem proof.
It also defines the auxiliary family `SSet.Marked.Over.anodyneGeneratorsOver` by the actual
formula `fun _ _ i ↦ anodyneGenerators true i.left`. This merely equips the existing generating
maps with maps to the fixed base; it does not duplicate the marked-anodyne class or introduce
an independent notion. No new nodes, dependency repairs or statement corrections were needed.
Only the item's `lean` field changes.

Source read: HTT, downloaded to sandbox `HTT.pdf` and converted to `HTT.txt`, pp. 147–151,
Definition the project server, Remark the project server, Proposition the project server, Definition the project server and Remark the project server;
p. 155, Remark the project server; Corollary the project server and its proof. The latter explicitly chooses marked
anodyne fibrant replacements. Definition the project server supplies the four weak-saturation families;
Remark the project server supplies small generation; Remark the project server identifies the right lifting objects
over a fully marked arbitrary base with exactly naturally marked Cartesian fibrations.
Remark the project server supplies the Cartesian-equivalence conclusion. The module docstring reproduces
all five proof steps of the DAG, including slice smallness, cellularity, the relative lifting
criterion, the sharp boundary restriction test and underlying monomorphisms.

Hypotheses and clauses matched with Lean:

- Every input universe is represented by the explicitly declared `universe u`. The only
  parameter is `(S : SSet.{u})`. There is no `Quasicategory S` or total-space hypothesis.
- A marked object over S is the recorded `SSet.Marked.Over S`, definitionally the existing
  `CategoryTheory.Over (SSet.Marked.sharp S)`. Its morphisms preserve markings and commute with
  the base maps. Thus the claimed replacement remains over S without a separate equation.
- Relative marked anodyne means `markedAnodyne i.left`. The existing `markedAnodyne` is exactly
  `markedSaturation (anodyneGenerators false)`, whose definition is the least closure under
  pushouts, small transfinite compositions and arrow retracts of the four specified families.
  The theorem uses this class directly and does not assume pullback stability.
- Functorial replacement is the existential pair `(R : Over S ⥤ Over S)` and
  `(η : 𝟭 (Over S) ⟶ R)`. The universal `∀ X : Over S` includes every marked input. Naturality
  of η supplies compatibility with every marked map over S, including identities/composites.
- The map `X → Z^natural` is `η.app X`, with `markedAnodyne (η.app X).left`.
  `IsNaturallyFibrant false (R.obj X)` asserts both `relativeFibration false` of the underlying
  map and, for every edge, membership in the marking iff it is Cartesian. The former means
  `InnerFibration` plus a Cartesian lift of each base edge with prescribed target. The latter
  uses `Enhanced.IsCartesianEdge`, the final-outer-horn condition in dimension at least two.
  This preserves exactly the arbitrary-base definitions, rather than the quasicategory-only API.
- For every marked map `i` over S, the implication
  `markedAnodyne i.left → cof i ∧ weak false i` asserts the trivial-cofibration conclusion.
  The recorded relative model has precisely `cof` as its cofibrations and `weak false` as its
  weak equivalences, so their conjunction is exactly its trivial-cofibration class. No choice
  of model witness and no model-existence assumption are required.
- The replacement's objects belong to the original `Over S`, so their simplicial sets and
  markings have universe u. The additional cellular clause
  `transfiniteCompositions.{u} (coproducts.{u} (anodyneGeneratorsOver S)).pushouts (η.app X)`
  renders the node's small-object construction clause: a u-small continuous transfinite chain
  of pushouts of u-small coproducts of the four relative generators, with only countable Kan
  complexes in family (iv). Its intermediate objects are also in `Over S`. This makes the
  construction bound explicit; it does not merely assert an abstract lifting-class replacement.

Dependency declarations used, signatures and docstrings read in the recorded source files:

- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`: `SSet.Marked.Over`,
  `SSet.Marked.Over.relativeFibration`, `SSet.Marked.Over.IsNaturallyFibrant`,
  `SSet.Marked.Over.cof`, `SSet.Marked.Over.weak`,
  `SSet.Marked.Over.RelativeCartesianModelStatement`, and
  `SSet.Marked.Over.marked_relative_cartesian_model`. Its structure fields normalize cofibrations
  and weak equivalences; its natural-fibrancy definition states exact edge marking.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`:
  `SSet.Marked.anodyneGenerators`, `SSet.Marked.markedSaturation`,
  `SSet.Marked.markedAnodyne`, and `SSet.Marked.marked_anodyne_lifting_calculus`.
  The Boolean `true` restricts only the fourth family to countable Kan complexes; the theorem
  identifies the resulting saturation with the unrestricted marked-anodyne class.
- `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus`:
  `SSet.Marked.Over.relative_marked_anodyne_calculus`. Its second clause is the required
  arbitrary-base lifting iff natural-fibrancy criterion; the mapping restriction clauses give
  the same sharp complexes used in the proof. No interface repair is needed.
- Proof-only import `Sheaf.AlgebraicTopology.KanQuillenRightProper` supplies
  `SSet.KanQuillen.right_proper_kan_quillen`, including the boundary criterion in dimension zero.
- Proof-only import `Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument`
  supplies the Mathlib-match declarations for `lem-coef-small-object-cell-factorization`:
  `CategoryTheory.SmallObject.functorialFactorizationData` (460–469),
  `relativeCellComplexιObj` (318–330), `rlp_πObj` (412), and
  `llp_rlp_of_isCardinalForSmallObjectArgument` (508–515). Their complete signatures and the
  smallness class at lines 76–88 were read. The cellular clause also uses Mathlib's
  `MorphismProperty.transfiniteCompositions`, `coproducts` and `pushouts` directly.

Edge cases checked:

- Empty base: every object over it has empty underlying simplicial set; the quantifiers still
  include the empty object and its identity cellular map, and no nonempty condition is imposed.
- Point base: natural fibrancy specializes to a quasicategory with exactly its equivalences
  marked, consistent with the absolute lifting calculus.
- Non-quasicategory base, e.g. the inner two-horn: no quasicategory instance is requested, and
  the horn-based relative definitions remain meaningful. Empty total spaces over any base are
  included; the prescribed-target lift condition is then vacuous as it should be.
- Marking-only generators have identity underlying maps, so relative cofibrancy does not
  incorrectly require strict inclusion of underlying simplices or equality of markings.
- The final-horn generator includes dimension one (prescribed-target edge lifts). The relative
  Cartesian-edge condition starts at dimension two, exactly as required.
- The boundary restriction proof includes n = 0 and the empty boundary, which supplies
  extension of mapping vertices. There is no nonempty/finiteness restriction on inputs.
- The cellular expression fixes both coproduct and chain universes at u; it does not quantify
  over a smaller independent universe or impose an equality of unrelated universes.

Searches executed via `msearch.py Q128 lem-coef-relative-marked-anodyne-replacement`:

- LeanFinder: `Functorial marked anodyne replacement over a simplicial set by a naturally marked
  Cartesian fibration`. Eight hits, including `SSet.modelCategoryQuillen.J`, `.I`, the ordinary
  fibrations/cofibrations instances, and `CategoryTheory.SimplicialNerve`. None states a marked
  relative Cartesian replacement.
- Loogle: `"MarkedAnodyne"`. Zero hits.
- Mathlib grep: `marked.{0,20}anodyne|CartesianFibration|MarkedSSet`. Zero hits.
- LeanSearch: `Functorial relative marked anodyne Cartesian fibrant replacement`. Eight hits:
  ordinary cofibrant-resolution objects and ordinary categorical fibered-functor declarations;
  none provides this marked simplicial result.
- Direct rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the marked-anodyne,
  CartesianFibration and MarkedSSet pattern, and for the exact node id: no matches.
- Direct rg in `lean/Sheaf` for `relative_marked_anodyne_replacement|markedAnodyne|` followed by
  `RelativeCartesianModelStatement` found the three recorded dependencies and marked triangle
  cancellation, not this statement. The helper name `anodyneGeneratorsOver` and theorem name
  were searched in both project trees before writing and were absent.
- Direct search of `dag/lean_names_upstream.json` for `MarkedAnodyne` and the proposed theorem
  name found no match. No existing declaration duplicates the proposed theorem.

Validation: the prescribed `scompile.py` compiled the delivered module cleanly, both its sandbox
and library paths, in 1.1 and 1.2 seconds respectively. `autoImplicit` is explicitly false;
all variables and universe binders are explicit. There are no proved theorem bodies, hollow
definitions, statement disputes, or source corrections.

The independent second reading is left to the next worker, as required by the dispatcher brief.

## Second reading by Q128

I reread the item against HTT Definition the project server, Proposition the project server, Remarks the project server,
the project server and the project server, and the relative small-object use in Corollary the project server.
The node's statement decomposes as follows, with the Lean rendering and verdict after each item:

1. **Ambient objects and generators.** The source uses small marked simplicial sets, a small
   simplicial base `S`, Cartesian fibrations, and the four marked-anodyne generator families.
   Lean uses `S : SSet.{u}`, `SSet.Marked.Over S` (the recorded slice over `sharp S`),
   `SSet.Marked.anodyneGenerators`, and `anodyneGeneratorsOver S`. The helper is the actual
   inverse-image property `fun _ _ i => anodyneGenerators true i.left`; it introduces no second
   marked-anodyne notion. **Matches.**
2. **Relative marked-anodyne meaning.** The node requires the underlying marked map to lie in
   the weakly saturated class, closed under pushouts, transfinite composition, and retracts.
   Lean's `markedAnodyne (η.app X).left` and `markedAnodyne i.left` use the existing
   `SSet.Marked.markedAnodyne`, defined as that saturation. **Matches; no pullback stability is
   assumed.**
3. **Functorial replacement object.** For every `S`, every marked object `X -> S` has a
   functorial marked-anodyne map to a naturally marked Cartesian fibration over `S`. Lean's
   existential `R : Over S ⥤ Over S`, `η : 𝟭 (Over S) ⟶ R`, and the universal `∀ X : Over S`
   state this for every input and make functoriality natural in all maps over the fixed base.
   **Matches.**
4. **Replacement properties.** The node requires `η_X` marked anodyne and the target to be a
   Cartesian fibration whose marking is exactly its Cartesian edges. Lean states
   `markedAnodyne (η.app X).left ∧ IsNaturallyFibrant false (R.obj X)`. The dependency's
   `IsNaturallyFibrant false` is `relativeFibration false` plus marking iff
   `Enhanced.IsCartesianEdge`, with degenerate edges included by the existing marked-set
   convention. **Matches.**
5. **Trivial cofibration clause.** The node requires every relative marked-anodyne map to be a
   trivial cofibration in `M_S`. Lean states `∀ {X Y : Over S} (i : X ⟶ Y), markedAnodyne i.left →
   cof i ∧ weak false i`; the dependency defines `cof` as the underlying degreewise
   monomorphism property and `weak false` by all naturally marked Cartesian-fibration mapping
   tests. **Matches exactly; no model witness or extra hypothesis is introduced.**
6. **Small-object/cellular and universe clause.** The node permits the replacement and its
   small-object construction in the input universe. Lean states
   `transfiniteCompositions.{u} (coproducts.{u} (anodyneGeneratorsOver S)).pushouts
   (η.app X)`, with all objects in `Over S` and the same `u` parameter. **Matches the stated
   cellular conclusion; the expression is a property of the displayed replacement map, not an
   additional existential choice.**
7. **Arbitrary-base conventions.** The source/node require inner-horn fillers, final outer-horn
   Cartesian edges in dimensions at least two, prescribed-target Cartesian lifts, and no
   quasicategory hypothesis on `S` or on the total space. Lean does not bind a `Quasicategory`
   instance in the replacement theorem; these notions are inherited from
   `relativeFibration false` and `IsDistinguishedEdge false` in
   `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`, with the arbitrary-base equivalence
   supplied by `relative_marked_anodyne_calculus`. **Matches.**

Edge cases checked: empty base and empty total object remain in the unrestricted slice
quantifiers; the point base specializes to the absolute naturally marked case; non-quasicategory
bases are allowed; marking-only generators have identity underlying maps and hence do not impose
an unintended underlying inclusion; the one-dimensional final-horn generator remains present for
prescribed-target lifts; and the cellular universe is the same `u` as the input. No nonempty,
finite, characteristic, or universe-equality assumption is present, so zero and empty cases are
covered.

I searched the project and source trees for the exact theorem/helper names and for marked-anodyne,
Cartesian-fibration, and marked-simplicial notions, and searched Mathlib/source with LeanFinder,
Loogle, LeanSearch, and direct `rg` as recorded in the worker report and `searches.jsonl`. The
results contain only ordinary simplicial/model-category infrastructure and the three recorded
project dependencies; no exact existing declaration was found.

I found no mismatch requiring repair. In particular, the recorded dependency declarations were
opened and their signatures agree with every use above: `Over`, `markedAnodyne`, `IsNaturallyFibrant`,
`cof`, and `weak false` are the intended notions. The module has explicit universes and
`autoImplicit false`, contains no hollow definition, and its sole theorem proof is `sorry`.
The node's `lean.statement` is verbatim the theorem signature in the module. The prescribed
`scompile.py` check succeeds without errors or warnings beyond the allowed postponed proof.

Independent search details from this second reading (distinct wording from the author):

- LeanFinder query `Small object cellular functorial replacement in marked simplicial sets over
  an arbitrary base` returned eight generic small-object/relative-cell-complex declarations,
  including `SmallObject.relativeCellComplexιObj` and `attachCellsOfSuccStructProp`; none states
  the marked arbitrary-base replacement conclusion.
- Loogle query `"Cartesian", "replacement"` returned zero hits.
- Mathlib grep via `msearch.py` query
  `marked.*replacement|anodyne.*fibrant|anodyneGeneratorsOver` returned zero hits.
- Direct `rg` with that same pattern on the source `WeilConjectures` and project `lean/Sheaf`
  found the absolute replacement clause in `MarkedAnodyneLiftingCalculus`, the relative lifting
  criterion, and proof-plan mentions; none is this relative functorial cellular replacement.
  Exact-name searches for the theorem and helper also found neither in the shared library.
- I read Mathlib `MorphismProperty/TransfiniteComposition.lean` lines 183–184 and 338–350 and
  `MorphismProperty/Limits.lean` lines 68–70 and 652–655: the cellular expression quantifies
  over small well-ordered continuous chains and small coproducts and uses genuine pushouts.

There are no added definition nodes, dependency modules, or `statement_change` in this delivery,
so H12/H13 and the corrected-statement citer audit introduce no additional files to inspect.
- Independent LeanSearch query `Marked simplicial objects over S admit natural cellular
  replacements by Cartesian fibrations` returned eight ordinary simplicial-object enrichment
  and Kan-Quillen fibration hits, with no marked relative replacement theorem.
