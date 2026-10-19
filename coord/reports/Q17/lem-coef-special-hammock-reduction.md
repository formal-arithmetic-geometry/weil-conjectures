## Worker report

The delivery states `CategoryTheory.specialHammockReduction` in
`Sheaf.CategoryTheory.SpecialHammockReduction`. Its only postponed theorem is that
statement, with `sorry`. All auxiliary data are real constructions or structures; no
object is chosen from an unproved existence theorem. The module docstring and each
helper docstring identify Low and this blueprint node, and the theorem docstring carries
all eleven DAG proof steps. No node statement, proof, or dependency list is changed.

Source read: Low, *Revisiting function complexes and simplicial localisation*,
https://arxiv.org/pdf/1409.8062, conventions on pp. 2--3 and Definitions 3.1--3.2,
Remark 3.3, Lemma 3.4, Proposition 3.5 on printed pp. 12--14 (PDF pages 11--13).
The current main-20261015 blueprint ancestor `prop-coef-integral-exceptional-adjoint`
and its proof paragraph 2 were also read. The node's source page numbers are slightly
stale, but its definitions and assertion agree with these named source places. This
technical statement does not change the unit route.

Hypothesis and clause correspondence:

* The category and its three classes are `{C : Type u} [Category.{v} C]
  [ModelCategory C]`. Mathlib's model structure gives retract closure and
  two-out-of-three of `weakEquivalences C` and the two required weak factorization
  systems (`ModelCategory.Basic`, including the two instances below the class).
  `[HasLimits C] [HasColimits C]` render completeness and cocompleteness; these are
  Mathlib's standard small-shape conventions. The two
  `MorphismProperty.HasFunctorialFactorization` binders render precisely the
  functorial factorizations `(cofibrations C, trivialFibrations C)` and
  `(trivialCofibrations C, fibrations C)`. No endpoint is cofibrant or fibrant by
  assumption; no properness, enrichment, or combinatoriality assumption is present.
* `H : HammockLocalization (weakEquivalences C)` uses the actual recorded hammock
  construction. The theorem applies to any such realization of the construction.
  Its enriched Hom simplicial sets live in `max u v`, as does the special-category
  nerve. The object and arrow universes remain independent.
* `SpecialThreeArrow x y` has exactly `u,v,p,f,i`, with `hp` asserting that `p`
  is a trivial fibration and `hi` that `i` is a trivial cofibration. The endpoint
  arrows have types `u ⟶ x` and `y ⟶ v`, giving the stated leftward orientation.
  This special category is part of the item's own definition; it is not a second
  definition of the unrestricted relative zigzag category.
* `SpecialThreeArrowHom s t` has exactly the pair `a : s.u ⟶ t.u`,
  `b : s.v ⟶ t.v`, and `left`, `right`, `middle` render, respectively,
  `p' a = p`, `b i = i'`, `b f = f' a` in Lean's composition order.
  `specialThreeArrowCategory` composes the two components. It imposes no extra
  weak-equivalence condition. In `specialHammockU` and `specialHammockV`, library
  two-out-of-three directly derives their markings from these outer equations.
* `specialThreeArrowU/V` are the actual two evaluation functors. For every nerve
  simplex `s` (a functor from `Fin (k+1)`), `specialHammockPath s` constructs
  precisely its left-backward, middle-forward, right-backward path. The three
  naturality laws are the three equations of each component morphism; its endpoint
  chains are `hammockEndpoint`, so their vertical arrows are identities.
* `ρ` is an actual family of simplicial maps. `IsSpecialHammockReduction H (ρ x y)`
  requires `HammockReduces (specialHammockPath s)` to the simplex corresponding to
  `ρ(s)` for EVERY degree and EVERY simplex. This characterizes the canonical
  comparison, rather than asserting an arbitrary weak equivalence between the spaces.
* `SSet.Enhanced.IsWeakHomotopyEquivalence (ρ x y)` is the existing realization-based
  condition: bijective path components and all positive based homotopy groups.
* `SpecialHammockPullback a y` supplies the endpoint functor and its natural
  projection. Its `pullback` fields assert the actual universal pullback squares
  of `p` along `a`; `middle` and `right` specify the resulting arrows, while
  `v_eq` and `maps_v` keep the second interior column fixed on objects and arrows.
  Naturality of `projection` forces the first-column map to be the induced pullback
  map. Thus these are canonical actions up to their usual unique isomorphisms,
  not arbitrary maps or strengthened hypotheses about chosen actions.
* Dually `SpecialHammockPushout x b` supplies the natural coprojection, the
  universal `pushout` squares for `i` along `b`, the induced middle and left arrows,
  and unchanged first-column objects and maps (`u_eq`, `maps_u`).
* For each endpoint change, the theorem supplies an enriched point `A` or `B`
  whose EVERY simplex reduces the actual-arrow path. `specialHammockPre/Post`
  are pre/postcomposition with exactly this point, using the recorded
  `H.enrichment.comp` and the monoidal unitors. The two `SSet.Homotopy` clauses
  compare these compositions to the nerve of the corresponding endpoint functor.
  They have the orientations of the source-end and target-end hammock prisms in
  DAG steps 9 and 10. The homotopies are maps into the original hammock simplicial
  sets, so their simplices are actual reduced commutative hammocks via `H.simplices`.
  Pasting the two homotopies gives the simultaneous endpoint comparison.
* `specialThreeArrowActual f` has `p=i=1`. The actual-map conjunct requires its
  image to be the reduction of `hammockActualPath ... 0 f`. An identity `f`
  is therefore the length-zero hammock, exactly as the dependency's reduction
  convention requires; a nonidentity is the length-one hammock.

Dependency declarations and source signatures read:

* `Sheaf.CategoryTheory.HammockInfinityLocalization`:
  `CategoryTheory.hammockLocalization_universal` (the node's recorded theorem),
  and the complete definitions/docstrings of `HammockChain`, `HammockStep`,
  `HammockReduction`, `HammockReduces`, `ReducedHammock`, `hammockEndpoint`,
  `hammockRows`, `hammockActualPath`, `HammockLocalization`, and the replacement,
  mapping comparison, and naturality interfaces through the final theorem.
  The delivery reuses these definitions; it does not restate the dependency theorem.
* Proof import `Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus`:
  `CategoryTheory.RelativeZigzag.ThreeArrow`, `Diagram`, `Hom`, `diagramCategory`,
  and `HasTwoSidedHomotopyCalculus`, with their docstrings and signatures. These
  are the unrestricted categories used in proof steps 3--8; the special category
  has only the stronger outer-arrow conditions specified in the item.
* Proof import `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`:
  `llp_isStableUnderRetracts`, `rlp_isStableUnderRetracts`,
  `llp_isStableUnderCobaseChange`, `llp_isMultiplicative`, and the definitions
  `llp`, `rlp`, read at lines 35--79. These are the Mathlib match of
  `lem-coef-lifting-class-closure`.
* `lem-coef-homotopy-fractions-square-criterion` and
  `lem-coef-homotopy-fractions-hammock-comparison` have no Lean attachment yet.
  They are proof dependencies only, so they are named in the proof docstring and
  no nonexistent import or duplicate statement is introduced.
* `Mathlib.AlgebraicTopology.ModelCategory.Basic`: the model-category class and
  both weak-factorization-system instances, plus `MorphismProperty.Factorization`'s
  `HasFunctorialFactorization` signature. `SSet.Homotopy` was read in
  `Mathlib.AlgebraicTopology.SimplicialSet.Homotopy`: it is a simplicial-cylinder
  homotopy with the specified two endpoints, not equality only on components.

Edge cases checked: degree `k=0` gives one row; all identities and `f=1` reduce to
an empty path, not a forced length-one identity column. Empty special categories and
empty mapping spaces impose no hidden nonemptiness assumption; all maps and weak
homotopy equivalences use the usual empty-set meanings. Arbitrary endpoints are
retained without replacements or fibrancy hypotheses. Endpoint changes need not be
weak equivalences: only the trivial outer arrows and the forced vertical maps are
marked. The pushout coprojection and pullback projection over an arbitrary endpoint
change are not wrongly assumed to be weak equivalences. Independent `u,v` are combined
only by `max u v` for the mapping/nerve universe. Zero/initial/terminal objects need no
extra cases or restrictions. No source or statement fault was found.

Searches actually run:

* `msearch.py ... leanfinder "The nerve of special three arrow zigzags in a model
  category is weakly equivalent to the hammock mapping space"`: eight results,
  concerning nerves and truncated homotopy categories; none states this comparison.
* `msearch.py ... loogle '"hammock"'`: zero hits.
* `msearch.py ... grep 'hammock|specialHammock|SpecialZigzag'`: zero Mathlib hits.
* `rg -n 'hammock|specialHammock|SpecialZigzag'` in upstream `WeilConjectures`
  and project `lean/Sheaf`: the landed hammock interface and mentions in
  `CosimplicialFrameMapping`; no special-category comparison declaration.
* `grep -rn 'lem-coef-special-hammock-reduction'` in upstream `WeilConjectures`:
  no hits. `rg` in `dag/lean_names_upstream.json` and the project sources found
  no upstream declaration, but did locate `RelativeZigzag.ThreeArrow` in the
  landed general calculus module, which is reused as the proof's unrestricted
  category via its required proof import.

Validation: `scompile.py Q17 lem-coef-special-hammock-reduction
lean/Sheaf/CategoryTheory/SpecialHammockReduction.lean` is the only compiler entrypoint
used. Initial failures exposed implicit interior chains and unfolding of the two
endpoint naturality equations; explicit chain arguments and definition unfolding
repair those elaboration issues. The final compile and required delivery dry run
are recorded below after their completion. Independent second reading is left to
the dispatcher-designated second worker, as requested; this is a worker report only.

Final validation: the repaired file compiled with no errors or warnings through
`scompile.py`, both as `Sheaf/Stage2/Sandbox0.lean` (2.1 s) and as the final library
module (2.3 s). `deliver2.py Q17 lem-coef-special-hammock-reduction --no-push`
printed `OK (dry run)`: compilation and maintainer preflight passed, with only the
expected missing independent second-reading section reserved for the second worker.
Nothing was pushed. There are no new definition nodes or dependency repairs in this packet.


## Second reading by Q17

I independently read the sandbox node and every declaration in
`lean/Sheaf/CategoryTheory/SpecialHammockReduction.lean`, against Low,
*Revisiting function complexes and simplicial localisation*,
https://arxiv.org/pdf/1409.8062, conventions on printed pp. 2--3, Definitions
3.1--3.2, Remark 3.3, Lemma 3.4 and Proposition 3.5 on printed pp. 12--14
(PDF pages 11--13). The source is Low, not a Stacks tag: the node explicitly
says no Stacks tag states this result. I also read the current blueprint ancestor
`prop-coef-integral-exceptional-adjoint` and proof paragraph 2. This is an
internal mapping-space input to that route. No unit or target statement changes.
There is no maintenance repair note for this item.

My inventory of the node, in statement order, and the corresponding Lean is:

1. An ordinary category M, with separately sized objects and morphisms:
   `{C : Type u} [Category.{v} C]`. Verdict: exact; neither universe is equated
   with or bounded by the other.
2. Classes C, F, W, retract closure and two-out-of-three for W, the two weak
   factorization systems, and completeness/cocompleteness:
   `[ModelCategory C] [HasLimits C] [HasColimits C]`. I read Mathlib's
   `ModelCategory` fields and its two `IsWeakFactorizationSystem` instances.
   Conversely its `mk'` constructor takes the stated WFS formulation; retract
   closure for the lifting classes is a consequence, not a stronger mathematical
   assumption. Mathlib's `HasLimits`/`HasColimits` use shapes the size of the
   hom-sets, the usual small-limit convention. Low works with finite limits and
   colimits; the node explicitly uses complete and cocomplete model categories,
   and Lean follows that convention. Verdict: exact for this node.
3. Functorial factorizations of the two indicated kinds: the two explicit
   `MorphismProperty.HasFunctorialFactorization` instances, for
   `(cofibrations C, trivialFibrations C)` and
   `(trivialCofibrations C, fibrations C)`. I read the class: it asserts
   nonempty genuine functorial factorization data. Verdict: exact; the source's
   standing functoriality hypothesis is present.
4. The hammock localization of (M,W):
   `H : HammockLocalization (weakEquivalences C)`, using the dependency's actual
   declaration. Its `simplices` equivalence has reduced commutative hammocks
   as codomain; `row_operators`, `identities` and `composition` specify the
   required deletion/repetition, empty identities, and concatenation followed
   by reduction. Verdict: the same construction, with no replacement by an
   arbitrary mapping space or a hom-set in the ordinary localization.
5. Arbitrary endpoints x,y and the category T(x,y):
   `SpecialThreeArrow x y` contains precisely `u`, `v`, `p : u ⟶ x`,
   `f : u ⟶ v`, `i : y ⟶ v`, `hp : trivialFibrations C p`, and
   `hi : trivialCofibrations C i`. Verdict: both arrow directions and both
   triviality conditions match Low Definition 3.2 and the node.
6. Morphisms are pairs of maps with three equations:
   `SpecialThreeArrowHom.a`, `.b`, `.left`, `.right`, `.middle` translate
   respectively a, b, p'a=p, bi=i', bf=f'a. `specialThreeArrowCategory`
   gives componentwise identities and composition. The `marked` fields in
   `specialHammockU/V` derive both component weak equivalences by the
   outer equations and two-out-of-three, without adding a condition on a
   morphism. Verdict: exact category, rather than a smaller category obtained
   by imposing extra lifting conditions on its morphisms.
7. A string of these morphisms gives the three-column unreduced hammock:
   `specialThreeArrowU/V` are the evaluation functors, and
   `specialHammockPath s` is backward p, forward f, backward i, with constant
   endpoint chains. Its three naturality proofs are exactly the three
   equations above. Verdict: correct for every simplex degree, including 0.
8. Reducing those strings defines a simplicial comparison:
   `∃ ρ : ∀ x y : C, nerve (SpecialThreeArrow x y) ⟶ H.enrichment.Hom x y`
   followed by `∀ x y, IsSpecialHammockReduction H (ρ x y)`.
   The predicate quantifies over every k and every k-simplex s and requires
   `HammockReduces (specialHammockPath s)` to the reduced hammock corresponding
   to `ρ(s)`. Verdict: the canonical comparison is characterized on all
   simplices; it is not an arbitrary map satisfying a homotopy-type assertion.
9. This very map is a weak homotopy equivalence:
   `∀ x y, SSet.Enhanced.IsWeakHomotopyEquivalence (ρ x y)`.
   I read the reused definition in `EnhancedDiagramsCones`: realization
   induces a bijection on components and bijections on every positive based
   homotopy group, for every source basepoint. Verdict: exact meaning of weak
   homotopy equivalence, with no nonemptiness premise.
10. Pullback along every source map a:x'→x acts on T:
    `∀ (x' x y : C) (a : x' ⟶ x), ∃ P : SpecialHammockPullback a y, ...`.
    `P.pullback` is the universal `IsPullback` square, its natural `projection`
    gives the induced maps on the first column, `middle` and `right` give
    the resulting zigzag, and `v_eq`/`maps_v` fix the second column.
    The `HEq` expresses transport along the specified object equalities;
    it does not change the mathematical map. Verdict: the stated pullback
    action up to the usual canonical identifications, not an arbitrary action.
11. This source action compares to precomposition by the actual arrow a:
    the enriched point A satisfies the reduction of
    `hammockActualPath (weakEquivalences C) k a` in EVERY degree;
    `specialHammockPre H A` uses the given enriched composition. The
    `Nonempty (SSet.Homotopy (nerveMap P.functor ≫ ρ x' y)
    (ρ x y ≫ specialHammockPre H A))` clause has the direction of the
    source-end prism in node step 9. Verdict: correct actual-map comparison
    as a simplicial-cylinder homotopy in the original hammock mapping space.
12. Pushout along every target map b:y→y' acts on T:
    `∀ (x y y' : C) (b : y ⟶ y'), ∃ P : SpecialHammockPushout x b, ...`.
    `P.pushout` is the universal square of i along b; `coprojection`,
    `middle`, `left`, `u_eq`, `maps_u` specify the resulting arrows and
    unchanged first column. Verdict: precisely the source's pushout action.
13. The target comparison is postcomposition by actual b:
    B is characterized by the actual-arrow reduction in every degree,
    `specialHammockPost H B` uses the same enriched composition, and
    the homotopy runs from `ρ x y ≫ specialHammockPost H B` to
    `nerveMap P.functor ≫ ρ x y'`. Verdict: the direction is exactly the
    target prism in node step 10. The two endpoint comparisons paste for
    simultaneous endpoint changes as in that step; no extra endpoint premise
    is needed. Reading Mathlib's `SSet.Homotopy` confirmed the actual
    cylinder map with both endpoints, rather than equality only on components.
14. With p=i=1, the image is f's actual-arrow hammock:
    `specialThreeArrowActual f` has both outer maps identities, and the
    third conjunct identifies its image by
    `HammockReduces (hammockActualPath ... 0 f) ...`.
    Verdict: exact after the dependency's required reduction. When f itself
    is an identity its reduced one-arrow representative is the length-zero
    hammock; there is no erroneous nonempty-length requirement.
15. There are no endpoint cofibrancy or fibrancy conditions, or enrichment,
    properness or combinatoriality conditions on the model category.
    Verdict: none occur among the theorem's hypotheses. H supplies the
    constructed hammock enrichment, not an enrichment of the input category.

Dependencies were read from their nodes and declaration source, not inferred
from names. In particular the recorded
`CategoryTheory.hammockLocalization_universal` and its `HammockLocalization`,
`HammockChain`, `HammockStep`, `HammockReduction`, `HammockReduces`,
`ReducedHammock`, `hammockEndpoint`, `hammockRows`, `hammockActualPath`
interfaces are usable exactly as imported. I also read the remaining
replacement/mapping/naturality interfaces of its module. The proof import
`RelativeZigzag.ThreeArrow` is the unrestricted category built from `Diagram`
and its marked vertical `Hom`; its `HasTwoSidedHomotopyCalculus` is the
specified pair of identity-insertion weak equivalences. It does not already
provide this item's special subcategory or comparison. The Mathlib lifting
import supplies `llp`, `rlp`, their retract/base/cobase-change closure and
multiplicativity instances. The square-criterion and generic hammock-comparison
proof nodes currently have neither Lean attachment nor Mathlib match: they
are cited in the complete proof docstring and have no nonexistent imports.
No new definition node or dependency module is delivered, so H12/H13 have
no additional files to inspect.

Edge cases: k=0 is included, as are identity maps and all-identity zigzags;
length-zero reduction agrees with Low Definition 3.1. Empty T and empty
mapping spaces require no chosen object or basepoint. An empty input category
is not a complete model category (the initial/terminal object axioms already
exclude it), so no additional exclusion has been introduced. Zero objects and
initial/terminal endpoints require no extra assumption. General endpoint
changes need not be weak equivalences; neither pullback projections nor
pushout coprojections are incorrectly required to be weak equivalences.
There is no arithmetic n or characteristic here. All universes are bound;
`max u v` accommodates the special-category nerve and hammock simplices
without requiring u=v. All quantifiers follow the node's order: one reduction
family for all endpoints, then arbitrary endpoint changes and their canonical
actions/comparison homotopies.

Independent duplicate searches (using different queries from the first reader):

* `msearch.py Q17 lem-coef-special-hammock-reduction leanfinder
  'Special zigzag categories of trivial fibrations and trivial cofibrations
  compute simplicial localization mapping spaces'`: eight hits, on ordinary
  cofibrant localization and bifibrant maps, none on special hammock categories
  or this mapping-space comparison.
* `msearch.py ... loogle '"ThreeArrow"'`: zero hits.
* `msearch.py ... grep 'hammock|SpecialThreeArrow|ThreeArrow|special.*zigzag'`:
  zero Mathlib hits.
* Independent `rg` on upstream `WeilConjectures`, project `lean/Sheaf`,
  Mathlib CategoryTheory/AlgebraicTopology, with
  `special.{0,20}(hammock|zigzag)|three.?arrow|three.?arrows|trivialFibrations.*trivialCofibrations`:
  the unrestricted project `RelativeZigzag.ThreeArrow`, proof-plan mentions
  in `CosimplicialFrameMapping`, and unrelated ordinary composites/duality
  declarations; no competing special category or theorem. `rg` on
  `dag/lean_names_upstream.json` for the new declaration names also found
  none. The existing unrestricted category is a different notion and remains
  the proof import, rather than being restated.

No mathematical mismatch or missing clause was found, and no Lean or node
field was changed. The only edit is this second-reading report. The module
has real structure/functor/path data; its only postponed theorem is
`specialHammockReduction`. All source/blueprint docstrings and the eleven
proof steps are present. There is no local notation, private substitute,
unbound variable, new axiom, or line over 100 columns. The recorded
`lean.statement` was checked byte-for-byte against the theorem signature
through the text preceding `:= by`: it matches. Comparing the sandbox node
to the read-only base shows only the authorized `lean` field differs.

Validation after this independent reading:
`scompile.py Q17 lem-coef-special-hammock-reduction
lean/Sheaf/CategoryTheory/SpecialHammockReduction.lean`, run from the item
sandbox, passed without errors or warnings: sandbox 2.2 s, library module
2.6 s. No global build or direct compilation was run. The delivery dry run
and pushed commit are recorded by the prescribed wrapper.
