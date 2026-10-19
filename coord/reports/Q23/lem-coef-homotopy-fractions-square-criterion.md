## Worker report

Item: `lem-coef-homotopy-fractions-square-criterion` (Q23 stage 2).

The module `Sheaf.CategoryTheory.Localization.HomotopyFractionsSquareCriterion`
states `CategoryTheory.MorphismProperty.homotopyCalculus_of_functorialSquareCompletions`.
Its proof is exactly `by sorry`; no mathematical theorem is proved. The module also
supplies the helper data types needed to express this statement's functorial choices.
Their data and structure laws are fully specified. There are no new independent
notions, dependency repairs, or statement corrections.

The previous blocker is resolved: `def-coef-zigzag-homotopy-calculus` now records
`Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus` and
`CategoryTheory.RelativeZigzag.HasTwoSidedHomotopyCalculus`. I read the entire
landed module, including its diagram category and identity-insertion functor.
This delivery imports and uses that definition unchanged.

Hypothesis and conclusion audit:

- A category C: `{C : Type u} [Category.{v} C]`, bound by the section and included
  in the theorem's elaborated parameters. Object and morphism universes are
  independently quantified. The dependency forms nerves in `max u v`, allowing
  exactly the source's enlargement to a universe where these categories are small.
- Wide subcategory W: `W : MorphismProperty C` and `[W.IsMultiplicative]` encode
  identity membership and closure under composition, with all objects retained.
- Two-out-of-three: `[W.HasTwoOutOfThreeProperty]`, Mathlib's existing class,
  includes closure under composition and cancellation on both sides. Its full
  definition in `Mathlib.CategoryTheory.MorphismProperty.Composition` was read.
- Wide U,V inside W: `U V : MorphismProperty C`, `[U.IsMultiplicative]`,
  `[V.IsMultiplicative]`, `hUW : U ≤ W`, and `hVW : V ≤ W`.
- Every span X' ← X → Y with u in U: `SpanInput U` has objects `X'`, `X`, `Y`,
  arrows `u : X ⟶ X'`, `f : X ⟶ Y`, and `hu : U u`. It imposes no restriction
  on f. `FunctorialSpanCompletionData.complete` takes every such input.
- Chosen span completion: `SpanCompletion W U S` has `Y'`,
  `g : S.X' ⟶ Y'`, `v : S.Y ⟶ Y'`, `hv : U v`, and
  `commutes : S.u ≫ g = S.f ≫ v`. Lean's left-to-right composition translates
  the node's `gu = vf` literally.
- Span preservation clause: `SpanCompletion.preserves (hf : W S.f) : W g`.
  This is conditional, not a requirement that the original f always lie in W.
- Functoriality of span completions: `SpanInputHom` is the unrestricted triple
  `(a,b,c)` of vertical maps satisfying the two input squares. No vertical map
  is assumed in W. The chosen output `map` satisfies `map_g` and `map_v`, the
  two new squares, and `map_id` and `map_comp`, the identity and composition
  laws. Thus these are functorial choices on all commuting input maps, exactly
  as stated, not just choices on objects or on weak-equivalence maps.
- Every cospan X → Y ← Y' with v in V: `CospanInput V` has objects `X`, `Y`,
  `Y'`, arrows `g : X ⟶ Y`, `v : Y' ⟶ Y`, and `hv : V v`. The arrow g is
  unrestricted. `FunctorialCospanCompletionData.complete` takes every input.
- Chosen cospan completion: `CospanCompletion W V S` has `X'`,
  `u : X' ⟶ S.X`, `f : X' ⟶ S.Y'`, `hu : V u`, and
  `commutes : u ≫ S.g = f ≫ S.v`, again exactly `gu = vf`.
- Cospan preservation clause: `CospanCompletion.preserves (hg : W S.g) : W f`.
- Cospan functoriality: `CospanInputHom` consists of all triples of vertical
  maps commuting with g and v; `map_u` and `map_f` give the output squares,
  and `map_id`/`map_comp` give the functor laws. This has the covariant direction
  required for the proof's vertical zigzag maps.
- Every w:A → B in W has a functorial U-then-V factorization:
  `WeakArrowProperty W : ObjectProperty (Arrow C)` is literally `fun A ↦ W A.hom`.
  Its Mathlib full subcategory has all commuting arrow squares as morphisms.
  `WeakArrowFactorizations W U V` supplies the middle-object functor Z,
  natural maps i from the source and p to the target, with
  `fac : ∀ A, i.app A ≫ p.app A = A.obj.hom`, `hi : ∀ A, U (i.app A)`,
  and `hp : ∀ A, V (p.app A)`. Natural transformations and the functor Z carry
  all identity, composition and naturality laws. The domain is restricted to
  W arrows; no factorization of arbitrary arrows is assumed.
- Conclusion: `RelativeZigzag.HasTwoSidedHomotopyCalculus W` is exactly the
  dependency's predicate: for all endpoints and positive r,s, BOTH unrestricted
  forward and weak forward identity-insertion nerve maps are realization-based
  weak homotopy equivalences. No replacement by ordinary calculus of fractions,
  a model category, or an arbitrary comparison map is used.

Dependency and Mathlib declarations used:

- `Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus`:
  `CategoryTheory.RelativeZigzag.HasTwoSidedHomotopyCalculus`, and its existing
  zigzag/nerve/insertion constructions. The theorem uses the predicate directly.
- `Mathlib.CategoryTheory.MorphismProperty.Composition` (via the dependency):
  `MorphismProperty.IsMultiplicative`, `MorphismProperty.HasTwoOutOfThreeProperty`.
- `Mathlib.CategoryTheory.Comma.Arrow`: `CategoryTheory.Arrow`, `Arrow.leftFunc`,
  `Arrow.rightFunc`; these are used in the factorization data.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`:
  `ObjectProperty.FullSubcategory`, its category, and `ObjectProperty.ι`.
- `CategoryTheory.Functor` and `CategoryTheory.NatTrans` are the existing
  functor and natural-transformation definitions, not private copies.
- The other proof dependency, `lem-coef-nerve-natural-homotopy-equivalence`, has
  no Lean record in the read snapshot. It is named in the complete seven-step
  proof docstring; it is not restated or imported prematurely in this delivery.

Edge cases and strength checks:

- C may be empty: there are no span/cospan/arrow inputs; the conclusion's
  endpoint quantification is also empty. No nonemptiness hypothesis is added.
- Singleton/discrete categories, identities, and W=U=V consisting only of
  identities are permitted. A chosen factorization of an identity need not
  itself have E=A or identity legs; the proof docstring explicitly handles uv.
- W, U, V need not contain all isomorphisms. Only identities and composition
  are requested, exactly the wide-subcategory assumption.
- `r=0` or `s=0` is not newly required by the conclusion: the landed predicate
  has `0 < r` and `0 < s`. Its word constructions still define empty blocks.
- Arbitrary forward arrows are allowed; only the conditional `preserves`
  fields are used to restrict to the all-W case. Neither chosen square is
  assumed to be a universal pullback or pushout.
- A commuting input map need not be a weak equivalence. This matters for the
  proof's endomorphisms e_j and follows from both Hom structures and the full
  subcategory of Arrow C used for factorization.
- `FunctorialFactorizationData U V` in Mathlib factors EVERY arrow, so using
  it directly would strengthen the node. Its full signature was read and it
  was rejected as an exact match. `WeakArrowFactorizations` uses precisely the
  same functor/natural-map encoding restricted to W arrows.

Searches (all tool searches used the prescribed msearch wrapper):

- LeanFinder: `Functorial square completions and factorization of weak equivalences
  imply two sided homotopy calculus of fractions`. Eight hits concerning
  left/right homotopy relations and model-category lifting/localization;
  none states this nerve insertion criterion.
- Loogle: `"HasTwoOutOfThreeProperty", "FunctorialFactorizationData"`.
  Zero hits.
- LeanSearch: `Functorial completion of spans and cospans and factorization of weak
  equivalences imply homotopy calculus of fractions`. Eight hits: classical
  calculus of fractions, derived-category fractions, homotopy relations, and
  cospan presentation; no match for the two nerve weak equivalences.
- Mathlib grep: `homotopy.*[Ff]raction|[Ff]raction.*homotopy|FunctorialSpanCompletion|
  WeakArrowFactorization|hammock` in CategoryTheory. Two bibliography hits for
  Gabriel--Zisman; no theorem or helper with these meanings. Read
  `CalculusOfFractions.lean`'s classical fraction classes when rejecting that
  candidate; they concern ordinary localization rather than homotopy types.
- Project/source grep: the same concepts and the exact item id in
  `WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json`.
  No source declaration or exact statement found. The landed zigzag definition
  is the reusable notion; hammock localization and cosimplicial frame mapping
  files mention related constructions but do not provide this criterion.
- Read Mathlib's `MapFactorizationData`, `FunctorialFactorizationData`, and
  `HasFunctorialFactorization` in full. Their global functorial factorization
  does not provide the weaker restricted-input interface required here.
- Duplicate-name search for `SpanInput`, `SpanInputHom`, `SpanCompletion`,
  `FunctorialSpanCompletionData`, their cospan counterparts,
  `WeakArrowProperty`, `WeakArrowFactorizations`, and the theorem name across
  Mathlib, upstream WeilConjectures, and the project sources: no declarations
  with these full namespace-qualified names.

Source checked: Dwyer--Kan, *Calculating simplicial localizations*,
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf,
Definition 6.1(i), §7.1(iii), and Proposition 8.2, printed p. 29 / PDF page 13.
The three clauses of Proposition 8.2 agree with the node and the helper fields.
The module docstring carries the full seven-step DAG proof plan, including
identity factorizations which are not normalized strictly.

Validation: scompile.py compiles the sandbox file and its library-path form
cleanly, with no errors or warnings (2.2 s and 2.4 s in the final run).
No statement is disputed. The only sorry is the item's named theorem.
The node copy changes only `lean`; all helper declarations are listed there.


## Second reading by Q23

Independent review of the sandbox node, the complete Lean module, the recorded
statement dependency and its complete source module, and the mathematical source.
The source is Dwyer--Kan, *Calculating simplicial localizations*, not Stacks:
Proposition 8.2 on printed p. 29 (PDF page 13), read together with §§1.2, 5.1,
6.1(i), and 7.1(iii). The source URL was opened independently. Its three clauses
are precisely the two functorial square completions and the functorial
factorization in this node. There are no ambient model-category, lifting,
completeness, or universal pushout/pullback hypotheses in Proposition 8.2.
No maintenance repair note exists for this item.

The following is my independent object/hypothesis/conclusion list, matched with
what the Lean file actually declares. All names below are in
`CategoryTheory.MorphismProperty`, except the explicitly qualified conclusion.

| Node object, hypothesis, or clause | Lean rendering and verdict |
| --- | --- |
| A category C, with enlargement allowed for nerves | `variable {C : Type u} [Category.{v} C]`, `universe u v`. PASS: object and morphism sizes are independent; the dependency forms its nerve in `max u v`. |
| W is a wide subcategory | `(W : MorphismProperty C)` and `[W.IsMultiplicative]`. PASS: I opened `Composition.lean`; this means identities and composition, with no restriction on objects. |
| W has two-out-of-three for every composable pair | `[W.HasTwoOutOfThreeProperty]`. PASS: the class extends composition closure and both cancellation implications, exactly all three cases. |
| U and V are wide subcategories contained in W | `(U V : MorphismProperty C)`, `[U.IsMultiplicative]`, `[V.IsMultiplicative]`, `hUW : U ≤ W`, `hVW : V ≤ W`. PASS: no repleteness or extra closure is imposed. |
| Every span X' ← X → Y, with its left arrow u in U | `SpanInput U` has `X'`, `X`, `Y`, `u : X ⟶ X'`, `f : X ⟶ Y`, `hu : U u`; `FunctorialSpanCompletionData.complete` quantifies over every input. PASS: f is arbitrary. |
| A chosen output vertex Y', arrows g and v, v in U | `SpanCompletion W U S` has `Y'`, `g : S.X' ⟶ Y'`, `v : S.Y ⟶ Y'`, `hv : U v`. PASS: the same arrow directions and same class U as the source. |
| The span square commutes | `commutes : S.u ≫ g = S.f ≫ v`. PASS: this is gu = vf in the paper's composition notation. |
| If the original f is in W, the output g is in W | `preserves (hf : W S.f) : W g`. PASS: conditional preservation, not an assumption on all inputs. |
| Span choices are functorial in all commuting input maps | `SpanInputHom` has all three vertical maps and both commuting equations; `map`, `map_g`, `map_v`, `map_id`, `map_comp` specify the output map, naturality and functor laws. PASS: no W condition is imposed on input maps, and complete is a single choice for all inputs. |
| Every cospan X → Y ← Y', with its right arrow v in V | `CospanInput V` has `X`, `Y`, `Y'`, `g : X ⟶ Y`, `v : Y' ⟶ Y`, `hv : V v`; `FunctorialCospanCompletionData.complete` covers every such input. PASS: g is arbitrary. |
| A chosen output vertex X', arrows u and f, u in V | `CospanCompletion W V S` has `X'`, `u : X' ⟶ S.X`, `f : X' ⟶ S.Y'`, `hu : V u`. PASS: the output denominator is in V, not U. |
| The cospan square commutes | `commutes : u ≫ S.g = f ≫ S.v`. PASS: precisely gu = vf. |
| If the original g is in W, the output f is in W | `preserves (hg : W S.g) : W f`. PASS: again conditional, in the correct direction. |
| Cospan choices are functorial in all commuting input maps | `CospanInputHom` and `FunctorialCospanCompletionData.map`, `map_u`, `map_f`, `map_id`, `map_comp`. PASS: covariant output maps with the two required naturality squares, unrestricted vertical inputs, and both functor laws. |
| Every w : A → B in W factors as u then v | `WeakArrowProperty W := fun A ↦ W A.hom`, its `FullSubcategory`, and `WeakArrowFactorizations W U V`. PASS: the domain includes precisely W arrows. `Z` supplies the middle object, `i` and `p` the two legs, `fac` gives `i.app A ≫ p.app A = A.obj.hom`, and `hi`, `hp` put them in U and V. |
| Factorization is functorial in commuting arrow squares | `Z` is an actual functor from the full subcategory of `Arrow C`; `i` and `p` are natural transformations from the source functor and to the target functor. PASS: I read `Arrow`, its commuting-square morphisms, and `ObjectProperty.FullSubcategory`; this imposes no W restriction on the vertical maps and includes all functor/naturality laws. |
| The conclusion is the two-sided homotopy calculus of the dependency | `RelativeZigzag.HasTwoSidedHomotopyCalculus W`. PASS: I opened `ZigzagHomotopyCalculus.lean` in full. The definition quantifies over every x,y and every positive r,s and asserts both identity-insertion nerve maps are weak homotopy equivalences: arbitrary forward arrows and all-W forward arrows. |

For the last row I also read the actual realization-based
`SSet.Enhanced.IsWeakHomotopyEquivalence` in `EnhancedDiagramsCones.lean`:
it requires a bijection on path components and bijections on every positive
based homotopy group of geometric realization. The zigzag dependency uses
vertical W arrows and identity endpoint components, and its insertion repeats
the cut vertex with a backward identity. This is the node's notion verbatim,
not merely an ordinary localization calculus or a connected-components claim.
The helper structures are all data describing the hypotheses of this item,
not independent additional mathematical notions. No new node or dependency
module is needed; none is delivered. The sole statement dependency is imported
and used unchanged. The nerve-natural-homotopy proof dependency still has no Lean
record in this snapshot, so there is no module to import for it.

Edge cases checked independently:

- An empty C is allowed: no nonemptiness assumption or selected object occurs.
  The span, cospan, and W-arrow domains are empty and endpoint quantification in
  the conclusion is empty as well.
- A zero object, when C happens to have one, imposes no additional assumption.
  Identity and zero arrows can be inputs whenever they meet the stated class
  membership conditions. No pointed, additive, or nonzero hypothesis occurs.
- U,V,W may consist only of identities; the classes need not contain all
  isomorphisms. Mathlib's multiplicativity asks only for identities and
  composition. The three completion/factorization assumptions retain their
  actual content in such cases.
- No empty auxiliary index set is excluded. There is no indexing family in this
  statement; the dependency's finite words include the empty-block case as data.
  Its calculus condition requires r,s > 0, exactly Definition 6.1(i), and does
  not silently ask for the left/right calculus cases r=0 or s=0.
- Arbitrary unequal u,v are supported. No SmallCategory assumption forces
  object and hom universes equal; `max u v` in the nerve gives the stipulated
  universe enlargement.
- No field, ring, scheme, characteristic, finiteness, or Noetherian assumption
  appears in either source or Lean. Empty-scheme and characteristic distinctions
  therefore produce no restriction on this category-theoretic criterion.
- Identity factorizations need not be normalized: the helper data do not force
  their middle object or factors to be identities. Step 5 of the proof docstring
  handles the resulting endomorphism uv and its functorial iterates explicitly.

Independent searches used different query wording from the author:

- LeanFinder via msearch: `Functorially extend a span along a weak equivalence
  and dually extend cospans; factor weak equivalences into two classes; nerve
  identity insertion is a weak equivalence`. Eight hits for nerve/Segal results
  and the nerve map itself; no square criterion or helper definition.
- Loogle via msearch: `"HasTwoOutOfThreeProperty", "nerveMap"`. Zero hits.
- LeanSearch via msearch: `Two subcategories with functorial completion of
  commuting squares and functorial factorization yield weak equivalences on
  zigzag category nerves`. Eight hits, principally the global
  `FunctorialFactorizationData` interface, connectedness zigzags, and squares
  of functors; none has this conclusion or these restricted hypotheses.
- Direct rg of Mathlib/CategoryTheory, upstream WeilConjectures, project
  lean/Sheaf, and dag/lean_names_upstream.json for
  `homotop.{0,30}calculus|calculus.{0,30}homotop|square.?completion|weak.?arrow.?factor|span.?completion|cospan.?completion|functorialfactorization`.
  The existing relative-zigzag definition was reused. Other hits concern
  ordinary calculi, global/model-category factorization, or theorem applications,
  not this criterion. Exact helper/theorem names have no existing full-name match.
- I read `FunctorialFactorizationData` in Mathlib's `Factorization.lean`:
  its middle-object functor has domain all of `Arrow C`. Replacing the current
  restricted domain by it would add a genuine stronger hypothesis. I also read
  `HasLeftCalculusOfFractions` and `HasRightCalculusOfFractions`: their
  ordinary fraction cancellation properties are different statements and cannot
  replace this realization/nerve condition.

Mismatch/change verdict: no mathematical or mechanical mismatch found, so the
Lean module and node record were left unchanged. The only addition is this
independent second-reading record. The node differs from the read-only base
only in `lean`; its `lean.statement` is byte-for-byte the theorem signature
before `:= by`. No statement correction, citer audit, new definition node, or
dependency repair is called for. All helper data are real structure fields,
`WeakArrowProperty` has its actual predicate body, and the only `sorry` belongs
to the named theorem. The `by simp`/`by rw` expressions inside structure field
types merely construct identity/composite input maps; they prove no additional
mathematical theorem. Each declaration has its source/blueprint docstring,
and the theorem docstring follows all seven DAG proof steps, including both
natural zigzags and their restriction to all-W forward arrows. Every variable
and universe is bound; there is no private definition, local notation, hidden
choice, axiom, or additional theorem. Maximum Lean line width is 97 characters.

Validation: independent required scompile.py run passed both the sandbox and
library-path forms without errors or warnings (1.9 s and 2.3 s respectively).
