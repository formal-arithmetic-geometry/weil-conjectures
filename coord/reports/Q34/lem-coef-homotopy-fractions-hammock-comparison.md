## Worker report

The module `Sheaf.CategoryTheory.Localization.HomotopyFractionsHammockComparison`
states `CategoryTheory.RelativeZigzag.threeArrow_hammock_comparison`, with its
whole proof `sorry`. It also defines the canonical-map characterization
`CategoryTheory.RelativeZigzag.IsThreeArrowHammockReduction`, with real data
(a Prop-valued definition, no choice and no postponed proof). This is an owning-node
helper describing the map mentioned by the item, not a new independent notion.

Hypothesis and conclusion correspondence:

- A category C is `{C : Type u} [Category.{v} C]`, with independent universes u, v.
- The wide subcategory W is `(W : MorphismProperty C) [W.IsMultiplicative]`:
  identities and composition are exactly the wide-subcategory conditions, without
  any two-out-of-three, saturation, isomorphism or model-category assumption.
- The two-sided homotopy calculus is
  `(hcalculus : HasTwoSidedHomotopyCalculus W)`, precisely the dependency's
  two positive-block insertion conditions, including its all-W condition.
- The hammock simplicial set is `(H : HammockLocalization W)` and
  `H.enrichment.Hom x y`. H is an arbitrary implementation of the dependency's
  exact reduced-hammock enrichment, not an extra mathematical restriction.
  Its existence is the recorded `hammockLocalization_universal` theorem.
- Any endpoints are `(x y : C)`; neither is required cofibrant or fibrant.
- The domain is exactly `zigzagNerve W [.backward, .forward, .backward] x y`.
  The middle arrow is unrestricted and both outer arrows belong to W.
- A simplicial map is the existential witness `ρ : ... ⟶ H.enrichment.Hom x y`.
  `IsThreeArrowHammockReduction W H x y ρ` specifies its action on EVERY
  k-simplex, rather than merely asserting the existence of an unrelated weak
  equivalence. A k-simplex σ is `ComposableArrows (ThreeArrow W x y) k`.
  U,V are the two interior vertical W-chains. Their objects are the two interior
  objects of every row of σ; their maps are exactly the corresponding components
  of every σ.map a (all i,j,a are quantified). The natural transformations p,f,q
  are exactly the row's three horizontal arrows, with membership hp,hq in W on
  the outer two. Their naturality records all commuting squares. The endpoints
  are `hammockEndpoint W k x` and `hammockEndpoint W k y`, hence have identity
  vertical arrows. `HEq` is equality after the stored endpoint identifications;
  in particular the rightmost Diagram object z carries the tail proof z = y,
  so the right arrow is the canonical transport of the stored arrow z → v.
  `HammockReduces` relates precisely the backward/forward/backward path of
  these transformations to `(H.simplices x y k (ρ.app (op ⦋k⦌) σ)).val`.
  This states ordinary reduction, including identity deletion and newly adjacent
  column composition, using the dependency's actual operations.
- The concluding `SSet.Enhanced.IsWeakHomotopyEquivalence ρ` is the shared
  geometric-realization definition: bijection on components and on every positive
  homotopy group at every source basepoint. Since these maps preserve the group
  operation, these bijections are the stated group isomorphisms.
- No model structure, cofibrancy, fibrancy or properness binder appears.

The existential presentation retains both source assertions (the canonical
simplicial reduction map exists, and that map is a weak equivalence). Its
simplexwise characterization specifies all of the input hammock, so no arbitrary
map or Nonempty choice substitutes for the canonical comparison. Column data
are existential witnesses in the characterization, not selected objects used to
define an unspecified comparison. No statement correction was needed.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus`:
  `CategoryTheory.RelativeZigzag.HasTwoSidedHomotopyCalculus`, `ThreeArrow`,
  `zigzagNerve`, `Diagram`, `Hom` (including `.app`) and its category instance.
  Read the full module, in particular horizontal orientations, endpoint identities,
  insertion functor, positive-block quantifiers and the unrestricted middle arrow.
- `Sheaf.CategoryTheory.HammockInfinityLocalization`:
  `CategoryTheory.HammockChain`, `HammockStep`, `hammockEndpoint`,
  `HammockReduction`, `HammockReduces`, `ReducedHammock`, `HammockLocalization`
  (including its `simplices` equivalences and row-reduction equations), and
  `hammockLocalization_universal`.
- Through these imports: the existing
  `SSet.Enhanced.IsWeakHomotopyEquivalence` from
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Read its realization/component/
  homotopy-group definition, not an ordinary localization or hom-set substitute.
- Mathlib's `CategoryTheory.nerve`, `ComposableArrows`, `Quiver.Path` and
  natural transformations are used directly. Read the nerve source: an n-simplex
  is exactly `Fin (n+1) ⥤ C`, and simplicial operators precompose its row functor.

The proof dependencies `lem-coef-proper-word-colimit-invariance` and
`lem-coef-zigzag-concatenation-invariance` have neither Lean nor Mathlib records
in the base read for this delivery. They are proof-only dependencies and are not
restated here. Their imports are omitted until modules exist. The theorem
Docstring records all seven proof steps, including both inputs, the empty-forward
word, proper-image intersections, inverse-column contractions, explicit comparison
homotopies and basepoint changes.

Edge cases checked:

- Empty C is allowed (the endpoint-parametrized assertion is vacuous); no
  Nonempty/inhabited category assumption occurs.
- Empty three-arrow categories and hence empty nerves are allowed; no simplex
  or basepoint is chosen by the statement. Weak equivalence retains its component
  condition, including the empty-space case.
- k = 0 gives three horizontal arrows and constant single-object interior chains;
  all k, all vertical morphisms and identity morphisms are included.
- x = y and identity horizontal columns are allowed. The specified raw path may
  reduce to a length-zero hammock; no nonidentity or reduced-input restriction
  is imposed.
- The right endpoint in the inductive Diagram is an equality, not necessarily a
  definitional equality. The HEq clauses accommodate exactly this existing
  encoding without replacing its zigzag category.
- No forward-block length is restricted beyond the dependency's own r,s > 0
  convention; the proof Docstring treats words with no forward letters separately.
- Both sides live in SSet.{max u v}; no equality between u and v is assumed.

Searches (2026-10-16 UTC):

1. `msearch.py ... leanfinder` query:
   "The nerve of three arrow relative zigzags maps by weak homotopy equivalence
   to hammock localization under a two sided homotopy calculus of fractions".
   Eight hits concern homotopy relations factoring through ordinary localization,
   truncated nerve/homotopy-category maps and the ordinary nerve functor. No match.
2. `msearch.py ... loogle '"hammock"'`: zero hits.
3. `msearch.py ... grep 'hammock|homotopy.*[Ff]raction|[Ff]raction.*homotopy'`:
   nine Mathlib hits, all bibliography references to calculus of fractions.
4. `msearch.py ... leansearch` query:
   "The nerve of the category of three arrow zigzags computes a hammock
   localization mapping space". Eight hits concern ordinary nerve definitions,
   its simplices and Cech nerves. No comparison theorem.
5. `rg -n 'hammock|threeArrow|homotopy.*[Ff]raction'` in the upstream
   `WeilConjectures/`: no hits. `rg` for this item id and for
   `threeArrow.*hammock|hammock.*threeArrow` in upstream and `lean/Sheaf`:
   no hits. Read the two landed source modules rather than duplicating their
   definitions. Searched `dag/lean_names_upstream.json` for the item and hammock/
   three-arrow names: no match.

Source verified by opening the Dwyer--Kan PDF at
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf :
Sections 2.1, 5.1--5.5, Definition 6.1(i), Proposition 6.2(i), first comparison,
and proof 6.5. These give exactly the source operations and assumptions used
here. No Stacks replacement was used. No statement dispute or dependency fault.

Validation: the prescribed `scompile.py Q34
lem-coef-homotopy-fractions-hammock-comparison
lean/Sheaf/CategoryTheory/Localization/HomotopyFractionsHammockComparison.lean`
passed the sandbox and library-path file compiles (1.7 s each), without errors
or warnings. All universes and binders are explicit and autoImplicit is false.

## Second reading by Q34

I independently opened the item node, its copied node record, the module, both
recorded dependency modules, and the Dwyer--Kan source at Proposition 6.2(i),
Definition 6.1(i), and Sections 2.1 and 5.1. The node's statement parses into
the following list, with the corresponding Lean rendering and verdict:

1. A category `\mathcal C` and a wide subcategory `W`: `{C : Type u}` with
   `[Category.{v} C]`, `(W : MorphismProperty C)`, and
   `[W.IsMultiplicative]`. `IsMultiplicative` supplies the identity and
   composition closure of the wide subcategory and adds no two-out-of-three,
   saturation, model, or properness assumption. This is the same relative
   category as `def-coef-zigzag-homotopy-calculus`.
2. The two-sided homotopy calculus of fractions: the explicit hypothesis
   `hcalculus : HasTwoSidedHomotopyCalculus W`, whose two insertion maps and
   positive block lengths are exactly the dependency declaration.
3. Arbitrary endpoints `x,y`: the binders `(x y : C)` impose no cofibrancy,
   fibrancy, properness, or other endpoint condition.
4. The source simplicial set: `zigzagNerve W
   [.backward, .forward, .backward] x y`, the nerve of diagrams
   `x <- u -> v <- y` with the two outer arrows in `W` and unrestricted middle
   arrow, with the dependency's commuting vertical morphisms.
5. The hammock target: `H : HammockLocalization W` and
   `H.enrichment.Hom x y`. Its `simplices` equivalence is precisely the
   reduced hammock simplicial set of the hammock-localization dependency.
6. The canonical reduction map and its characterization: the existential
   `ρ : ... ⟶ H.enrichment.Hom x y`, together with
   `IsThreeArrowHammockReduction W H x y ρ`. For every degree and every
   composable string, this predicate retains the two interior chains, all
   vertical arrows, the three horizontal transformations, endpoint identities,
   and the reduction to `H.simplices ... (ρ.app ...)`; hence it describes the
   stated three-arrow reduction rather than an unrelated map.
7. Weak homotopy equivalence: the final conjunct
   `SSet.Enhanced.IsWeakHomotopyEquivalence ρ` is the project definition using
   realization components and all positive based homotopy groups.

Every object, hypothesis, quantifier order, and conclusion clause is present.
The source's Proposition 6.2(i) gives the two reductions
`W^{-1}CW^{-1}` and `W^{-1}WW^{-1}` to hammock mapping spaces; this item is
the first (`-+-`) comparison, exactly as the node says. No hypothesis is
stronger than the source and no source clause is omitted. `hcalculus` is a
proposition argument rather than an extra structure, and `H` is the recorded
implementation of the hammock mapping simplicial set, not a model-category
assumption.

Edge cases are covered: an empty `C` makes the endpoint assertion vacuous;
the three-arrow diagram category and its nerve may be empty; `k = 0` gives
the three horizontal arrows with one-row vertical chains; `x = y` and identity
outer arrows are allowed; and length-zero reduced hammocks are represented by
the dependency's path constructors. No zero object, scheme, characteristic,
or finiteness assumption occurs in this node, so those cases are irrelevant
and no binder excludes them. The two universes `u,v` remain independent and
the simplicial sets live in `max u v`.

The duplicate search was repeated with exact declaration names in
`WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json`; it found
no existing `threeArrow_hammock_comparison` or
`IsThreeArrowHammockReduction`. Broad `rg` searches for hammock,
three-arrow, and homotopy-calculus terms found only the two recorded
dependency modules and unrelated prose. A fresh `msearch.py ... leanfinder`
search for a three-arrow hammock weak equivalence returned only ordinary
model-category/localization results, with no matching declaration. The source
PDF was checked directly at the cited proposition and definitions. Therefore
the worker's module is the single definition/statement of this notion and no
existing record should replace it.

I found no mismatch and made no code or node-statement changes. The copied node
`lean.statement` is byte-for-byte the theorem signature from the module. The
prescribed `scompile.py` compilation succeeds for both sandbox and library-path
compiles, with no errors or warnings.
