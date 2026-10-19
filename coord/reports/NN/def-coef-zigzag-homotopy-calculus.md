## Worker report

The module `Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus` defines
`CategoryTheory.RelativeZigzag.HasTwoSidedHomotopyCalculus`, together with the actual
fixed-word zigzag categories and identity-insertion functors it uses. This is a definition
node: there are no theorem declarations and no postponed proofs. Structural proofs in the
category and functor records verify that the specified data form categories and functors;
no mathematical assertion about weak equivalences is proved.

Source read: Dwyer--Kan, *Calculating simplicial localizations*, Sections 5.1--5.2,
printed p. 24, Section 5.9 and Definition 6.1(i), printed p. 25 (PDF pages 8--9).
The source's words compose right to left; the node and this module read them left to right.
The two displayed insertion maps of Definition 6.1(i) are the two conjuncts of the main
definition. No correction to the node's statement is needed.

Clause-by-clause correspondence:

- A category is `C : Type u` with `[Category.{v} C]`. The universes `u` and `v` are
  independent. The same object type underlies the wide subcategory, represented by
  `W : MorphismProperty C` with `[W.IsMultiplicative]`: it contains every identity and
  is closed under composition. No two-out-of-three or isomorphism-closure assumption
  is added.
- A word is `List Letter`; the constructors `forward`, `weakForward`, and `backward`
  are respectively `+`, `+_W`, and `-`. A cons adds an arrow at the left, so the word
  is read from the source on the left to the target on the right.
- `Horizontal W l x y` is `x ⟶ y` for `forward`, the subtype of such maps in `W`
  for `weakForward`, and the subtype of maps `y ⟶ x` in `W` for `backward`.
- `Diagram W w x y` recursively supplies precisely those arrows and intermediate
  objects, with endpoints `x,y`. At the empty word its data is a universe lift of
  the equality `x = y`, which is exactly a single vertex with the prescribed endpoints.
  The final equality in a nonempty diagram identifies its last vertex with `y`.
- `Vertex`, `first`, `last`, and `objectAt` index the actual vertices. `Endpoints`
  and `endpoints` expose their endpoint identifications, including the empty word.
- `Hom W D E` supplies a vertical component at each vertex, a `mem` proof that each
  component belongs to `W`, and `commutes`, which is the recursive commuting-square
  condition `Commutes`. `Square` uses the forward or backward square equation as
  appropriate. The `left` and `right` fields say the endpoint components are the
  identities after the endpoint identifications. Thus there is no unrestricted
  extra endpoint action.
- `diagramCategory` has those `Hom`s, pointwise identity components, and pointwise
  vertical composition. Composition is legal because `W` is multiplicative.
- `zigzagNerve W w x y` is Mathlib's ordinary `CategoryTheory.nerve` of that category.
  Its simplices are `ComposableArrows`, i.e. functors from finite ordinals; its
  operators are restriction, hence compose/delete arrows and insert identities.
  The nerve has universe `max u v`, so no equality of object and morphism universes
  or restriction to a smaller category is imposed.
- Weak homotopy equivalence is the existing
  `SSet.Enhanced.IsWeakHomotopyEquivalence`. Its full implementation was read:
  `SSet.toTop.map` induces `componentsMap` on `ZerothHomotopy`, required bijective,
  and `homotopyGroupMap` on cubical homotopy classes relative to the boundary,
  required bijective in every positive degree at every point in the source
  realization. These are the induced group isomorphisms because postcomposition
  preserves concatenation. The empty-source component condition is retained.
- `insertDiagram W p q` repeats the cut vertex between `p` and `q` and adds its
  backward identity. Its recursion preserves every other horizontal arrow.
  `insertVertical` repeats the corresponding vertical component and preserves the
  other components. Endpoint identifications are transported by `eqToHom`, rather
  than chosen maps. `insertFunctor` packages exactly these operations.
- `fractionPrefix l r` is `-` followed by `r` copies of `l`, and
  `fractionSuffix l s` is `s` copies of `l` followed by `-`. Their concatenation
  is the node's `- l^(r+s) -` (the two contiguous repeated-letter blocks), and
  insertion produces `- l^r - l^s -`.
- `HasTwoSidedHomotopyCalculus` quantifies over every `x,y : C` and
  `r,s : ℕ` with `0 < r` and `0 < s`. These are exactly the positive integers
  in the node. Its first conjunct applies weak homotopy equivalence to
  `nerveMap (insertFunctor ... forward ...)`; its second conjunct uses
  `weakForward`, so every forward arrow in that condition lies in `W`.
- `ThreeArrow W x y` abbreviates the already defined category for
  `[backward, forward, backward]`. Expanding `Diagram` gives exactly
  `x ← u → v ← y`, with outer arrows in `W` and the preceding morphisms.

Dependency declarations read and used:

- `def-nagata-category`: `CategoryTheory.Category`,
  `Mathlib.CategoryTheory.Category.Basic`, whose full signature, inherited
  `CategoryStruct` data, and identity/associativity fields were read.
- `def-weil-pbc-simplicial-set`: `SSet`,
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`. The other clauses in its recorded
  match (`SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, `SSet.Finite`)
  were also read; these extra notions are not needed here.
- Added the already landed node `def-cbc-enhanced-diagrams-cones` to `stmt_deps`,
  as authorized for a needed existing definition. Its module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` supplies the exact realization-based
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, `componentsMap`, and `homotopyGroupMap`.
  This avoids defining the weak-equivalence notion twice. No dependency module or
  other DAG node is stated or changed.
- Standard Mathlib tools used directly are
  `MorphismProperty.IsMultiplicative`, `id_mem`, `comp_mem`, and
  `ContainsIdentities.eqToHom` from
  `Mathlib.CategoryTheory.MorphismProperty.Composition`, plus
  `CategoryTheory.nerve` and `nerveMap` from
  `Mathlib.AlgebraicTopology.SimplicialSet.Nerve` (available through the landed
  dependency). The full nerve and nerveMap definitions were read.

Edge cases checked before completing the construction: the empty category makes
endpoint quantification vacuous; an empty word requires the two endpoints to agree;
a single-arrow word has no unintended intermediate object; repeated equal objects
are allowed; all identities lie in `W`; `W` can be just the identities or all maps;
zero-length blocks contribute no arrow by `List.replicate 0`, although the calculus
itself quantifies only over positive lengths; the three-arrow case has exactly two
free intermediate vertices. Category and functor universes remain independent, and
the nerves enlarge to `max u v`. The component clause excludes empty-to-nonempty
realizations from being weak equivalences.

Searches actually run with `msearch.py NN def-coef-zigzag-homotopy-calculus`:

- LeanSearch: `Relative categories of zigzags with weak equivalences and two sided
  homotopy calculus of fractions via identity insertion functors`. Eight hits,
  including ordinary fraction localization and `CategoryWithWeakEquivalences`;
  none defines fixed-word relative zigzag categories or homotopy calculus.
- LeanFinder: `Definition of two sided homotopy calculus of fractions using nerves
  of zigzag categories`. Eight hits concerning the nerve adjunction and truncated
  homotopy categories; no exact match.
- Loogle: `"nerve", "weak"`. Zero hits.
- Mathlib grep: `homotopy.*calculus|calculus.*homotopy|WeakHomotopy|weakHomotopy|geometricRealization`.
  Seven hits, bibliographic mentions or ordinary derived-category fractions;
  no exact match.
- Direct `rg` of upstream `WeilConjectures` and this project's `lean/Sheaf` for
  `homotopy.*[Ff]raction|[Ff]raction.*homotopy|hammock|zigzag.*[Nn]erve|def-coef-zigzag-homotopy-calculus`
  found only unrelated derived-category fraction comments. Searching the new
  declaration names and `dag/lean_names_upstream.json` found no collision.
- A DAG search for the realization weak-equivalence definition found
  `def-cbc-enhanced-diagrams-cones`; the recorded module was read and reused.
  Its notion agrees exactly with this node's weak-equivalence clause.

No statement dispute, correction, new node, dependency repair, or proof prerequisite
is part of this delivery. Validation uses only the prescribed `scompile.py` and
`deliver2.py --no-push` wrappers.

Validation on resuming the earlier attempt: `scompile.py` compiled the module separately
as a sandbox file and under its final library module name, each in 7.4 seconds, with
no errors or warnings. The shared signature reader returned exactly the signature
recorded in `lean.statement`. There are no `sorry`s, theorem declarations, diagnostic
commands, overlong lines, or undeclared universe variables in the module.

The source was checked again in the [archived Dwyer--Kan PDF](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf),
printed pp. 24--25 (PDF pp. 8--9): Section 5.1 gives the fixed-word commuting
diagrams, Section 5.9 permits the restricted columns, and Definition 6.1(i) gives
both insertion maps for strictly positive block lengths. No mathematical mismatch
was found in the earlier construction.

Repeated searches on this resumed attempt (full machine results in `searches.jsonl`):

- LeanFinder: `A category of fixed word relative zigzags with weak vertical arrows
  admits two sided homotopy calculus of fractions when identity insertion is a weak
  equivalence on nerves`. Eight hits on model-category homotopy relations and
  truncated homotopy categories; no fixed-word zigzag-calculus definition.
- Loogle: `"nerve", "fractions"`. Zero hits.
- Mathlib grep: `homotopy.*calculus|calculus.*homotopy|hammock|RelativeZigzag|HasTwoSidedHomotopyCalculus`.
  Seven hits, all bibliography entries or ordinary derived-category fractions.
- Direct upstream, side-library, and upstream-name-inventory `rg` for the earlier
  zigzag/fraction patterns together with `RelativeZigzag` and
  `HasTwoSidedHomotopyCalculus` found only unrelated fraction comments, and no name
  collision. The prescribed upstream `grep -rn` for the node id returned no match.

Live-base refresh: the first dry run reached delivery validation after the lock wait and
reported that the live item's statement dependencies had gained `def-weil-size-convention`.
That dependency is retained in the node copy. Its statement and full convention record
were read: it has `existing: true`, `convention: true`, and deliberately no Lean
declaration or module. Its instructions require a citer to express size hypotheses
directly, which this module does through independent `u,v` and nerves in `max u v`.
No module import is attached to that metatheoretic convention. No statement text changed.

The delivery dry run printed `OK (dry run)`: the module compiles and server preflight
passes except for the independent second-reading section, which the next worker writes.
Nothing was pushed. A final dry run validates the completed report and module docstring.

## Second reading by NN

I reread the node statement against Dwyer--Kan, *Calculating simplicial localizations*,
Section 5.1 (fixed-word hammock graphs and their nerves), Section 5.2 (three-arrow example),
Section 5.9
(restricted columns), and Definition 6.1(i), printed pp. 24--25 (PDF pp. 8--9).
The source's composition convention is right-to-left; the node explicitly chooses the
left-to-right convention, which the module documents and implements.

Clause-by-clause rendering and verdict:

* The category and wide subcategory are rendered by `C : Type u`,
  `[Category.{v} C]`, `W : MorphismProperty C`, and `[W.IsMultiplicative]`.
  `IsMultiplicative` supplies identities and composition, with no two-out-of-three,
  Noetherian, finiteness, or closure hypothesis. Verdict: exact.
* The three letters are `Letter.forward`, `Letter.weakForward`, and
  `Letter.backward`; `Horizontal` makes the first unrestricted, and the latter two
  subtypes carrying `W` proofs, with the backward arrow oriented right-to-left.
  Verdict: exact.
* `Diagram` recursively supplies one horizontal arrow per letter and endpoint
  equalities; `Vertex`, `first`, `last`, `objectAt`, `Endpoints`, and `endpoints`
  expose the prescribed vertices and endpoints. The empty word is inhabited exactly
  when its endpoints agree. Verdict: exact.
* `Vertical`, `Square`, and `Commutes` render commuting vertical diagrams. `Hom.app`
  is W-valued by `Hom.mem`; `Hom.left` and `Hom.right` impose endpoint identities
  through the canonical endpoint equalities. `diagramCategory` gives pointwise
  identity and vertical composition. Verdict: exact.
* `zigzagNerve` is Mathlib's ordinary `CategoryTheory.nerve`; its simplices and
  operators are composable strings with the usual restriction, composition, deletion,
  and identity insertion. Verdict: exact.
* The imported `SSet.Enhanced.IsWeakHomotopyEquivalence` is the recorded realization
  definition: bijection on path components and bijections on every positive based
  homotopy group. Verdict: exact, with no empty-source case lost.
* `insertDiagram`, `insertVertical`, and `insertFunctor` repeat the cut vertex and
  insert the backward identity, transporting endpoint equalities by `eqToHom`.
  `fractionPrefix` and `fractionSuffix` make `- l^r - l^s -`; `HasTwoSidedHomotopyCalculus`
  quantifies over every `x,y` and positive `r,s` and gives both insertion weak
  equivalences, for `forward` and `weakForward`. Verdict: exact.
* `ThreeArrow` unfolds to `Diagram W [.backward, .forward, .backward]`, namely
  `x ← u → v ← y`, with the two outer arrows in W and the middle arrow unrestricted;
  its morphisms are the previously specified commuting W-valued endpoint-fixed maps.
  Verdict: exact.

Edge cases checked independently: empty `C` makes the endpoint quantifier vacuous;
the empty word has a diagram exactly for equal endpoints; one-letter words have no
spurious intermediate vertex; repeated objects are allowed; `W` may be identities or
all maps; `List.replicate 0` contributes no arrow; the calculus quantifies only positive
block lengths as the source does; `ThreeArrow` has exactly two intermediate vertices;
and `u` and `v` remain independent, with nerves in `max u v`.

I searched Mathlib, the upstream `WeilConjectures` tree, this project's `lean/Sheaf`,
and `dag/lean_names_upstream.json` for fixed-word relative zigzags, hammock nerves,
and two-sided homotopy calculi. I also ran fresh LeanFinder and Loogle searches and
read Mathlib's ordinary calculus-of-fractions/localization declarations. All matches
concern ordinary localization or unrelated homotopy relations; no exact notion exists.
The dependency declarations `CategoryTheory.Category`, `SSet`, and the landed
`SSet.Enhanced.IsWeakHomotopyEquivalence` were opened and match the node's uses;
`def-weil-size-convention` is metatheoretic and correctly has no import.

No mismatch was found, so no Lean or node statement was changed. The module has no
hollow definition or postponed theorem, and all declarations carry source and blueprint
docstrings. Fresh searches were LeanFinder (eight ordinary nerve hits), Loogle
`"nerve", "zigzag"` (zero hits), and grep
`fixed.?word|homotopy.*calculus|calculus.*homotopy|hammock` (seven bibliography or
ordinary-fractions hits); their machine records are in `searches.jsonl`.

Validation: `scompile.py` compiled this single module in sandbox and final-library
form in 6.3 and 8.6 seconds, with no errors or warnings. `deliver2.py --no-push`
then printed `OK (dry run)` and confirmed that the completed second-reading report,
node binding and module pass current server preflight and compilation. The node's
`lean.statement` remains the signature read from the file; every variable and universe
is explicitly bound. Only this report was changed by the second reader.
